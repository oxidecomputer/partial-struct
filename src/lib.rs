// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

// Copyright 2023 Oxide Computer Company

extern crate proc_macro;
#[macro_use]
extern crate quote;

use proc_macro::TokenStream;
use proc_macro2::Group;
use quote::ToTokens;
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input,
    spanned::Spanned,
    DeriveInput, Error, Ident, Result, Token, Type, GenericParam, punctuated::Punctuated, WherePredicate, PredicateType, Attribute,
};

/// Optional commands that can be define on a per field level. Commands are paired with the
/// specific struct name that it applies to.
///
/// Commands:
///   skip - Omits the field from the newly generated struct
#[derive(Debug)]
struct FieldCommands {
    name: Ident,
    skip: bool,
    retype: Option<Type>,
}

/// Currently field command syntax is a comma separated list of values. This will likely be
/// replaced with a more flexible syntax in the future
impl Parse for FieldCommands {
    fn parse(input: ParseStream) -> Result<Self> {
        let name = input.parse()?;

        let content;
        syn::parenthesized!(content in input);

        let mut skip = false;
        let mut retype = None;

        while !content.is_empty() {
            let command: Ident = content.parse()?;

            if command == "skip" {
                skip = true;
            } else if command == "retype" {
                // If a retype command has already been found, return an error on the second one
                if retype.is_some() {
                    return Err(Error::new(
                        command.span(),
                        "Only a single retype command is allowed per field",
                    ));
                }

                let _: Token![=] = content.parse()?;
                let new_type: Type = content.parse()?;
                retype = Some(new_type);
            } else {
                return Err(Error::new(
                    command.span(),
                    format!("Unknown command: {}", command),
                ));
            }

            // Parse an optional comma following each trait
            let _: Result<Token![,]> = content.parse();
        }

        Ok(FieldCommands { name, skip, retype })
    }
}

/// A holder of derive identifiers to add or remove from generated structs
#[derive(Debug, Clone)]
struct DeriveOptions {
    traits: Vec<Ident>,
}

impl Parse for DeriveOptions {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut traits = vec![];

        while !input.is_empty() {
            let t: Ident = input.parse()?;

            // We do not try to validate the derive, if an invalid derive is supplied then it
            // will fail during compilation later on
            traits.push(t);

            // Parse an optional comma following each trait
            let _: Result<Token![,]> = input.parse();
        }

        Ok(DeriveOptions { traits })
    }
}

/// A parsed out struct that has been requested to be created
#[derive(Debug)]
struct NewItem {
    name: Ident,

    // Additional derives that should be added to the struct
    with: Option<DeriveOptions>,

    // Derives that should be removed from the new struct (if they exist)
    without: Option<DeriveOptions>,

    // Arbitrary attributes that should be applied to only this variant
    attributes: Option<proc_macro2::TokenStream>,
}

impl Parse for NewItem {
    fn parse(input: ParseStream) -> Result<Self> {
        let name: Ident = input.parse()?;

        let mut new_item = NewItem {
            name,
            with: None,
            without: None,
            attributes: None,
        };

        while !input.is_empty() {
            // If there are remaining tokens then the next token must be a comma
            let _: Token![,] = input.parse()?;

            // Following there are two possible options `with` and `without`
            let option: Ident = input.parse()?;

            if option == "with" {
                let to_add: Group = input.parse()?;
                let tokens = to_add.stream();
                let traits: DeriveOptions = syn::parse2(tokens)?;
                new_item.with = Some(traits);
            } else if option == "without" {
                let to_add: Group = input.parse()?;
                let tokens = to_add.stream();
                let traits: DeriveOptions = syn::parse2(tokens)?;
                new_item.without = Some(traits);
            } else if option == "attributes" {
                let to_add: Group = input.parse()?;
                let tokens = to_add.stream();
                new_item.attributes = Some(tokens);
            } else {
                return Err(syn::Error::new(option.span(), "unknown option"));
            }
        }

        Ok(new_item)
    }
}

#[derive(Debug)]
struct Derives {
    derives: Vec<Ident>,
}

impl Parse for Derives {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;
        syn::parenthesized!(content in input);

        let mut derives: Vec<Ident> = vec![];

        while !content.is_empty() {
            let derive: Ident = content.parse()?;
            let _: Result<Token![,]> = content.parse();

            derives.push(derive);
        }

        Ok(Derives { derives })
    }
}

fn compute_derives(
    mut attr: syn::Attribute,
    with: Option<DeriveOptions>,
    without: Option<DeriveOptions>,
) -> syn::Attribute {
    let derives: Result<Derives> = syn::parse2(attr.tokens);
    let mut derive_list = derives.map(|d| d.derives).unwrap_or_else(|_| vec![]);

    if let Some(mut with) = with {
        derive_list.append(&mut with.traits);
    }

    if let Some(without) = without {
        derive_list.retain(|item| !without.traits.contains(item));
    }

    let stream = quote! {
        (#( #derive_list ),*)
    };

    attr.tokens = stream;

    attr
}

/// A macro (for structs) that generates a new struct containing a subset of the fields of the
/// tagged struct. New structs can have additional derive values added or removed. Any subsequent
/// (non-partial) derives or macros will be applied to the new structs as well.
///
/// Examples:
///
/// ```
/// use partial_struct::partial;
///
/// // Using all of the macro features
///
/// #[partial(NewStruct, with(Debug), without(Default))]
/// #[derive(Default)]
/// struct OldStruct {
///     a: u32,
///     #[partial(NewStruct(skip))]
///     b: u32,
/// }
///
/// // will generate
///
/// // #[derive(Debug)]
/// // struct NewStruct {
/// //    a: u32
/// // }
/// ```
#[proc_macro_attribute]
pub fn partial(attr: TokenStream, input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let input_span = input.span();

    // We will need this name later when generating [From] impls
    let original_name = input.ident;

    // Parse the attribute that triggered this macro to execute
    let first_new_item = parse_macro_input!(attr as NewItem);

    // Look through the remaining attributes on this struct and find any other instances of the
    // [partial] macro. For each of those, parse them into their own [NewItem]
    let additional_items: Result<Vec<NewItem>> = input
        .attrs
        .iter()
        .filter_map(|attr| {
            if attr.path.is_ident("partial") {
                Some(attr.parse_args())
            } else {
                None
            }
        })
        .collect();

    match additional_items {
        Ok(mut additional_items) => {
            // Construct the full list of structs that need to be created. This list needs to
            // include the original struct (without modification) as well
            let mut new_items: Vec<NewItem> = vec![
                NewItem {
                    name: original_name.clone(),
                    with: None,
                    without: None,
                    attributes: None,
                },
                first_new_item,
            ];
            new_items.append(&mut additional_items);

            let result = match input.data {
                // This macro is only defined for structs. Usage on any other data type will
                // fail with a panic
                syn::Data::Struct(ref s) => {
                    let visibility = input.vis;
                    let generics = input.generics;

                    // Create the list of all attribute macros that need to be applied to the
                    // generated structs
                    let attr_without_partials = input
                        .attrs
                        .iter()
                        .filter(|attr| !attr.path.is_ident("partial"));

                    // From the list of attributes, find all of the non-derive attributes
                    let struct_attrs: Vec<&syn::Attribute> = attr_without_partials
                        .into_iter()
                        .filter(|attr| !attr.path.is_ident("derive"))
                        .collect();

                    // Find the derive attribute if one exists
                    let orig_derives: Option<&syn::Attribute> =
                        input.attrs.iter().find(|attr| attr.path.is_ident("derive"));

                    // Keep track of all of the structs to output
                    let mut expanded_structs = vec![];

                    if let syn::Fields::Named(ref fields) = s.fields {
                        // Generate each of the requested structs
                        for new_item in new_items {
                            let NewItem {
                                name,
                                with,
                                without,
                                attributes,
                            } = new_item;

                            // Generate the list of fields to assign to the new struct

                            let mut without_skipped = vec![];

                            for field in &fields.named {
                                let parsed_attrs = field
                                    .attrs
                                    .iter()
                                    .filter_map(|attr| {
                                        if attr.path.is_ident("partial") {
                                            Some(attr.parse_args::<FieldCommands>())
                                        } else {
                                            None
                                        }
                                    })
                                    .collect::<Result<Vec<_>>>();

                                match parsed_attrs {
                                    Ok(parsed_attrs) => {
                                        let should_skip = parsed_attrs
                                            .iter()
                                            .any(|parsed| parsed.name == name && parsed.skip);

                                        if !should_skip {
                                            without_skipped.push(field);
                                        }
                                    }
                                    Err(err) => return err.into_compile_error().into(),
                                }
                            }

                            let mut has_retyped_field = false;
                            let mut new_fields = vec![];

                            for field in without_skipped {
                                let mut field = field.to_owned();

                                let retype = match field
                                    .attrs
                                    .iter()
                                    .filter_map(|attr| {
                                        if attr.path.is_ident("partial") {
                                            // This ideally would be a helpful error message instead
                                            // of a panic
                                            let parsed = attr.parse_args::<FieldCommands>();

                                            match parsed {
                                                Ok(command) => {
                                                    if command.name == name
                                                        && command.retype.is_some()
                                                    {
                                                        Some(Ok(command.retype.unwrap()))
                                                    } else {
                                                        None
                                                    }
                                                }
                                                Err(err) => Some(Err(err)),
                                            }
                                        } else {
                                            None
                                        }
                                    })
                                    .collect::<Result<Vec<_>>>()
                                {
                                    Ok(mut retypes) => {
                                        if retypes.len() > 1 {
                                            return quote_spanned! {
                                                input_span => compile_error!("Only a single retype command is allowed")
                                            }.into();
                                        }

                                        retypes.pop()
                                    }
                                    Err(err) => return err.into_compile_error().into(),
                                };

                                has_retyped_field = has_retyped_field || retype.is_some();

                                if let Some(retype) = retype {
                                    field.ty = retype.clone();
                                }

                                // Filter out any `partial` attributes assigned to the field
                                field.attrs = field
                                    .attrs
                                    .into_iter()
                                    .filter(|attr| !attr.path.is_ident("partial"))
                                    .collect();

                                new_fields.push(field);
                            }

                            let filtered_fields = new_fields;

                            // If this is not the original struct being generated, create a default
                            // From impl from the original struct to the new struct.
                            let from_impl = if name != original_name && !has_retyped_field {
                                let field_names = filtered_fields
                                    .iter()
                                    .map(|field| field.ident.as_ref())
                                    .collect::<Vec<Option<&Ident>>>();

                                let mut generics_without_bounds = generics.clone();
                                let predicates = generics_without_bounds.params.iter_mut().filter_map(|p| {
                                    match p {
                                        GenericParam::Const(_) => unimplemented!("Const generic params are not supported"),
                                        GenericParam::Lifetime(_) => unimplemented!("Lifetime generic params are not supported"),
                                        GenericParam::Type(p) => {
                                            let predicate = WherePredicate::Type(PredicateType {
                                                lifetimes: None,
                                                bounded_ty: Type::Verbatim(p.ident.clone().into_token_stream()),
                                                colon_token: Token![:](input_span),
                                                bounds: p.bounds.clone(),
                                            });

                                            p.bounds = Punctuated::new();

                                            return Some(predicate)
                                        },
                                    };
                                }).collect::<Vec<_>>();

                                {
                                    let where_clause = generics_without_bounds.make_where_clause();
                                    for p in predicates {
                                        where_clause.predicates.push(p);
                                    }
                                }

                                let where_clause = &generics_without_bounds.where_clause;

                                quote! {
                                    impl #generics_without_bounds From<#original_name #generics_without_bounds> for #name #generics_without_bounds #where_clause {
                                        fn from(orig: #original_name #generics_without_bounds) -> Self {
                                            Self {
                                                #( #field_names: orig.#field_names, )*
                                            }
                                        }
                                    }
                                }
                            } else {
                                quote! {}
                            };

                            let derives: Option<syn::Attribute> =
                                orig_derives.map(|d| d.to_owned());

                            let derive_attr = if let Some(derives) = derives {
                                // Add in and/or remove the additional derives defined by the caller.
                                // Adding derives may result in further compilation errors in the
                                // fields in the original struct are not compatible with the new
                                // derives
                                let computed = compute_derives(derives, with, without);
                                quote! { #computed }
                            } else {
                                quote! {}
                            };

                            expanded_structs.push(quote! {
                                #derive_attr
                                #( #struct_attrs )*
                                #attributes
                                #visibility struct #name #generics {
                                    #( #filtered_fields, )*
                                }

                                #from_impl
                            });
                        }
                    }

                    proc_macro::TokenStream::from(quote! {
                        #( #expanded_structs )*
                    })
                }

                syn::Data::Enum(ref e) => {
                    let visibility = input.vis;
                    let generics = input.generics;

                    let attr_without_partials = get_attr_without_partials(input.attrs.iter());
                    let container_attrs = get_non_derive_attributes(attr_without_partials);
                    let orig_derives = get_derive_attribute(input.attrs.iter());

                    // Keep track of all of the enums to output
                    let mut expanded_enums = vec![];

                    // Generate each of the requested enums
                    for new_item in new_items {
                        let NewItem {
                            name,
                            with,
                            without,
                            attributes,
                        } = new_item;

                        let derives: Option<syn::Attribute> =
                            orig_derives.map(|d| d.to_owned());

                        let derive_attr = if let Some(derives) = derives {
                            // Add in and/or remove the additional derives defined by the caller.
                            // Adding derives may result in further compilation errors in the
                            // fields in the original struct are not compatible with the new
                            // derives
                            let computed = compute_derives(derives, with, without);
                            quote! { #computed }
                        } else {
                            quote! {}
                        };

                        let variants = &e.variants;

                        // If this is not the original struct being generated, create a default
                        // From impl from the original struct to the new struct.
                        let from_impl = if name != original_name {
                            let variant_names = variants
                                .iter()
                                .map(|variant| &variant.ident)
                                .collect::<Vec<_>>();

                            let variant_fields = variants
                                .iter()
                                .map(|variant| &variant.fields)
                                .collect::<Vec<_>>();

                            let mut generics_without_bounds = generics.clone();
                            let predicates = generics_without_bounds.params.iter_mut().filter_map(|p| {
                                match p {
                                    GenericParam::Const(_) => unimplemented!("Const generic params are not supported"),
                                    GenericParam::Lifetime(_) => unimplemented!("Lifetime generic params are not supported"),
                                    GenericParam::Type(p) => {
                                        let predicate = WherePredicate::Type(PredicateType {
                                            lifetimes: None,
                                            bounded_ty: Type::Verbatim(p.ident.clone().into_token_stream()),
                                            colon_token: Token![:](input_span),
                                            bounds: p.bounds.clone(),
                                        });

                                        p.bounds = Punctuated::new();

                                        return Some(predicate)
                                    },
                                };
                            }).collect::<Vec<_>>();

                            {
                                let where_clause = generics_without_bounds.make_where_clause();
                                for p in predicates {
                                    where_clause.predicates.push(p);
                                }
                            }

                            let where_clause = &generics_without_bounds.where_clause;

                            quote! {
                                impl #generics_without_bounds From<#original_name #generics_without_bounds> for #name #generics_without_bounds #where_clause {
                                    fn from(orig: #original_name #generics_without_bounds) -> Self {
                                        match orig {
                                            #( #original_name::#variant_names #variant_fields => Self::#variant_names #variant_fields, )*
                                        }
                                    }
                                }
                            }
                        } else {
                            quote! {}
                        };

                        expanded_enums.push(quote! {
                            #derive_attr
                            #( #container_attrs )*
                            #attributes
                            #visibility enum #name #generics {
                                #variants
                            }

                            #from_impl
                        });
                    }
                    
                    proc_macro::TokenStream::from(quote! {
                        #( #expanded_enums )*
                    })
                }

                // Ideally this would return a descriptive error instead of panicking
                _ => quote_spanned! {
                    input_span => compile_error!("Partial can only be defined on structs");
                }
                .into(),
            };

            result
        }
        Err(err) => err.to_compile_error().into(),
    }
}

// Create the list of all attribute macros that need to be applied to the
// generated structs
fn get_attr_without_partials<'a>(attrs: impl Iterator<Item = &'a Attribute>) -> impl Iterator<Item = &'a Attribute> {
    attrs
        .filter(|attr| !attr.path.is_ident("partial"))
}

// From the list of attributes, find all of the non-derive attributes
fn get_non_derive_attributes<'a>(attrs: impl Iterator<Item = &'a Attribute>) -> Vec<&'a Attribute> {
    attrs
        .into_iter()
        .filter(|attr| !attr.path.is_ident("derive"))
        .collect()
}

// Find the derive attribute if one exists
fn get_derive_attribute<'a>(mut attrs: impl Iterator<Item = &'a Attribute>) -> Option<&'a Attribute> {
    attrs.find(|attr| attr.path.is_ident("derive"))
}
