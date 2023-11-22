// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

// Copyright 2023 Oxide Computer Company

use partial_struct::partial;
use serde::{Deserialize, Serialize};

#[test]
fn test_create_new() {
    fn default_to_true() -> bool {
        true
    }

    #[partial(NewStruct1, with(Default), without(Eq), attributes(#[serde(rename_all = "camelCase")]))]
    #[partial(NewStruct2, attributes(#[serde(rename_all = "PascalCase")]))]
    #[derive(Debug, PartialEq, Eq, Deserialize, Serialize)]
    #[doc(hidden)]
    pub(crate) struct OldStruct<T: Ord> {
        gen: T,
        #[partial(NewStruct1(skip))]
        f1: u8,
        #[partial(NewStruct2(skip))]
        #[serde(default = "default_to_true")]
        f2: bool,
    }

    assert_eq!(
        NewStruct1 { gen: "", f2: false },
        NewStruct1::<&str>::default()
    );
    assert_eq!(
        "{\"gen\":\"\",\"f2\":false}",
        serde_json::to_string(&NewStruct1::<&str>::default())
            .expect("Failed to serialize NewStruct1")
    );
    assert_eq!(
        NewStruct1 { gen: "", f2: true },
        serde_json::from_str("{\"gen\":\"\"}").expect("Failed to deserialize NewStruct1")
    );
}

#[test]
fn test_multiple_commands() {
    #[partial(NewStruct1)]
    #[derive(Debug, PartialEq, Eq, Deserialize, Serialize)]
    pub(crate) struct OldStruct {
        #[partial(NewStruct1(skip, retype = u8))]
        f1: bool,
    }

    let _ = OldStruct { f1: false };

    let _ = NewStruct1 {};
}

#[test]
fn test_retype_field() {
    #[partial(NewStruct1)]
    #[derive(Debug, PartialEq, Eq, Deserialize, Serialize)]
    pub(crate) struct OldStruct {
        #[partial(NewStruct1(retype = u8))]
        f1: bool,
    }

    let _ = OldStruct { f1: false };

    let _ = NewStruct1 { f1: 5 };
}

#[test]
fn test_empty_structs() {
    #[partial(NewStruct1)]
    pub(crate) struct OldStruct {
        #[partial(NewStruct1(skip))]
        _x: bool,
    }

    #[partial(NewStruct2)]
    pub(crate) struct OldStruct2 {}
}

#[test]
fn test_basic_enum() {
    #[partial(NewEnum1)]
    #[derive(Debug)]
    pub(crate) enum OldEnum {
        A,
        B,
    }
}

#[test]
fn test_tagged_enum() {
    #[partial(NewEnum1)]
    #[derive(Debug)]
    pub(crate) enum OldEnum {
        A,
        B(u32),
        C(u32, u64),
    }
}

#[test]
fn test_tagged_generics_enum() {
    #[partial(NewEnum1)]
    #[derive(Debug)]
    pub(crate) enum OldEnum {
        A,
        B(u32),
        C(Vec<bool>),
    }
}