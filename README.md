# partial-struct

Create subsets of structs

A macro (for structs) that generates a new struct containing a subset of the fields of the
tagged struct. New structs can have derive values added or removed. Any subsequent (non-partial)
derives or macros will be applied to the new structs.

### Example

```rust
use partial_struct::partial;

///
// Using all of the macro features
///
#[partial(NewStruct, with(Debug), without(Default))]
#[derive(Default)]
struct OldStruct {
    a: u32,
    #[partial(NewStruct(skip))]
    b: u32,
    #[partial(NewStruct(retype = u32))]
    c: u8,
}
```

will generate

```rust
#[derive(Default)]
struct NewStruct {
   a: u32,
   b: u32,
   c: u8,
}

#[derive(Debug)]
struct NewStruct {
   a: u32,
   c: u32,
}
```