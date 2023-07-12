use partial_struct::partial;

#[partial(NewStruct1)]
pub struct OldStruct {
    #[partial(NewStruct1(unknown))]
    x: u8,
}

fn main() {}