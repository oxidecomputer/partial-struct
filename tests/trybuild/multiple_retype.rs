use partial_struct::partial;

#[partial(NewStruct1)]
pub struct OldStruct {
    #[partial(NewStruct1(retype = bool, retype = u32))]
    x: u8,
}

fn main() {}