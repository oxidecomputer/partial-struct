use partial_struct::partial;

#[partial(NewEnum)]
pub enum OldEnum {
    A,
    B,
}

fn main() {}