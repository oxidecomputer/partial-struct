// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

// Copyright 2023 Oxide Computer Company

use partial_struct::partial;

#[partial(NewStruct1)]
pub struct OldStruct {
    #[partial(NewStruct1(unknown))]
    x: u8,
}

fn main() {}