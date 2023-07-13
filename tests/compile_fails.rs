// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

// Copyright 2023 Oxide Computer Company

use trybuild::TestCases;

#[test]
fn failures() {
    let t = TestCases::new();
    t.compile_fail("tests/trybuild/*.rs");
}
