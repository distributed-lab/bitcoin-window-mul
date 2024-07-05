//! Package for performance testing of the `BigInt` library.

use bitcoin_script::script;
use prettytable::{row, Table};

use crate::{
    bigint::{U254Windowed, U255Cmpeq, U254, U508, U510},
    traits::{arithmeticable::Arithmeticable, integer::NonNativeLimbInteger},
    treepp::*,
};

#[test]
#[ignore = "performance debugging"]
fn debug_mul_performance_comparison() {
    let naive_script_narrow = U254::OP_MUL();
    let windowed_script_narrow = U254Windowed::OP_MUL();

    let naive_script_wide = U254::OP_WIDENINGMUL::<U508>();
    let windowed_script_wide = U254Windowed::OP_WIDENINGMUL::<U508>();
    let cmpeq_script_wide = U255Cmpeq::OP_WIDENINGMUL::<U510>();

    // Create the table
    let mut table = Table::new();

    // Add the headers
    table.add_row(row!["Variant", "Naive (BitVM)", "Cmpeq", "Windowed (Ours)"]);

    // Add the data
    table.add_row(row![
        "Narrow",
        naive_script_narrow.len(),
        "-",
        windowed_script_narrow.len()
    ]);
    table.add_row(row![
        "Wide",
        naive_script_wide.len(),
        cmpeq_script_wide.len(),
        windowed_script_wide.len()
    ]);

    // Print the table
    table.printstd();
}

#[test]
#[ignore = "performance debugging"]
fn debug_test_push_int_length() {
    let integers_to_test = [
        0u32, 1, 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000,
    ];

    for integer in integers_to_test {
        let script = script! {
            { integer }
        };

        println!(
            "Pushing an integer {} costs {} OPCODEs",
            integer,
            script.len()
        );
    }
}
