//! Package for performance testing of the `BigInt` library.

#[cfg(test)]
mod test {
    use prettytable::{row, Table};

    use crate::{
        bigint::{U254Windowed, U254, U508},
        traits::{arithmeticable::Arithmeticable, integer::NonNativeLimbInteger},
    };

    #[test]
    #[ignore = "performance debugging"]
    fn debug_mul_performance_comparison() {
        let naive_script_narrow = U254::OP_MUL();
        let windowed_script_narrow = U254Windowed::OP_MUL();

        let naive_script_wide = U254::OP_WIDENINGMUL::<U508>();
        let windowed_script_wide = U254Windowed::OP_WIDENINGMUL::<U508>();

        // Create the table
        let mut table = Table::new();

        // Add the headers
        table.add_row(row!["Variant", "Naive (BitVM)", "Windowed (Ours)"]);

        // Add the data
        table.add_row(row!["Narrow", naive_script_narrow.len(), windowed_script_narrow.len()]);
        table.add_row(row!["Wide", naive_script_wide.len(), windowed_script_wide.len()]);

        // Print the table
        table.printstd();
    }
}
