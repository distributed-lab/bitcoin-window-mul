//! Package for performance testing of the `BigInt` library.

#[cfg(test)]
mod test {
    use bitcoin::ScriptBuf;
    use prettytable::{row, Table};

    use crate::{
        bigint::{U254Windowed, U254},
        traits::arithmeticable::Arithmeticable,
    };

    fn print_comparison_table(script_1: (&str, ScriptBuf), script_2: (&str, ScriptBuf)) {
        // Create the table
        let mut table = Table::new();

        // Add the headers
        table.add_row(row![script_1.0, script_2.0]);

        // Add the data
        table.add_row(row![script_1.1.len(), script_2.1.len()]);

        // Print the table
        table.printstd();
    }

    #[test]
    #[ignore = "performance test, used for debugging"]
    fn mul_performance_comparison() {
        let naive_script = U254::OP_MUL();
        let windowed_script = U254Windowed::OP_MUL();

        print_comparison_table(("Naive", naive_script), ("Windowed", windowed_script));
    }
}
