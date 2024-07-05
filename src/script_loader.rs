use std::str::FromStr;

use bitcoin::{script::Builder, Opcode, ScriptBuf};

pub struct AsmScriptLoader;

impl AsmScriptLoader {
    /// Converts the raw string into a script buffer.
    pub fn from_raw_str(raw: &str) -> ScriptBuf {
        let mut builder = Builder::new();
        let rows: Vec<String> = raw.split_whitespace().map(|s| s.to_string()).collect();

        for row in rows.iter() {
            builder = Self::append_row(builder, row);
        }

        builder.into_script()
    }

    /// Iterprets the row and appends the corresponding opcode or integer to the builder.
    fn append_row(builder: Builder, row: &String) -> Builder {
        if Self::is_push_instruction(row) {
            let parsed_integer = Self::parse_integer(row);
            return builder.push_int(parsed_integer);
        }

        let opcode = Opcode::from_str(row).expect("unknown opcode encountered");
        builder.push_opcode(opcode)
    }

    /// Checks if the row is an integer push instruction.
    fn is_push_instruction(row: &str) -> bool {
        row.contains('<')
    }

    /// Parses the integer from the row.
    fn parse_integer(row: &str) -> i64 {
        row.replace(['<', '>'], "")
            .parse()
            .expect("unable to parse integer")
    }
}
