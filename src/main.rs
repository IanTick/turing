use std::{env::args, fs::read_to_string, process::exit, str::FromStr, time::Instant};

use turing::{Tape, Program, TuringMachine};

fn main() {
    let mut args = args();
    // Skip the executable
    args.next();

    let program_path = args.next().unwrap_or_else(|| {
        eprintln!("Expected a program path.");
        exit(1);
    });
    let tape = args.next().unwrap_or_else(|| {
        eprintln!("Expected a tape buffer.");
        exit(1);
    });

    let tape = Tape::from_str(&tape).unwrap_or_else(|_| {
        eprintln!("Tape buffer is invalid.");
        exit(1);
    });

    let code = read_to_string(program_path).unwrap_or_else(|e| {
        eprintln!("Could not read program: {e}.");
        exit(1);
    });

    let program = Program::from_str(&code).unwrap_or_else(|e| {
        eprintln!("Failed to parse program: {e:?}");
        exit(1);
    });

    let mut machine = TuringMachine::from_tape(tape);

    let start = Instant::now();
    let result = machine.run(program);
    let taken = start.elapsed();

    let tape = machine.tape();

    match result {
        Ok(s) => println!(
            "Program finished successfully in {taken:?}. Final tape: {tape}. Final state: {s:?}"
        ),
        Err(e) => println!("Program failed to run in {taken:?}. Final tape: {tape}. Error: {e:?}"),
    }
}
