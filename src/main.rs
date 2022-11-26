use std::{env::args, fs::read_to_string, process::exit, str::FromStr, time::Instant};

use turing::{Band, Program, TuringMachine};

fn main() {
    let mut args = args();
    // Skip the executable
    args.next();

    let program_path = args.next().unwrap_or_else(|| {
        eprintln!("Expected a program path.");
        exit(1);
    });
    let band = args.next().unwrap_or_else(|| {
        eprintln!("Expected a band buffer.");
        exit(1);
    });

    let band = Band::from_str(&band).unwrap_or_else(|_| {
        eprintln!("Band buffer is invalid.");
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

    let mut machine = TuringMachine::from_band(band);

    let start = Instant::now();
    let result = machine.execute(&program);
    let taken = start.elapsed();

    let band = machine.band();

    match result {
        Ok(s) => println!(
            "Program finished successfully in {taken:?}. Final band: {band}. Final state: {s:?}"
        ),
        Err(e) => println!("Program failed to run in {taken:?}. Final band: {band}. Error: {e:?}"),
    }
}
