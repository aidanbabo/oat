use clap::Parser;

use std::path::PathBuf;
use std::fs;

#[derive(Parser)]
struct Args {
    path: PathBuf,
}

fn main() {
    let args = Args::parse();
    let s = fs::read_to_string(&args.path).unwrap();
    let prog = oat::llvm::parse(&s);
    println!("{prog:?}");
}
