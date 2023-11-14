use clap::Parser;

use std::path::PathBuf;
use std::fs;

#[derive(Parser)]
struct Args {
    path: PathBuf,
    #[arg(long)]
    pretty: bool,
}

fn main() {
    let args = Args::parse();
    let s = fs::read_to_string(&args.path).unwrap();
    let prog = match oat::llvm::parse(&s) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("{e}");
            return;
        }
    };

    if args.pretty {
        println!("{prog:#?}");
    } else {
        println!("{prog:?}");
    }
    let r = oat::llvm::interp(&prog, &[]).unwrap();
    println!("Program returned {r}");
}
