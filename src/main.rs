use clap::Parser;

use std::path::PathBuf;
use std::ffi::OsStr;
use std::fs;

#[derive(Parser)]
struct Args {
    path: PathBuf,
    // todo: support multiple files, idk how that will interact with passing args with --execute-asm/x86
    args: Vec<String>,
    #[arg(long)]
    print_ll: bool,
    #[arg(long)]
    interp_ll: bool,
}

fn ll_main() {
    let args = Args::parse();
    if args.path.extension() != Some(&OsStr::new("ll")) {
        eprintln!("Only supporting ll files");
        return;
    }

    let s = fs::read_to_string(&args.path).unwrap();
    let prog = match oat::llvm::parse(&s) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("{e}");
            return;
        }
    };

    if args.print_ll {
        oat::llvm::print(&prog);
    }

    if args.interp_ll {
        let prog_args: Vec<_> = args.args.iter().map(|s| &**s).collect();
        let r = oat::llvm::interp(&prog, &prog_args).unwrap();
        eprintln!("Program returned {r}");
    }
}

fn main() {
    let args = Args::parse();
    if args.path.extension() != Some(&OsStr::new("oat")) {
        eprintln!("Only supporting oat files");
        return;
    }

    let s = fs::read_to_string(&args.path).unwrap();
    let prog = match oat::oat::parse(&s) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("{e}");
            return;
        }
    };

    println!("{prog:?}");
}
