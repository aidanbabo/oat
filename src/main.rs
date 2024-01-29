use clap::Parser;

use std::path::PathBuf;
use std::fs;
use std::process;

#[derive(Parser)]
struct Args {
    path: PathBuf,
    // todo: support multiple files, idk how that will interact with passing args with --execute-asm/x86
    args: Vec<String>,
    #[arg(long)]
    print_oat: bool,
    #[arg(long)]
    print_ll: bool,
    #[arg(long)]
    interpret_ll: bool,
    #[arg(long)]
    clang: bool,
}

fn main() {
    let args = Args::parse();
    let Some(ext) = args.path.extension().and_then(|s| s.to_str()) else {
        eprintln!("need a file extension");
        return;
    };

    let ll_prog = if ext == "oat" {
        let s = fs::read_to_string(&args.path).unwrap();
        let prog = match oat::oat::parse(&s) {
            Ok(p) => p,
            Err(e) => {
                eprintln!("{e:?}");
                return;
            }
        };

        if args.print_oat {
            oat::oat::print(&prog);
        }

        oat::oat::to_llvm(prog)
    } else if ext == "ll" {
        let s = fs::read_to_string(&args.path).unwrap();
        match oat::llvm::parse(&s) {
            Ok(p) => p,
            Err(e) => {
                eprintln!("{e}");
                return;
            }
        }
    } else {
        eprintln!("Only supporting oat or ll files");
        return;
    };

    if args.print_ll {
        oat::llvm::print(&ll_prog);
    }

    if args.interpret_ll {
        let prog_args: Vec<_> = args.args.iter().map(|s| &**s).collect();
        let r = oat::llvm::interp(&ll_prog, &prog_args).unwrap();
        println!("Interpreter Result: {r}");
        return;
    }

    let _ = fs::create_dir("output");

    let base_name = args.path.file_stem().unwrap();
    let mut path = PathBuf::from("output").join(base_name);
    path.set_extension("ll");
    let file = fs::OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(true)
        .open(&path)
        .unwrap();
    oat::llvm::write(file, &ll_prog).unwrap();

    if args.clang {
        let mut cmd = process::Command::new("clang");
        cmd.arg(&path);
        if ext == "oat" {
            cmd.arg("runtime.c");
        } else if ext == "ll" {
            // todo: runtime support for ll files (tests)
        }
        cmd
            .arg("-Wno-override-module")
            .spawn()
            .unwrap()
            .wait()
            .unwrap();
    }
}

