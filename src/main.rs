use clap::Parser;
use internment::Arena;

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
    print_asm: bool,
    #[arg(long)]
    interpret_ll: bool,
    #[arg(long)]
    clang: bool,
    #[arg(long)]
    check: bool,
    // todo: add cross compilation support?
}

fn main() {
    let args = Args::parse();
    let Some(ext) = args.path.extension().and_then(|s| s.to_str()) else {
        eprintln!("need a file extension");
        process::exit(1);
    };

    let ll_arena = Arena::new();

    let ll_prog = if ext == "oat" {
        let oat_arena = Arena::new();

        let s = fs::read_to_string(&args.path).unwrap();
        let prog = match oat::oat::parse(&s, &oat_arena) {
            Ok(p) => p,
            Err(e) => {
                eprintln!("{e:?}");
                process::exit(1);
            }
        };

        if args.print_oat {
            oat::oat::print(&prog);
        }

        let tctx = match oat::oat::typecheck(&prog, &oat_arena) {
            Ok(tctx) => tctx,
            Err(oat::oat::TypeError(msg)) => {
                eprintln!("Type Error: {msg}");
                process::exit(1);
            }
        };

        if args.check {
            return;
        }

        oat::oat::to_llvm(prog, tctx, &ll_arena, &oat_arena)
    } else if ext == "ll" {
        let s = fs::read_to_string(&args.path).unwrap();
        match oat::llvm::parse(&s, &ll_arena) {
            Ok(p) => p,
            Err(e) => {
                eprintln!("{e}");
                process::exit(1);
            }
        }
    } else {
        eprintln!("Only supporting oat or ll files");
        process::exit(1);
    };

    // todo: optimizations
    
    let ll_prog = oat::llvm::dataflow::constprop::propagate(ll_prog);
    let ll_prog = oat::llvm::dataflow::dce::run(ll_prog);
    // todo: remove and do dce until fixed point internally
    let ll_prog = oat::llvm::dataflow::constprop::propagate(ll_prog);
    let ll_prog = oat::llvm::dataflow::dce::run(ll_prog);

    if args.print_ll {
        oat::llvm::print(&ll_prog);
    }

    if args.interpret_ll {
        let prog_args: Vec<_> = args.args.iter().map(|s| &**s).collect();
        let entry = ll_arena.intern("main");
        let r = oat::llvm::interp(&ll_prog, &prog_args, entry).unwrap();
        println!("Interpreter Result: {r}");
        return;
    }

    let _ = fs::create_dir("output");

    let clang_input_file_path = if args.clang {
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
        path
    } else {
        let arena = Arena::new();
        let asm_prog = oat::backend::x64::x64_from_llvm(ll_prog, &arena);

        if args.print_asm {
            oat::backend::x64::print(&asm_prog);
        }

        let base_name = args.path.file_stem().unwrap();
        let mut path = PathBuf::from("output").join(base_name);
        path.set_extension("S");
        let file = fs::OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(&path)
            .unwrap();
        oat::backend::x64::write(file, &asm_prog).unwrap();
        path
    };

    let mut cmd = process::Command::new("clang");
    cmd.arg(&clang_input_file_path);
    if ext == "oat" {
        cmd.arg("runtime.c");
    } else if ext == "ll" {
        // todo: runtime support for ll files (tests)
    }
    let run = cmd
        // todo: add triple
        .arg("-Wno-override-module")
        .arg("-mstackrealign") // automatically realigns stack for "backward compatibility" 
                               // i.e. allows us to be lazier
        .spawn()
        .unwrap()
        .wait()
        .unwrap();
    if !run.success() {
        std::process::exit(1);
    }
}

