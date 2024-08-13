use clap::Parser;
use internment::Arena;

use std::path::{Path, PathBuf};
use std::fs::{self, File};
use std::io::BufWriter;
use std::process::{self, Command};
use std::time::{Instant, Duration};

#[derive(Parser)]
struct Args {
    path: PathBuf,
    // todo: support multiple files, idk how that will interact with passing args with --execute-asm/x86
    program_args: Vec<String>,
    #[arg(long)]
    print_oat: bool,
    #[arg(long)]
    print_ll: bool,
    #[arg(long)]
    print_preopt_ll: bool,
    #[arg(long)]
    print_asm: bool,
    #[arg(long)]
    interpret_ll: bool,
    #[arg(long)]
    clang: bool,
    #[arg(long)]
    check: bool,
    #[arg(long)]
    timings: bool,
    #[arg(long)]
    recompile_runtime: bool,
    // todo: add cross compilation support?
}

#[derive(Default)]
struct Timings {
    parsing: Option<Duration>,
    typechecking: Option<Duration>,
    to_llvm: Option<Duration>,
    optimizations: Option<Duration>,
    interpreting: Option<Duration>,
    to_assembly: Option<Duration>,
    linking: Option<Duration>,
}

fn print_timings(timings: &Timings) {
    let mut total = Duration::default();
    if let Some(t) = timings.parsing {
        println!("Parsing: {t:?}");
        total += t;
    }
    if let Some(t) = timings.typechecking {
        println!("Typechecking: {t:?}");
        total += t;
    }
    if let Some(t) = timings.to_llvm {
        println!("Lowering to LLVM: {:?}", t);
        total += t;
    }
    if let Some(t) = timings.interpreting {
        println!("Interpreting: {t:?}");
        total += t;
    }
    if let Some(t) = timings.optimizations {
        println!("Optimizing: {t:?}");
        total += t;
    }
    if let Some(t) = timings.to_assembly {
        println!("To Assembly: {t:?}");
        total += t;
    }
    if let Some(t) = timings.linking {
        println!("Assembling and Linking: {t:?}");
        total += t;
    }
    println!("Total: {total:?}");
}

fn precompile_runtime(args: &Args, path: &Path) {
    let precompiled_runtime = path;
    if args.recompile_runtime || !precompiled_runtime.exists() {
        Command::new("clang")
            .arg(precompiled_runtime.with_extension("c"))
            .arg("-c")
            .arg("-mstackrealign")
            .args(["-o", &precompiled_runtime.to_string_lossy()])
            .spawn()
            .unwrap()
            .wait()
            .unwrap();
    }
}

fn main() {
    let args = Args::parse();
    let Some(ext) = args.path.extension().and_then(|s| s.to_str()) else {
        eprintln!("need a file extension");
        process::exit(1);
    };

    let mut timings: Timings = Default::default();

    let ll_arena = Arena::new();

    let ll_prog = if ext == "oat" {
        let oat_arena = Arena::new();

        let start = Instant::now();
        let s = fs::read_to_string(&args.path).unwrap();
        let prog = match oat::oat::parse(&s, &oat_arena) {
            Ok(p) => p,
            Err(e) => {
                eprintln!("{e:?}");
                process::exit(1);
            }
        };
        timings.parsing = Some(start.elapsed());

        if args.print_oat {
            oat::oat::print(&prog);
        }

        let start = Instant::now();
        let tctx = match oat::oat::typecheck(&prog, &oat_arena) {
            Ok(tctx) => tctx,
            Err(oat::oat::TypeError(msg)) => {
                eprintln!("Type Error: {msg}");
                process::exit(1);
            }
        };
        timings.typechecking = Some(start.elapsed());

        if args.check {
            return;
        }

        let start = Instant::now();
        let ll = oat::oat::to_llvm(prog, tctx, &ll_arena, &oat_arena);
        timings.to_llvm = Some(start.elapsed());
        ll
    } else if ext == "ll" {
        let start = Instant::now();
        let s = fs::read_to_string(&args.path).unwrap();
        let ll = match oat::llvm::parse(&s, &ll_arena) {
            Ok(p) => p,
            Err(e) => {
                eprintln!("{e:?}");
                process::exit(1);
            }
        };
        timings.parsing = Some(start.elapsed());
        ll
    } else {
        eprintln!("Only supporting oat or ll files");
        process::exit(1);
    };

    // todo: optimizations
    if args.print_preopt_ll {
        oat::llvm::print(&ll_prog);
    }
    
    let start = Instant::now();
    let ll_prog = oat::llvm::dataflow::constprop::propagate(ll_prog);
    let ll_prog = oat::llvm::dataflow::dce::run(ll_prog);
    // todo: remove and do dce until fixed point internally
    let ll_prog = oat::llvm::dataflow::constprop::propagate(ll_prog);
    let ll_prog = oat::llvm::dataflow::dce::run(ll_prog);
    timings.optimizations = Some(start.elapsed());

    if args.print_ll {
        oat::llvm::print(&ll_prog);
    }

    if args.interpret_ll {
        let start = Instant::now();
        let prog_args: Vec<_> = args.program_args.iter().map(|s| &**s).collect();
        let entry = ll_arena.intern("main");
        let r = oat::llvm::interp(&ll_prog, &prog_args, entry).unwrap();
        timings.interpreting = Some(start.elapsed());
        println!("Interpreter Result: {r}");
        if args.timings {
            print_timings(&timings);
        }
        return;
    }

    let _ = fs::create_dir("output");

    let start = Instant::now();
    let clang_input_file_path = if args.clang {
        let base_name = args.path.file_stem().unwrap();
        let base_path = PathBuf::from("output").join(base_name); 
        let ll_path = base_path.with_extension("ll");
        let asm_path = base_path.with_extension("S");

        let ll_file = BufWriter::new(File::create(&ll_path).unwrap());
        oat::llvm::write(ll_file, &ll_prog).unwrap();
        let cmd = Command::new("clang")
            .arg(&ll_path)
            .arg("-S")
            // todo: add triple
            .arg("-Wno-override-module")
            .args(["-o", &asm_path.to_string_lossy()])
            .spawn()
            .unwrap()
            .wait()
            .unwrap();
        if !cmd.success() {
            process::exit(1);
        }

        asm_path
    } else {
        let arena = Arena::new();
        let asm_prog = oat::backend::x64::x64_from_llvm(ll_prog, &arena);

        if args.print_asm {
            oat::backend::x64::print(&asm_prog);
        }

        let base_name = args.path.file_stem().unwrap();
        let path = PathBuf::from("output").join(base_name).with_extension("S");
        let file = BufWriter::new(File::create(&path).unwrap());
        oat::backend::x64::write(file, &asm_prog).unwrap();
        path
    };
    timings.to_assembly = Some(start.elapsed());

    let start = Instant::now();
    let mut cmd = Command::new("clang");
    cmd.arg(&clang_input_file_path);
    if ext == "oat" {
        let path = Path::new("runtime/oat_runtime.o");
        precompile_runtime(&args, path);
        cmd.arg(path);
    } else if ext == "ll" {
        let path = Path::new("runtime/ll_runtime.o");
        precompile_runtime(&args, path);
        cmd.arg(path);
    }
    let run = cmd
        .arg("-mstackrealign") // automatically realigns stack for "backward compatibility" 
                               // i.e. allows us to be lazier
                               // requires us to compile the runtime with the same option
        .spawn()
        .unwrap()
        .wait()
        .unwrap();
    if !run.success() {
        process::exit(1);
    }
    timings.linking = Some(start.elapsed());

    if args.timings {
        print_timings(&timings);
    }
}
