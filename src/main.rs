use clap::Parser;
use internment::Arena;

use std::path::{Path, PathBuf};
use std::fs::{self, File};
use std::io::BufWriter;
use std::process::{self, Command};
use std::time::{Instant, Duration};

use oat::{backend, frontend, llvm};

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
    #[arg(long)]
    arch: Option<String>,
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

fn precompile_runtime(args: &Args, source_path: &Path, precompiled_path: &Path) {
    if args.recompile_runtime || !precompiled_path.exists() {
        Command::new("clang")
            .arg(source_path)
            .arg("-c")
            .arg("-mstackrealign")
            .args(["-o", &precompiled_path.to_string_lossy()])
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

    if let Err(e) = backend::set_target(None, args.arch.as_deref()) {
            eprintln!("Error setting platform: '{e}'");
            std::process::exit(1);
    }

    let mut timings: Timings = Default::default();

    let ll_arena = Arena::new();

    let ll_prog = if ext == "oat" {
        let oat_arena = Arena::new();

        let start = Instant::now();
        let s = fs::read_to_string(&args.path).unwrap();
        let prog = match frontend::parse(&s, &oat_arena) {
            Ok(p) => p,
            Err(e) => {
                eprintln!("{e:?}");
                process::exit(1);
            }
        };
        timings.parsing = Some(start.elapsed());

        if args.print_oat {
            frontend::print(&prog);
        }

        let start = Instant::now();
        let tctx = match frontend::typecheck(&prog, &oat_arena) {
            Ok(tctx) => tctx,
            Err(frontend::TypeError(msg)) => {
                eprintln!("Type Error: {msg}");
                process::exit(1);
            }
        };
        timings.typechecking = Some(start.elapsed());

        if args.check {
            return;
        }

        let start = Instant::now();
        let ll = frontend::to_llvm(prog, tctx, &ll_arena, &oat_arena);
        timings.to_llvm = Some(start.elapsed());
        ll
    } else if ext == "ll" {
        let start = Instant::now();
        let s = fs::read_to_string(&args.path).unwrap();
        let ll = match llvm::parse(&s, &ll_arena) {
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

    if args.print_preopt_ll {
        llvm::print(&ll_prog);
    }
    
    let start = Instant::now();
    let ll_prog = llvm::dataflow::constprop::propagate(ll_prog);
    let ll_prog = llvm::dataflow::dce::run(ll_prog);
    // todo: remove and do dce until fixed point internally
    let ll_prog = llvm::dataflow::constprop::propagate(ll_prog);
    let ll_prog = llvm::dataflow::dce::run(ll_prog);
    timings.optimizations = Some(start.elapsed());

    if args.print_ll {
        llvm::print(&ll_prog);
    }

    if args.interpret_ll {
        let start = Instant::now();
        let prog_args: Vec<_> = args.program_args.iter().map(|s| &**s).collect();
        let r = llvm::interp(&ll_prog, &prog_args, "main").unwrap();
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
        llvm::write(ll_file, &ll_prog).unwrap();
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
        use backend::{Arch, x64};

        let base_name = args.path.file_stem().unwrap();
        let path = PathBuf::from("output").join(base_name).with_extension("S");

        match backend::get_target().arch {
            Arch::X64 => {
                let asm_prog = x64::x64_from_llvm(ll_prog);

                if args.print_asm {
                    x64::print(&asm_prog);
                }

                let file = BufWriter::new(File::create(&path).unwrap());
                x64::write(file, &asm_prog).unwrap();
            }
            Arch::Aarch64 => {
                eprintln!("Support for aarch64 isn't implemented yet");
                std::process::exit(1);
            }
        }

        path
    };
    timings.to_assembly = Some(start.elapsed());

    let start = Instant::now();
    let mut cmd = Command::new("clang");
    cmd.arg(&clang_input_file_path);
    let (runtime_path, precompiled_runtime_path) = {
        use backend::{Os, Arch};

        let language = match ext {
            "oat" => "oat",
            "ll" => "ll",
            _ => panic!("unsupported file extension"),
        };
        let target = backend::get_target();
        let os = match target.os {
            Os::MacOs => "mac",
            Os::Linux => "linux",
        };
        let arch = match target.arch {
            Arch::X64=> "x86_64",
            Arch::Aarch64 => "aarch64",
        };
        (
            PathBuf::from(format!("runtime/{language}_runtime.c")),
            PathBuf::from(format!("runtime/{language}_runtime-{os}-{arch}.o")),
        )
    };
    precompile_runtime(&args, &runtime_path, &precompiled_runtime_path);
    cmd.arg(precompiled_runtime_path);

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
