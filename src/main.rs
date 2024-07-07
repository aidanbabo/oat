use clap::Parser;
use internment::Arena;

use std::collections::HashMap;
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

    let mut ll_prog = if ext == "oat" {
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

    // todo: good code lol
    // todo: multiple rounds of dce
    for (_name, fdecl) in &mut ll_prog.fdecls {
        use oat::llvm::dataflow;
        let liveness = dataflow::solve(dataflow::Graph::<'_, '_, dataflow::liveness::Fact>::from_fdecl(fdecl)).facts;
        let mut f = liveness.iter().collect::<Vec<_>>();
        f.sort_by_key(|x| x.0);
        println!("liveness");
        for (n, f) in f {
            println!("{n:?}: {:?}", f.0);
        }

        let graph1 = dataflow::Graph::<'_, '_, dataflow::alias::Fact>::from_fdecl(fdecl);
        let alias = dataflow::solve(graph1).facts;
        let mut f = alias.iter().collect::<Vec<_>>();
        f.sort_by_key(|x| x.0);
        println!("alias");
        for (n, f) in f {
            println!("{n:?}: {:?}", f.0);
        }

        fn dce_block(b: &mut oat::llvm::ast::Block<'_>, bbix: usize, liveness: &HashMap<dataflow::Node, dataflow::liveness::Fact>, alias: &HashMap<dataflow::Node, dataflow::alias::Fact>) {
            let len = b.insns.len();
            let mut ix = len;
            // lmao lets reverse it because it works better that way! this is so silly!
            b.insns.reverse();
            b.insns.retain(|(uid, insn)| {
                // todo: fix this garbage at a better abstraction level
                // no forwards/backwards
                // no manual node-ding: make an iterator or smth
                let forwards_node_ix = dataflow::Node::Insn { bbix, ix: ix - 1};
                let backwards_node_ix = if ix == len {
                    dataflow::Node::Term { bbix }
                } else {
                    dataflow::Node::Insn { bbix, ix }
                };
                let keep = match insn {
                    oat::llvm::ast::Insn::Call(_, _, _) | oat::llvm::ast::Insn::Store(_, _, oat::llvm::ast::Operand::Gid(_)) => true,
                    oat::llvm::ast::Insn::Store(_, _, oat::llvm::ast::Operand::Id(id)) => {
                        let lives = liveness[&backwards_node_ix].0.contains(id);
                        let unique = alias[&forwards_node_ix].0.get(id).copied().unwrap_or(dataflow::alias::Alias::Undef) != dataflow::alias::Alias::May;
                        lives || !unique
                    }
                    _ => {
                        liveness[&backwards_node_ix].0.contains(uid)
                    }
                };
                ix -= 1;
                keep
            });
            b.insns.reverse();
        }

        // todo: this pattern happens too often, make an iterator or smth
        dce_block(&mut fdecl.cfg.entry, 0, &liveness, &alias);
        for (ix, (_lbl, b)) in fdecl.cfg.blocks.iter_mut().enumerate() {
            dce_block(b, ix + 1, &liveness, &alias);
        }
    }

    if args.print_ll {
        oat::llvm::print(&ll_prog);
    }

    /*
    println!("liveness for fdecl {name}");
    let mut facts = g.facts.iter().collect::<Vec<_>>();
    facts.sort_by_key(|f| f.0);
    for (n, f) in facts {
        println!("{n:?}: {f:?}");
    }
    */

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

