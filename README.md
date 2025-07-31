# Oat Compiler

This is a compiler for the Oat programming language, which is used in compiler coursework at Penn and consequently Princeton.

Oat is a high-level, memory-safe programming language with features like structural subtyping and optionals. This compiler is a Rust port of the compiler written in class.
I wanted to see if Rust was suited for compiler development because it inherits syntax and features from ML-like langauges, having first been written in OCaml itself before it began boostrapping.

Currently, the compiler:
- parses source code via a hand written recursive descent parser into an AST
- typechecks the AST
- converts the AST to LLVM lite, a subset of LLVM with simpler semantics used in the class
- performs some simple dataflow analysis and performs optimizations
- converts the IR into a machine-specific representation
- performs register allocation
- outputs an assembly file
- assembles and links with runtime support files using `clang`

In terms of matching features with the course compiler, I need to:
- make dataflow analysis more efficient by operating on basic blocks instead of individual instructions
- add tests for dataflow analysis, guaranteeing specific transformations take place, not just E2E tests
- introduce the graph coloring register allocator

In terms of additional features, the compiler has yet to:
- support more architectures than x64
  - My M1 Mac is in the shop :(
- run on Windows
- LSP support

Implementation styles I'd like to explore
- remove string interning dependency and use ids with arenas (in progress)
- parse into flat arrays, good ol' Chandler Carruth says they do in Carbon
- explore doing register allocation in another IR, gcc does odd stuff I wanna explore
