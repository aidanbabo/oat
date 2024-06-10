mod ast;
mod compile;
mod print;

pub use ast::*;
pub use compile::x64_from_llvm;
pub use print::write;

pub fn print(p: &Prog) {
    let _ = write(std::io::stdout(), p);
}
