pub mod x64;
mod platform;

pub use platform::{Arch, Os, Target};
pub use platform::{get_target, set_target};
