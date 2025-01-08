use std::env::consts::{OS, ARCH};

pub fn mangle(s: &str) -> String {
    match OS {
        "macos" => {
            let mut s = s.to_string();
            s.insert(0, '_');
            s
        }
        "linux" => s.to_string(),
        _ => panic!("unsupported"),
    }
}

pub enum Arch {
    X64,
    Aarch64,
}

/// On success returns the architecture as an `Arch`. On failure returns the arch string.
pub fn arch(s: Option<&str>) -> Result<Arch, String> {
    match s.unwrap_or(ARCH) {
        "x86_64" => Ok(Arch::X64),
        "aarch64" => Ok(Arch::Aarch64),
        s => Err(s.to_string()),
    }
}
