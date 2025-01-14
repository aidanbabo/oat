use once_cell::sync::OnceCell;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arch {
    X64,
    Aarch64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Os {
    MacOs,
    Linux,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Target {
    pub os: Os,
    pub arch: Arch,
}

static TARGET: OnceCell<Target> = OnceCell::new();

pub fn set_target(os: Option<&str>, arch: Option<&str>) -> Result<(), String> {
    use std::env::consts::{OS, ARCH};

    let os = match os.unwrap_or(OS) {
        "macos" => Os::MacOs,
        "linux" => Os::Linux,
        s => return Err(format!("Unsupported os: {s}")),
    };

    let arch = match arch.unwrap_or(ARCH) {
        "x86_64" => Arch::X64,
        "aarch64" => Arch::Aarch64,
        s => return Err(format!("Unsupported arch: {s}")),
    };

    TARGET.set(Target { os, arch }).expect("Target can only be set once");

    Ok(())
}

pub fn get_target() -> &'static Target {
    TARGET.get().expect("Target has been initialized via `set_target`")
}

pub fn mangle(s: &str) -> String {
    match get_target().os {
        Os::MacOs => {
            let mut buf = String::with_capacity(s.len() + 1);
            buf.push('_');
            buf.push_str(s);
            buf
        }
        Os::Linux => s.to_string(),
    }
}
