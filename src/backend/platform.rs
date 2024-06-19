pub fn mangle(s: &str) -> String {
    match std::env::consts::OS {
        "macos" => {
            let mut s = s.to_string();
            s.insert(0, '_');
            s
        }
        "linux" => s.to_string(),
        _ => panic!("unsupported"),
    }
}
