use once_cell::sync::Lazy;
use std::sync::Mutex;

pub fn append<T>(mut v: Vec<T>, t: T) -> Vec<T> {
	v.push(t);
	v
}

// should we add support for all hex escapes?
// this means we may need to use Vec<u8> :(
pub fn escape_string(s: &str) -> String {
    let mut out = String::new();
    // skip `c"` at start and `"` at end
    let mut iter = s.chars().skip(2).take(s.len() - 3);

    while let Some(c) = iter.next() {
        if c == '\\' {
            let c2 = iter.next().expect("escaped character");
            if c2 == '\\' {
                out.push('\\');
            } else if c2 == '"' {
                out.push('"');
            } else if c2 == '0' {
                iter.next().filter(|&c| c == '0').expect("second zero digit in hex escape");
                out.push('\0');
            }
        } else {
            out.push(c);
        }
    }
    out
}

// fixme: global state! ugh!
static ID_COUNT: Lazy<Mutex<i64>> = Lazy::new(|| Mutex::new(0));

pub fn gensym(s: &str) -> String {
    *ID_COUNT.lock().unwrap() += 1;
    format!("_{s}__{}", *ID_COUNT.lock().unwrap())
}
