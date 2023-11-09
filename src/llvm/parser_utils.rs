use once_cell::sync::Lazy;
use std::sync::Mutex;

pub fn append<T>(mut v: Vec<T>, t: T) -> Vec<T> {
	v.push(t);
	v
}

// todo: escape!
pub fn escape_string(s: &str) -> String {
    s.to_string()
}

// fixme: global state! ugh!
static ID_COUNT: Lazy<Mutex<i64>> = Lazy::new(|| Mutex::new(0));

pub fn gensym(s: &str) -> String {
    *ID_COUNT.lock().unwrap() += 1;
    format!("_{s}__{}", *ID_COUNT.lock().unwrap())
}

#[allow(dead_code)]
pub fn reset() {
    *ID_COUNT.lock().unwrap() = 0;
}
