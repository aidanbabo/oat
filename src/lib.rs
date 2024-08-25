use std::collections::HashMap;

pub mod llvm;
pub mod oat;
pub mod backend;

#[derive(Default)]
pub struct StrInterner {
    pool: Vec<Box<str>>,
    mapping: HashMap<Box<str>, u32>,
}

impl StrInterner {
    fn insert(&mut self, s: Box<str>) -> u32 {
        let ix = self.pool.len() as u32;
        self.pool.push(s.clone());
        self.mapping.insert(s, ix);
        ix
    }

    pub fn intern_boxed_str(&mut self, s: Box<str>) -> u32 {
        if let Some(&id) = self.mapping.get(&s) {
            return id;
        }
        self.insert(s)
    }

    pub fn intern_string(&mut self, s: String) -> u32 {
        if let Some(&id) = self.mapping.get(&*s) {
            return id;
        }
        self.insert(s.into_boxed_str())
    }

    pub fn intern(&mut self, s: &str) -> u32 {
        if let Some(&id) = self.mapping.get(s) {
            return id;
        }
        self.insert(s.to_string().into_boxed_str())
    }

    pub fn complete(self) -> Vec<Box<str>> {
        self.pool
    }
}
