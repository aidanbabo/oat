use std::collections::HashMap;
use std::convert::From;

pub mod llvm;
pub mod oat;
pub mod backend;

pub struct StrInterner<T> {
    pool: Vec<Box<str>>,
    mapping: HashMap<Box<str>, u32>,
    phantom: std::marker::PhantomData<T>,
}

impl<T> Default for StrInterner<T> {
    fn default() -> Self {
        Self {
            pool: Default::default(),
            mapping: Default::default(),
            phantom: std::marker::PhantomData,
        }
    }
}

impl<T: From<u32>> StrInterner<T> {
    fn insert(&mut self, s: Box<str>) -> T {
        let ix = self.pool.len() as u32;
        self.pool.push(s.clone());
        self.mapping.insert(s, ix);
        ix.into()
    }

    pub fn intern_boxed_str(&mut self, s: Box<str>) -> T {
        if let Some(&id) = self.mapping.get(&s) {
            return id.into();
        }
        self.insert(s)
    }

    pub fn intern_string(&mut self, s: String) -> T {
        if let Some(&id) = self.mapping.get(&*s) {
            return id.into();
        }
        self.insert(s.into_boxed_str())
    }

    pub fn intern(&mut self, s: &str) -> T {
        if let Some(&id) = self.mapping.get(s) {
            return id.into();
        }
        self.insert(s.to_string().into_boxed_str())
    }

    pub fn complete(self) -> Vec<Box<str>> {
        self.pool
    }
}
