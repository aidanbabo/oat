use super::ast;

impl<'a> ast::Cfg<'a> {
    pub fn block_iter(&self) -> impl Iterator<Item = &ast::Block<'a>> {
        std::iter::once(&self.entry).chain(self.blocks.iter().map(|(_, b)| b))
    }
    pub fn block_iter_mut(&mut self) -> impl Iterator<Item = &mut ast::Block<'a>> {
        std::iter::once(&mut self.entry).chain(self.blocks.iter_mut().map(|(_, b)| b))
    }
}
