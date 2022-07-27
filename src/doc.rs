use std::{io::{self, Write}, collections::HashSet};

use crate::{xref::XRef, shape::{Gid, MutSelector}};

///! Module defining documentation functionality for bin_prot shapes

pub struct Doc<'a, O> {
    xref: XRef<'a>,
    out: &'a mut O,
    done: HashSet<Gid>,
}

impl<'a, O> Doc<'a, O> {
    pub fn new(xref: XRef<'a>, out: &'a mut O) -> Self {
        Self { xref, out, done: HashSet::new() }
    }

    pub fn generate() -> Result<(), io::Error> {
        todo!()
    }
}

impl<'a, O> MutSelector for Doc<'a, O>
    where O: Write
{
    fn top_app(&mut self, group: &crate::shape::Group, _tid: &crate::shape::Tid, _args: &Vec<crate::shape::Expression>) {
        if !self.done.insert(group.gid) {
            return;
        }
        if let Some((_, name)) = self.xref.for_gid(group.gid) {
            write!(&mut self.out, "### Type {}", name.unwrap_or("<anonimous>")).unwrap();
        }
    }
}
