//! A module's globals, mirroring Lean's `Global` and `Init` (`spec/Fir/Syntax.lean`), stored
//! like a body (see `body.rs`): a row of `Copy` fields per global, names in one string, and
//! initializers as `Copy` nodes whose lists, integers, and bytes are runs in shared pools. The
//! globals' types live in their own [`Types`] table.

use num_bigint::BigInt;

use crate::ir::Ty;
use crate::types::Types;

/// A run of entries in one of the pools.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Run {
    start: u32,
    len: u32,
}

impl Run {
    fn range(self) -> std::ops::Range<usize> {
        self.start as usize..(self.start + self.len) as usize
    }
}

fn push_run<T>(pool: &mut Vec<T>, items: impl IntoIterator<Item = T>) -> Run {
    let start = pool.len();
    pool.extend(items);
    let len = pool.len() - start;
    let (Ok(start), Ok(len)) = (u32::try_from(start), u32::try_from(len)) else {
        panic!("a module holds fewer than 2^32 initializer entries of each kind");
    };
    Run { start, len }
}

/// A global's initial contents (Lean's `Init`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Init {
    /// `zero`: every byte zero.
    Zero,
    /// An integer, for an `iN` or `bN`: an index into the integers.
    Int(u32),
    /// `null`
    Null,
    /// `@name`: the address of a global or a function (a run of the names' text).
    Sym(Run),
    /// `bytes "0aff"`: the whole object's bytes.
    Bytes(Run),
    /// `{a, b}`: one initializer per struct field or array element.
    List(Run),
}

/// What a module says about one global, apart from its name.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Row {
    name: Run,
    ty: Ty,
    constant: bool,
    align: u32,
    init: Init,
}

/// A module's globals, in declaration order.
#[derive(Clone, Debug, Default)]
pub struct Globals {
    rows: Vec<Row>,
    /// The types the globals name.
    pub types: Types,
    /// Names: the globals' and the ones initializers take the address of.
    text: String,
    ints: Vec<BigInt>,
    bytes: Vec<u8>,
    items: Vec<Init>,
}

impl Globals {
    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    fn add_text(&mut self, s: &str) -> Run {
        let start = self.text.len();
        self.text.push_str(s);
        Run {
            start: start as u32,
            len: s.len() as u32,
        }
    }

    /// Add a global `global [const] @name: ty [align align] = init`.
    pub fn push(&mut self, name: &str, ty: Ty, constant: bool, align: u32, init: Init) {
        let name = self.add_text(name);
        self.rows.push(Row {
            name,
            ty,
            constant,
            align,
            init,
        });
    }

    /// Replace global `g`'s initializer, so that globals can be declared before the
    /// initializers that take each other's addresses.
    pub fn set_init(&mut self, g: usize, init: Init) {
        self.rows[g].init = init;
    }

    pub fn int_init(&mut self, n: BigInt) -> Init {
        self.ints.push(n);
        Init::Int((self.ints.len() - 1) as u32)
    }

    pub fn sym_init(&mut self, name: &str) -> Init {
        Init::Sym(self.add_text(name))
    }

    pub fn bytes_init(&mut self, bs: impl IntoIterator<Item = u8>) -> Init {
        Init::Bytes(push_run(&mut self.bytes, bs))
    }

    pub fn list_init(&mut self, items: impl IntoIterator<Item = Init>) -> Init {
        Init::List(push_run(&mut self.items, items))
    }

    pub fn name(&self, g: usize) -> &str {
        self.text(self.rows[g].name)
    }

    pub fn ty(&self, g: usize) -> Ty {
        self.rows[g].ty
    }

    pub fn is_const(&self, g: usize) -> bool {
        self.rows[g].constant
    }

    /// The alignment written on the global (1 when none is).
    pub fn align(&self, g: usize) -> u32 {
        self.rows[g].align
    }

    pub fn init(&self, g: usize) -> Init {
        self.rows[g].init
    }

    pub fn text(&self, r: Run) -> &str {
        &self.text[r.range()]
    }

    pub fn int(&self, i: u32) -> &BigInt {
        &self.ints[i as usize]
    }

    pub fn bytes(&self, r: Run) -> &[u8] {
        &self.bytes[r.range()]
    }

    pub fn items(&self, r: Run) -> &[Init] {
        &self.items[r.range()]
    }

    /// The names an initializer takes the address of, in order (Lean's `Init.syms`).
    pub fn syms<'a>(&'a self, init: Init, out: &mut Vec<&'a str>) {
        match init {
            Init::Sym(r) => out.push(self.text(r)),
            Init::List(r) => {
                for &i in self.items(r) {
                    self.syms(i, out);
                }
            }
            _ => {}
        }
    }
}
