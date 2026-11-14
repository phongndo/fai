//! What every backend's assembly says the same way: symbol spelling and the module's globals as
//! data (bytes, and the addresses of globals and functions they hold), for ELF and Mach-O.

use std::fmt::Write;

use fai_ir::ir::{Globals, Init, Module, Ty};
use fai_ir::types::Shape;

/// A symbol as the assembler writes it: quoted unless it is a plain identifier.
pub fn quote(s: &str) -> String {
    let plain = s
        .chars()
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && s.chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '$');
    if plain {
        s.to_owned()
    } else {
        format!("\"{s}\"")
    }
}

/// How the data refers to symbols: `sym(name, own)` spells a symbol of the module (`own`) or
/// any other, and `extern_prefix` goes before the names of what the module doesn't define.
struct Data<'a> {
    m: &'a Module,
    sym: &'a dyn Fn(&str, bool) -> String,
    extern_prefix: &'a str,
}

fn gs_has(gs: &Globals, name: &str) -> bool {
    (0..gs.len()).any(|g| gs.name(g) == name)
}

impl Data<'_> {
    /// A global's bytes, and the symbols stored in it (offset, symbol).
    fn image(&self, t: Ty, init: Init, out: &mut Vec<u8>, relocs: &mut Vec<(usize, String)>) {
        let gs = &self.m.globals;
        let sp = &self.m.space;
        let size = gs.types.size(sp, t) as usize;
        let start = out.len();
        match (init, t) {
            (Init::Zero, _) | (Init::Null, _) => out.resize(start + size, 0),
            (Init::Int(i), Ty::Int(w) | Ty::Byte(w)) => {
                let n = gs.int(i);
                let m = num_bigint::BigInt::from(1) << w;
                let v = ((n % &m) + &m) % &m;
                let (_, mut bytes) = v.to_bytes_le();
                bytes.resize((w / 8) as usize, 0);
                out.extend_from_slice(&bytes);
            }
            (Init::Float(f, i), Ty::Float(g)) if f == g => {
                let b = gs.float(i);
                out.extend((0..f.width() / 8).map(|k| (b >> (8 * k)) as u8));
            }
            (Init::Int(i), Ty::Ptr) => {
                let w = sp.ptr_bits;
                let n = gs.int(i);
                let m = num_bigint::BigInt::from(1) << w;
                let v = ((n % &m) + &m) % &m;
                let (_, mut bytes) = v.to_bytes_le();
                bytes.resize((w / 8) as usize, 0);
                out.extend_from_slice(&bytes);
            }
            (Init::SymOff(r, i), Ty::Ptr) => {
                let name = gs.text(r);
                let s = if gs_has(gs, name) || self.m.funcs.iter().any(|f| f.name == name) {
                    (self.sym)(name, true)
                } else {
                    (self.sym)(&format!("{}{name}", self.extern_prefix), false)
                };
                let n = gs.int(i);
                let sign = if n.sign() == num_bigint::Sign::Minus {
                    ""
                } else {
                    "+"
                };
                relocs.push((start, format!("{s}{sign}{n}")));
                out.resize(start + 8, 0);
            }
            (Init::Sym(r), Ty::Ptr) => {
                let name = gs.text(r);
                let s = if gs_has(gs, name) || self.m.funcs.iter().any(|f| f.name == name) {
                    (self.sym)(name, true)
                } else {
                    (self.sym)(&format!("{}{name}", self.extern_prefix), false)
                };
                relocs.push((start, s));
                out.resize(start + 8, 0);
            }
            (Init::Bytes(r), _) => out.extend_from_slice(gs.bytes(r)),
            (Init::List(r), Ty::Agg(id)) => {
                out.resize(start + size, 0);
                let items = gs.items(r);
                let mut part = Vec::new();
                let mut put = |off: usize,
                               ty: Ty,
                               item: Init,
                               out: &mut Vec<u8>,
                               relocs: &mut Vec<(usize, String)>| {
                    part.clear();
                    let mut rs = Vec::new();
                    self.image(ty, item, &mut part, &mut rs);
                    let off = start + off;
                    let n = part.len().min(out.len().saturating_sub(off));
                    out[off..off + n].copy_from_slice(&part[..n]);
                    relocs.extend(rs.into_iter().map(|(o, s)| (o + off, s)));
                };
                match gs.types.shape(id) {
                    Shape::Struct(p, fs) => {
                        let (offs, _, _) = gs.types.place(sp, p, fs);
                        for ((&f, &item), off) in fs.iter().zip(items).zip(offs) {
                            put(off as usize, f, item, out, relocs);
                        }
                    }
                    Shape::Array(n, e) => {
                        let stride = gs.types.stride(sp, e) as usize;
                        for (i, &item) in items.iter().take(n as usize).enumerate() {
                            put(i * stride, e, item, out, relocs);
                        }
                    }
                    Shape::Func(..) | Shape::Union(_) => {}
                }
            }
            _ => out.resize(start + size, 0),
        }
    }
}

fn line(out: &mut String, a: std::fmt::Arguments<'_>) {
    out.push('\t');
    let _ = out.write_fmt(a);
    out.push('\n');
}

/// The module's globals as assembly: each in its section (read-only data, relocated read-only
/// data for constants holding addresses, or data), aligned, with its bytes and the addresses it
/// holds. `sym(name, own)` spells symbols (see [`Data`]); `darwin` picks Mach-O's sections and
/// directives over ELF's.
pub fn globals(
    m: &Module,
    sym: &dyn Fn(&str, bool) -> String,
    extern_prefix: &str,
    darwin: bool,
) -> String {
    let d = Data {
        m,
        sym,
        extern_prefix,
    };
    let mut out = String::new();
    let gs = &m.globals;
    for g in 0..gs.len() {
        let t = gs.ty(g);
        let align = gs.types.align(&m.space, t).max(u64::from(gs.align(g)));
        let mut bytes = Vec::new();
        let mut relocs = Vec::new();
        d.image(t, gs.init(g), &mut bytes, &mut relocs);
        if bytes.is_empty() {
            bytes.push(0);
        }
        let section = match (darwin, gs.is_const(g), relocs.is_empty()) {
            (false, true, true) => ".section .rodata",
            (false, true, false) => ".section .data.rel.ro,\"aw\"",
            (false, false, _) => ".data",
            (true, true, true) => ".section __TEXT,__const",
            (true, true, false) => ".section __DATA,__const",
            (true, false, _) => ".data",
        };
        let s = sym(gs.name(g), true);
        out.push('\n');
        line(&mut out, format_args!("{section}"));
        line(&mut out, format_args!(".globl {s}"));
        line(
            &mut out,
            format_args!(".p2align {}", align.trailing_zeros()),
        );
        if !darwin {
            line(&mut out, format_args!(".type {s}, %object"));
            line(&mut out, format_args!(".size {s}, {}", bytes.len()));
        }
        let _ = writeln!(out, "{s}:");
        let mut i = 0;
        let mut ri = relocs.iter().peekable();
        while i < bytes.len() {
            if let Some((o, sym)) = ri.peek()
                && *o == i
            {
                line(&mut out, format_args!(".quad {sym}"));
                i += 8;
                ri.next();
                continue;
            }
            let end = relocs
                .iter()
                .map(|r| r.0)
                .find(|&o| o > i)
                .unwrap_or(bytes.len())
                .min(i + 16);
            let items: Vec<String> = bytes[i..end].iter().map(|b| b.to_string()).collect();
            line(&mut out, format_args!(".byte {}", items.join(", ")));
            i = end;
        }
    }
    out
}
