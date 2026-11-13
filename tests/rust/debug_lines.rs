//! Recovering source locations from native code (`fir compile -g`, `Options::debug_lines`).
//!
//! The recovery rule under test: a machine address recovers, through the object's DWARF line
//! table, the `line:col` of the FIR ops its instruction was selected for, or the synthetic file
//! `<fir: no source>` for code no op accounts for (prologues, epilogues, spill code, the trap
//! stub). It recovers a set of ops, not one: ops share locations, and the round trip back to
//! a single op is not claimed.
//!
//! For every fixture the backend compiles (with and without `-O`, each function given a source
//! file), the assembly is assembled by the AArch64 C compiler and its line table read back with
//! `llvm-dwarfdump`. Two properties must hold:
//!
//! * **Fidelity:** every machine instruction's row in the table is the location the emitter
//!   attached to it (its LFIR instruction's, or no source). This holds the assembler to what the
//!   emitter meant: GNU as drops `.loc` rows with line 0, which would attribute an epilogue to
//!   the op before it; the test found that.
//! * **Soundness:** every recovered location (other than no source) is in the file of the
//!   function containing the address, and is the location of some op of that function in the
//!   module before lowering, so an address never names an op of another function or one that
//!   doesn't exist.
//!
//! Without the toolchain (`$FIR_CC` or `aarch64-unknown-linux-gnu-cc`, and `llvm-dwarfdump`)
//! the test records a skip, which a full verification refuses.

#[allow(dead_code)]
mod common;

use std::collections::{BTreeMap, HashSet};
use std::path::{Path, PathBuf};
use std::process::Command;

use common::evidence::Evidence;
use fir::backend::aarch64 as a64;

fn on_path(tool: &str) -> bool {
    Command::new(tool).arg("--version").output().is_ok()
}

/// Every op's location in a function, at any depth.
fn locs(b: &fir::Body) -> HashSet<(u32, u32)> {
    let mut out = HashSet::new();
    let mut stack = vec![b.ops(b.entry())];
    while let Some(it) = stack.last_mut() {
        match it.next() {
            Some(op) => {
                if let Some(l) = b.loc(op) {
                    out.insert((l.line, l.col));
                }
                for &r in b.regions(op).iter().rev() {
                    stack.push(b.ops(r));
                }
            }
            None => {
                stack.pop();
            }
        }
    }
    out
}

/// A `.loc` or line-table row: file number, line, column.
type Row = (u32, u32, u32);

/// What the emitter meant, read off its assembly: for each instruction of `.text` (4 bytes each,
/// from address 0), the `.loc` in force (file number, line, col) and the function it is in.
fn intended(asm: &str) -> Vec<(Option<Row>, Option<String>)> {
    let mut out = Vec::new();
    let (mut text, mut at, mut func) = (true, None, None);
    for line in asm.lines() {
        let t = line.trim();
        if let Some(rest) = t.strip_prefix(".loc ") {
            let n: Vec<u32> = rest.split(' ').map(|x| x.parse().unwrap()).collect();
            at = Some((n[0], n[1], n[2]));
        } else if t == ".text" {
            text = true;
        } else if t == ".data" || t.starts_with(".section") {
            text = false;
        } else if t.starts_with(".type ") && t.ends_with("%function") {
            let name = t[6..]
                .split(',')
                .next()
                .unwrap()
                .trim_matches('"')
                .to_owned();
            func = Some(name);
        } else if text && line.starts_with('\t') && !t.starts_with('.') && !t.ends_with(':') {
            out.push((at, func.clone()));
        }
    }
    out
}

/// The line table's rows: address, line, column, file number.
fn rows(dump: &str) -> Vec<(u64, u32, u32, u32)> {
    dump.lines()
        .filter(|l| l.starts_with("0x"))
        .map(|l| {
            let f: Vec<&str> = l.split_whitespace().collect();
            (
                u64::from_str_radix(&f[0][2..], 16).unwrap(),
                f[1].parse().unwrap(),
                f[2].parse().unwrap(),
                f[3].parse().unwrap(),
            )
        })
        .collect()
}

/// The line table's file names by number, as the object holds them: the assembler splits a
/// `.file` path into an include directory and a name, joined back here. `llvm-dwarfdump` prints
/// them escaped (LLVM's `write_escaped`: `\\`, `\"`, `\n`, `\t`, and `\ooo` for other bytes),
/// which is undone, so names compare as the bytes the object holds.
fn dwarf_files(dump: &str) -> BTreeMap<u32, String> {
    fn quoted(s: &str) -> Option<String> {
        let s = s.trim().strip_prefix('"')?.strip_suffix('"')?.as_bytes();
        let (mut out, mut i) = (Vec::new(), 0);
        while i < s.len() {
            if s[i] != b'\\' {
                out.push(s[i]);
                i += 1;
                continue;
            }
            match *s.get(i + 1)? {
                b'n' => out.push(b'\n'),
                b't' => out.push(b'\t'),
                b'0'..=b'7' => {
                    let o = std::str::from_utf8(s.get(i + 1..i + 4)?).ok()?;
                    out.push(u8::from_str_radix(o, 8).ok()?);
                    i += 2;
                }
                c => out.push(c),
            }
            i += 2;
        }
        String::from_utf8(out).ok()
    }
    fn index(s: &str) -> Option<u32> {
        s.split_once('[')?.1.split_once(']')?.0.trim().parse().ok()
    }
    let (mut dirs, mut files) = (BTreeMap::new(), BTreeMap::new());
    let mut lines = dump.lines().map(str::trim);
    while let Some(l) = lines.next() {
        if l.starts_with("include_directories[") {
            let (k, v) = l.split_once('=').unwrap();
            dirs.insert(index(k).unwrap(), quoted(v).unwrap());
        } else if l.starts_with("file_names[") {
            let n = index(l).unwrap();
            let name = quoted(lines.next().unwrap().strip_prefix("name:").unwrap()).unwrap();
            let d: u32 = lines
                .next()
                .unwrap()
                .strip_prefix("dir_index:")
                .unwrap()
                .trim()
                .parse()
                .unwrap();
            let path = match dirs.get(&d) {
                Some(dir) if d > 0 => format!("{dir}/{name}"),
                _ => name,
            };
            files.insert(n, path);
        }
    }
    files
}

/// Compile one module with line info and check both properties; how many instructions had a
/// source location. With `give_files`, functions without a source file get one.
fn check(
    m: &fir::Module,
    optimize: bool,
    cc: &str,
    dir: &Path,
    name: &str,
    give_files: bool,
) -> Result<Option<(u64, u64)>, String> {
    let mut m = m.clone();
    if give_files {
        for f in &mut m.funcs {
            f.file.get_or_insert_with(|| format!("{name}.src"));
        }
    }
    let Ok(lowered) = fir::backend::prepare(&m, optimize) else {
        return Ok(None);
    };
    let o = a64::Options {
        os: a64::Os::Linux,
        prefix: String::new(),
        extern_prefix: String::new(),
        debug_lines: true,
    };
    let Ok(asm) = a64::compile(&lowered, &o) else {
        return Ok(None);
    };
    let (s, obj) = (dir.join(format!("{name}.s")), dir.join(format!("{name}.o")));
    std::fs::write(&s, &asm).unwrap();
    let mut words = cc.split_whitespace();
    let out = Command::new(words.next().unwrap_or(cc))
        .args(words)
        .arg("-w")
        .arg("-c")
        .arg(&s)
        .arg("-o")
        .arg(&obj)
        .output()
        .map_err(|e| format!("{cc}: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "{cc} -c: {}",
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    let dump = Command::new("llvm-dwarfdump")
        .arg("--debug-line")
        .arg(&obj)
        .output()
        .map_err(|e| format!("llvm-dwarfdump: {e}"))?;
    let dump = String::from_utf8_lossy(&dump.stdout);
    let (rows, files) = (rows(&dump), dwarf_files(&dump));
    let by_name: BTreeMap<&str, HashSet<(u32, u32)>> = m
        .funcs
        .iter()
        .map(|f| (f.name.as_str(), locs(&f.body)))
        .collect();
    let (mut located, mut total) = (0, 0);
    for (i, (want, func)) in intended(&asm).into_iter().enumerate() {
        let addr = 4 * i as u64;
        total += 1;
        let got = rows
            .iter()
            .take_while(|r| r.0 <= addr)
            .last()
            .map(|r| (r.3, r.1, r.2));
        if want.is_none() {
            return Err(format!(
                "{name}: instruction {i} (address {addr:#x}) has no line row: every instruction \
                 needs one, or a debugger attributes it to whatever came before"
            ));
        }
        if got != want {
            return Err(format!(
                "{name}: instruction {i} (address {addr:#x}): the line table says {got:?}, the \
                 emitter wrote {want:?}"
            ));
        }
        let Some((file, line, col)) = got else {
            continue;
        };
        let fname = files.get(&file).map_or("?", String::as_str);
        if fname == a64::emit::NO_SOURCE {
            continue;
        }
        located += 1;
        let func = func.ok_or(format!("{name}: address {addr:#x} is in no function"))?;
        let own = m
            .funcs
            .iter()
            .find(|f| f.name == func)
            .and_then(|f| f.file.as_deref());
        if Some(fname) != own {
            return Err(format!(
                "{name}: @{func} at {addr:#x} is attributed to {fname}"
            ));
        }
        if !by_name
            .get(func.as_str())
            .is_some_and(|ls| ls.contains(&(line, col)))
        {
            return Err(format!(
                "{name}: @{func} at {addr:#x} recovers {line}:{col}, which no op of @{func} has"
            ));
        }
    }
    Ok(Some((located, total)))
}

/// The AArch64 C compiler, if it and `llvm-dwarfdump` are installed; otherwise records a skip
/// (a panic under `FIR_REQUIRE_FULL`).
fn toolchain(ev: &Evidence) -> Option<String> {
    let cc = std::env::var("FIR_CC").unwrap_or_else(|_| {
        // The test assembles Linux ELF: macOS's `cc` makes Mach-O, so there it is LLVM's
        // assembler for Linux, which reads the same directives (nothing is linked or run).
        if cfg!(target_os = "macos") {
            "clang --target=aarch64-unknown-linux-gnu".to_owned()
        } else if cfg!(target_arch = "aarch64") {
            "cc".to_owned()
        } else {
            "aarch64-unknown-linux-gnu-cc".to_owned()
        }
    });
    if on_path(cc.split_whitespace().next().unwrap_or("")) && on_path("llvm-dwarfdump") {
        ev.fact("assembler", cc.clone());
        return Some(cc);
    }
    if std::env::var("FIR_REQUIRE_FULL").is_ok() {
        panic!("debug_lines needs {cc} and llvm-dwarfdump");
    }
    ev.skip(format!("no {cc} or llvm-dwarfdump"));
    ev.write();
    None
}

/// Cases the fixtures don't have, each found by review: an op on line 0 (DWARF's "no source",
/// which GNU as drops, so the instruction kept the line before it), a file name that needs
/// escaping (the test once read names off the assembly, undecoded), and a module with no
/// source files at all (which once got no line table).
#[test]
fn line_zero_escaped_file_names_and_modules_without_files() {
    let ev = Evidence::new("debug_lines_edges");
    let Some(cc) = toolchain(&ev) else {
        return;
    };
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("debug-lines-edges");
    std::fs::create_dir_all(&dir).unwrap();
    let body = r#"(%x: i64) -> i64 FILE {
  %a: i64 = int.const 2 @10:2
  %b: i64 = int.add.wrap %x, %a @0:2
  %c: i64 = int.mul.wrap %b, %b @0:5
  func.ret %c @11:1
}
"#;
    // Set directly: a name the `.fir` text can't spell, but a front end can hand over.
    let cases = [
        ("escaped", Some("dir\\sub\"q\"\n\t\u{1}.c"), true),
        ("no-files", None, false),
    ];
    for (name, file, located) in cases {
        let mut m = fir::parse_module(&format!("func @f{}", body.replace("FILE", "")))
            .unwrap_or_else(|e| panic!("{name}: {e:?}"));
        m.funcs[0].file = file.map(str::to_owned);
        for optimize in [false, true] {
            let n = format!("{name}{}", if optimize { "-O" } else { "" });
            let (got, total) = check(&m, optimize, &cc, &dir, &n, false)
                .unwrap_or_else(|e| panic!("{e}"))
                .unwrap_or_else(|| panic!("{n}: the backend refused it"));
            assert!(total > 0, "{n}");
            assert_eq!(got > 0, located, "{n}: {got} of {total} located");
            ev.count("modules", 1);
        }
    }
    ev.write();
}

#[test]
fn native_addresses_recover_the_source_locations_of_their_ops() {
    let ev = Evidence::new("debug_lines");
    let Some(cc) = toolchain(&ev) else {
        return;
    };
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("debug-lines");
    std::fs::create_dir_all(&dir).unwrap();
    let mut fails = Vec::new();
    // `FIR_DEBUG_LINES_DIR`: more modules to check, such as `fcc --emit hfir` output of the C
    // corpus, whose functions carry their own files and locations on every op.
    let mut files = common::fir_files();
    if let Ok(d) = std::env::var("FIR_DEBUG_LINES_DIR") {
        let mut more: Vec<PathBuf> = std::fs::read_dir(&d)
            .expect("FIR_DEBUG_LINES_DIR")
            .map(|e| e.unwrap().path())
            .filter(|p| p.extension().is_some_and(|x| x == "fir"))
            .collect();
        more.sort();
        files.extend(more);
    }
    for file in files {
        let text = std::fs::read_to_string(&file).unwrap();
        let Ok(m) = fir::parse_module(&text) else {
            continue;
        };
        if fir::verify_module(&m).is_err() || matches!(m.layer, fir::Layer::Lfir(_)) {
            continue;
        }
        let name = file
            .strip_prefix(env!("CARGO_MANIFEST_DIR"))
            .map_or_else(|_| file.display().to_string(), |p| p.display().to_string())
            .replace(['/', '.'], "_");
        for optimize in [false, true] {
            let n = format!("{name}{}", if optimize { "-O" } else { "" });
            match check(&m, optimize, &cc, &dir, &n, true) {
                Ok(Some((located, total))) => {
                    ev.count("modules", 1);
                    ev.count("instructions", total);
                    ev.count("instructions with a source location", located);
                }
                Ok(None) => ev.count("modules the backend doesn't compile", 1),
                Err(e) => fails.push(e),
            }
        }
    }
    ev.write();
    assert!(
        fails.is_empty(),
        "{} failures:\n{}",
        fails.len(),
        fails.join("\n")
    );
}
