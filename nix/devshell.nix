# FIR development shell: the same toolchain on every supported platform.
{ pkgs }:
let
  inherit (pkgs) lib stdenv;

  # One LLVM release for the C compiler, linker, debugger, and C tooling. Clang
  # builds the C test programs and C API consumers, and links the Rust compiler.
  llvm = pkgs.llvmPackages_23;

  # The AArch64 backend's tests run compiled binaries. On AArch64 hosts they run natively; on
  # x86-64 Linux they're linked by a cross toolchain (GCC driver and glibc for aarch64 Linux)
  # and run under qemu-user.
  cross = pkgs.pkgsCross.aarch64-multiplatform;
  needsCross = stdenv.hostPlatform.isLinux && !stdenv.hostPlatform.isAarch64;

  # The x86-64 backend's tests run Linux x86-64 binaries: natively on x86-64 Linux; on other
  # Linux hosts through a cross toolchain (`x86_64-unknown-linux-gnu-cc`) and qemu-user.
  crossX86 = pkgs.pkgsCross.gnu64;
  needsCrossX86 = stdenv.hostPlatform.isLinux && !stdenv.hostPlatform.isx86_64;

  # The C benchmark harness (frontends/c/bench/cbench.py) links every benchmark statically against
  # the AArch64 target's glibc, so the same binary runs under qemu-user and on any AArch64 Linux
  # machine; its QEMU plugin needs glib's headers (qemu-plugin.h includes glib.h). Linux only.
  benchLibc = lib.optionalString stdenv.hostPlatform.isLinux "${
    (if needsCross then cross else pkgs).glibc.static
  }/lib";
  benchGlib = "-I${pkgs.glib.dev}/include/glib-2.0 -I${pkgs.glib.out}/lib/glib-2.0/include";
  # Its reference GCC: the cross GCC off AArch64, and GCC itself on AArch64 Linux, where the
  # shell's `cc` is Clang (the stdenv is LLVM's).
  benchGcc =
    if needsCross then
      "aarch64-unknown-linux-gnu-cc"
    else
      lib.optionalString stdenv.hostPlatform.isLinux "${pkgs.gcc}/bin/gcc";
in
(pkgs.mkShell.override { stdenv = llvm.stdenv; }) {
  name = "fir-dev";

  packages = [
    # Rust: the FIR compiler
    pkgs.rustc
    pkgs.cargo
    pkgs.clippy
    pkgs.rustfmt
    pkgs.rust-analyzer
    pkgs.cargo-nextest

    # C API: generate the C header from the Rust exports
    pkgs.rust-cbindgen

    # C tooling for the C API header, C tests, and the C frontend: clangd, clang-format, clang-tidy
    llvm.lld
    llvm.clang-tools

    # The C frontend's build tools (frontends/c, fcc); its Clang and LLVM libraries are
    # CMAKE_PREFIX_PATH below
    pkgs.cmake
    pkgs.ninja

    # LLVM tools (llc, opt, llvm-mc, FileCheck) for the LLVM bridge and IR tests
    llvm.llvm
    pkgs.lit
    pkgs.python3

    # Lean 4 semantics and proofs; each Lean project pins its version in `lean-toolchain`
    pkgs.elan

    # SMT solvers for rewrite-rule checking and translation validation
    pkgs.z3
    pkgs.cvc5
    pkgs.bitwuzla

    # WebAssembly target: run, inspect, and optimize .wasm
    pkgs.wasmtime
    pkgs.wabt
    pkgs.binaryen
    pkgs.nodejs

    # Nix formatting (`nix fmt`)
    pkgs.nixfmt-tree
  ]
  # On macOS, use Apple's lldb from the Xcode Command Line Tools: it works with
  # macOS code signing, and nixpkgs often lacks a cached build of the newest lldb.
  ++ lib.optionals stdenv.hostPlatform.isLinux [
    llvm.lldb
    pkgs.gdb
    pkgs.valgrind
    pkgs.mold
  ]
  # AArch64 backend tests on x86-64 Linux: `aarch64-unknown-linux-gnu-cc` and `qemu-aarch64`.
  ++ lib.optionals needsCross [
    cross.stdenv.cc
    pkgs.qemu-user
  ]
  # x86-64 backend tests on other Linux hosts: `x86_64-unknown-linux-gnu-cc` and `qemu-x86_64`.
  ++ lib.optionals needsCrossX86 [
    crossX86.stdenv.cc
  ]
  ++ lib.optionals (needsCrossX86 && !needsCross) [ pkgs.qemu-user ];

  # rust-analyzer needs the standard library sources for go-to-definition and completion.
  RUST_SRC_PATH = "${pkgs.rustPlatform.rustLibSrc}";

  # Where CMake finds Clang's and LLVM's libraries, headers, and packages for the C frontend
  # (the same release as the compiler). Not in `packages`: their `bin` would put an unwrapped
  # clang ahead of the wrapped one on PATH.
  CMAKE_PREFIX_PATH = lib.makeSearchPath "" [
    llvm.libclang.dev
    llvm.llvm.dev
  ];

  FCC_BENCH_LIBC_STATIC = benchLibc;
  FCC_BENCH_GLIB_CFLAGS = benchGlib;
  FCC_BENCH_GCC = benchGcc;

  # Nix's default _FORTIFY_SOURCE flag warns on every -O0 debug build of C code.
  hardeningDisable = [ "fortify" ];
}
