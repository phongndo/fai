#!/usr/bin/env bash
# Build the QEMU plugins bench.py uses (instruction, load, and store counts; a per-instruction
# histogram) into DIR, against the dev shell's qemu-user headers and nixpkgs' glib.
set -euo pipefail
dir=${1:?usage: build-plugins.sh DIR}
mkdir -p "$dir"
here=$(cd "$(dirname "$0")" && pwd)
qemu=$(dirname "$(dirname "$(readlink -f "$(command -v qemu-aarch64)")")")
glib_dev=$(nix build --no-link --print-out-paths nixpkgs#glib.dev)
glib=$(nix build --no-link --print-out-paths nixpkgs#glib.out)
for p in count hist; do
  nix shell nixpkgs#gcc -c gcc -shared -fPIC -O2 -I"$qemu/include" -I"$glib_dev/include/glib-2.0" \
    -I"$glib/lib/glib-2.0/include" "$here/$p.c" -o "$dir/lib$p.so"
done
echo "built $dir/libcount.so $dir/libhist.so"
