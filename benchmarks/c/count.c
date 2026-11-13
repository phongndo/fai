/* A QEMU TCG plugin: counts the instructions executed, and the loads and stores they make, at
 * guest addresses in [lo, hi). Prints "COUNT insns loads stores" to stderr at exit.
 * Usage: qemu-aarch64 -plugin libcount.so,lo=0x...,hi=0x... PROGRAM */
#include <qemu-plugin.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

QEMU_PLUGIN_EXPORT int qemu_plugin_version = QEMU_PLUGIN_VERSION;

static uint64_t lo, hi = UINT64_MAX;
static struct qemu_plugin_scoreboard *sb;
static qemu_plugin_u64 insns, loads, stores;

typedef struct { uint64_t insns, loads, stores; } Counts;

static void tb_trans(struct qemu_plugin_tb *tb, void *ud) {
  size_t n = qemu_plugin_tb_n_insns(tb);
  for (size_t i = 0; i < n; i++) {
    struct qemu_plugin_insn *insn = qemu_plugin_tb_get_insn(tb, i);
    uint64_t pc = qemu_plugin_insn_vaddr(insn);
    if (pc < lo || pc >= hi) continue;
    qemu_plugin_register_vcpu_insn_exec_inline_per_vcpu(insn, QEMU_PLUGIN_INLINE_ADD_U64, insns, 1);
    qemu_plugin_register_vcpu_mem_inline_per_vcpu(insn, QEMU_PLUGIN_MEM_R, QEMU_PLUGIN_INLINE_ADD_U64, loads, 1);
    qemu_plugin_register_vcpu_mem_inline_per_vcpu(insn, QEMU_PLUGIN_MEM_W, QEMU_PLUGIN_INLINE_ADD_U64, stores, 1);
  }
}

static void at_exit(void *p) {
  fprintf(stderr, "COUNT %llu %llu %llu\n", (unsigned long long)qemu_plugin_u64_sum(insns),
          (unsigned long long)qemu_plugin_u64_sum(loads), (unsigned long long)qemu_plugin_u64_sum(stores));
}

QEMU_PLUGIN_EXPORT int qemu_plugin_install(qemu_plugin_id_t id, const qemu_info_t *info, int argc, char **argv) {
  for (int i = 0; i < argc; i++) {
    if (!strncmp(argv[i], "lo=", 3)) lo = strtoull(argv[i] + 3, 0, 0);
    if (!strncmp(argv[i], "hi=", 3)) hi = strtoull(argv[i] + 3, 0, 0);
  }
  sb = qemu_plugin_scoreboard_new(sizeof(Counts));
  insns = qemu_plugin_scoreboard_u64_in_struct(sb, Counts, insns);
  loads = qemu_plugin_scoreboard_u64_in_struct(sb, Counts, loads);
  stores = qemu_plugin_scoreboard_u64_in_struct(sb, Counts, stores);
  qemu_plugin_register_vcpu_tb_trans_cb(id, tb_trans, NULL);
  qemu_plugin_register_atexit_cb(id, at_exit, NULL);
  return 0;
}
