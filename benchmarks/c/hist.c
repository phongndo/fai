/* A QEMU TCG plugin: counts how often each instruction at a guest address in [lo, hi) runs.
 * Prints "HIST <address in hex> <count>" lines to stderr at exit; bench.py names them with
 * objdump (this qemu-user has no disassembler). Usage: -plugin libhist.so,lo=0x...,hi=0x... */
#include <qemu-plugin.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

QEMU_PLUGIN_EXPORT int qemu_plugin_version = QEMU_PLUGIN_VERSION;

static uint64_t lo, hi = UINT64_MAX;
typedef struct { uint64_t n; char *mn; } Site;
static GHashTable *sites; /* vaddr -> Site* */

static void exec(unsigned int vcpu, void *ud) { ((Site *)ud)->n++; }

static void tb_trans(struct qemu_plugin_tb *tb, void *ud) {
  size_t n = qemu_plugin_tb_n_insns(tb);
  for (size_t i = 0; i < n; i++) {
    struct qemu_plugin_insn *insn = qemu_plugin_tb_get_insn(tb, i);
    uint64_t pc = qemu_plugin_insn_vaddr(insn);
    if (pc < lo || pc >= hi) continue;
    Site *s = g_hash_table_lookup(sites, GUINT_TO_POINTER(pc));
    if (!s) {
      s = calloc(1, sizeof *s);
      char *d = qemu_plugin_insn_disas(insn);
      char *sp = strchr(d, ' ');
      if (sp) *sp = 0;
      s->mn = strdup(d);
      g_free(d);
      g_hash_table_insert(sites, GUINT_TO_POINTER(pc), s);
    }
    qemu_plugin_register_vcpu_insn_exec_cb(insn, exec, QEMU_PLUGIN_CB_NO_REGS, s);
  }
}

static void at_exit(void *p) {
  GHashTable *by = g_hash_table_new(g_str_hash, g_str_equal);
  GHashTableIter it; gpointer k, v;
  g_hash_table_iter_init(&it, sites);
  while (g_hash_table_iter_next(&it, &k, &v)) {
    Site *s = v;
    uint64_t *c = g_hash_table_lookup(by, s->mn);
    if (!c) { c = calloc(1, sizeof *c); g_hash_table_insert(by, s->mn, c); }
    *c += s->n;
  }
  g_hash_table_iter_init(&it, sites);
  while (g_hash_table_iter_next(&it, &k, &v))
    fprintf(stderr, "HIST %llx %llu\n", (unsigned long long)GPOINTER_TO_SIZE(k),
            (unsigned long long)((Site *)v)->n);
}

QEMU_PLUGIN_EXPORT int qemu_plugin_install(qemu_plugin_id_t id, const qemu_info_t *info, int argc, char **argv) {
  for (int i = 0; i < argc; i++) {
    if (!strncmp(argv[i], "lo=", 3)) lo = strtoull(argv[i] + 3, 0, 0);
    if (!strncmp(argv[i], "hi=", 3)) hi = strtoull(argv[i] + 3, 0, 0);
  }
  sites = g_hash_table_new(g_direct_hash, g_direct_equal);
  qemu_plugin_register_vcpu_tb_trans_cb(id, tb_trans, NULL);
  qemu_plugin_register_atexit_cb(id, at_exit, NULL);
  return 0;
}
