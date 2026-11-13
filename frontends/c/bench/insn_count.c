// A QEMU TCG plugin that counts executed guest instructions and classifies memory accesses, for
// `cbench.py count`. Instruction counts are architectural facts about the code a compiler
// produced, so counting them under emulation is exact; time under emulation says nothing about
// AArch64 hardware, and nothing here measures it.
//
// At exit it writes to `outfile=PATH`:
//
//   S <initial sp hex> <stack window low hex> <stack window high hex> <deep accesses>
//   B <vaddr hex> <instructions> <executions>       one per translated block that executed
//   M <vaddr hex> <stack loads> <stack stores> <other loads> <other stores>
//                                                   one per instruction that accessed memory
//
// AArch64 instructions are 4 bytes, so a block covers [vaddr, vaddr + 4 * instructions); the
// reader disassembles the (static) binary to name them. A block or instruction QEMU translated
// twice appears twice; the reader sums them.
//
// An access is to the stack if its address is in [sp0 - below, sp0 + above), sp0 being the stack
// pointer at the first instruction. That is only sound if the window lies inside the stack
// mapping, which qemu-user places directly above the program's first mmap()ed memory: so the
// caller runs QEMU with a known stack size (`-s 8M`) and an empty environment (sp0 within a few KiB
// of the top), and passes a window well inside it (below=7 MiB), and checks with `-strace` that no
// mapping meets it. Accesses in [sp0 - below - deep, sp0 - below) are counted as "deep": stack the
// window misses (the caller then refuses the run).
//
// Usage: -plugin insn_count.so,outfile=PATH,below=BYTES,above=BYTES,deep=BYTES
// Build: cc -shared -fPIC -O2 -I GLIB_INCLUDES -I QEMU/include insn_count.c -o insn_count.so
#include <glib.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <qemu-plugin.h>

QEMU_PLUGIN_EXPORT int qemu_plugin_version = QEMU_PLUGIN_VERSION;

struct block {
  uint64_t vaddr;
  uint64_t count;
  size_t n;
  struct block *next;
};

struct access {
  uint64_t vaddr;
  uint64_t stack_loads, stack_stores, other_loads, other_stores;
  struct access *next;
};

static struct block *blocks;
static struct access *accesses;
static GMutex lock;
static char *outfile;
static struct qemu_plugin_register *sp_handle;
static uint64_t sp0, stack_lo, stack_hi, deep_lo, deep;
static uint64_t below, above, deep_size;
static int have_sp;

// The benchmarks are single-threaded, so plain increments are exact.
static void on_exec(unsigned int vcpu, void *udata) {
  (void)vcpu;
  ((struct block *)udata)->count++;
}

static void on_vcpu_init(unsigned int vcpu, void *udata) {
  (void)vcpu;
  (void)udata;
  GArray *regs = qemu_plugin_get_registers();
  for (guint i = 0; regs && i < regs->len; i++) {
    qemu_plugin_reg_descriptor *r = &g_array_index(regs, qemu_plugin_reg_descriptor, i);
    if (strcmp(r->name, "sp") == 0)
      sp_handle = r->handle;
  }
  if (regs)
    g_array_free(regs, TRUE);
}

static void read_sp(unsigned int vcpu, void *udata) {
  (void)vcpu;
  (void)udata;
  if (have_sp || !sp_handle)
    return;
  GByteArray *buf = g_byte_array_new();
  if (qemu_plugin_read_register(sp_handle, buf) && buf->len == 8) {
    memcpy(&sp0, buf->data, 8);  // target byte order: little-endian, as the host's
    stack_lo = sp0 - below;
    stack_hi = sp0 + above;
    deep_lo = stack_lo - deep_size;
    have_sp = 1;
  }
  g_byte_array_free(buf, TRUE);
}

static void on_mem(unsigned int vcpu, qemu_plugin_meminfo_t info, uint64_t vaddr, void *udata) {
  (void)vcpu;
  struct access *a = udata;
  int stack = have_sp && vaddr >= stack_lo && vaddr < stack_hi;
  if (have_sp && vaddr >= deep_lo && vaddr < stack_lo)
    deep++;
  if (qemu_plugin_mem_is_store(info))
    stack ? a->stack_stores++ : a->other_stores++;
  else
    stack ? a->stack_loads++ : a->other_loads++;
}

static void on_trans(struct qemu_plugin_tb *tb, void *udata) {
  (void)udata;
  struct block *b = calloc(1, sizeof *b);
  b->vaddr = qemu_plugin_tb_vaddr(tb);
  b->n = qemu_plugin_tb_n_insns(tb);
  g_mutex_lock(&lock);
  b->next = blocks;
  blocks = b;
  for (size_t i = 0; i < b->n; i++) {
    struct qemu_plugin_insn *insn = qemu_plugin_tb_get_insn(tb, i);
    struct access *a = calloc(1, sizeof *a);
    a->vaddr = qemu_plugin_insn_vaddr(insn);
    a->next = accesses;
    accesses = a;
    qemu_plugin_register_vcpu_mem_cb(insn, on_mem, QEMU_PLUGIN_CB_NO_REGS, QEMU_PLUGIN_MEM_RW, a);
  }
  g_mutex_unlock(&lock);
  if (!have_sp)
    qemu_plugin_register_vcpu_tb_exec_cb(tb, read_sp, QEMU_PLUGIN_CB_R_REGS, NULL);
  qemu_plugin_register_vcpu_tb_exec_cb(tb, on_exec, QEMU_PLUGIN_CB_NO_REGS, b);
}

static void write_counts(void *udata) {
  (void)udata;
  FILE *f = fopen(outfile, "w");
  if (!f) {
    qemu_plugin_outs("insn_count: can't open outfile\n");
    return;
  }
  fprintf(f, "S %" PRIx64 " %" PRIx64 " %" PRIx64 " %" PRIu64 "\n", sp0, stack_lo, stack_hi, deep);
  for (struct block *b = blocks; b; b = b->next)
    if (b->count)
      fprintf(f, "B %" PRIx64 " %zu %" PRIu64 "\n", b->vaddr, b->n, b->count);
  for (struct access *a = accesses; a; a = a->next)
    if (a->stack_loads || a->stack_stores || a->other_loads || a->other_stores)
      fprintf(f, "M %" PRIx64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n", a->vaddr,
              a->stack_loads, a->stack_stores, a->other_loads, a->other_stores);
  fclose(f);
}

QEMU_PLUGIN_EXPORT int qemu_plugin_install(qemu_plugin_id_t id, const qemu_info_t *info,
                                           int argc, char **argv) {
  (void)info;
  for (int i = 0; i < argc; i++)
    if (strncmp(argv[i], "outfile=", 8) == 0)
      outfile = g_strdup(argv[i] + 8);
    else if (strncmp(argv[i], "below=", 6) == 0)
      below = strtoull(argv[i] + 6, NULL, 0);
    else if (strncmp(argv[i], "above=", 6) == 0)
      above = strtoull(argv[i] + 6, NULL, 0);
    else if (strncmp(argv[i], "deep=", 5) == 0)
      deep_size = strtoull(argv[i] + 5, NULL, 0);
  if (!outfile || !below || !above || !deep_size) {
    fprintf(stderr, "insn_count: outfile=PATH, below=, above=, and deep=BYTES are required\n");
    return -1;
  }
  qemu_plugin_register_vcpu_init_cb(id, on_vcpu_init, NULL);
  qemu_plugin_register_vcpu_tb_trans_cb(id, on_trans, NULL);
  qemu_plugin_register_atexit_cb(id, write_counts, NULL);
  return 0;
}
