/* The round's end-to-end test: a program built through the C API only, using every HFIR
 * building block (aggregate values, checked arithmetic, a tagged union, slices, exceptions)
 * with loops and cf.blocks, stack and heap memory, a global, an external call, and an indirect
 * call. It is verified and run in the interpreter (fir_module_run), which gives the expected
 * outcome lines; lowered and optimized, which must give them again; and compiled to AArch64
 * assembly (fir_module_compile, with and without -O), which is assembled and linked with a
 * generated main that prints each run's outcome in fir run's format, run (under qemu-aarch64
 * off AArch64), and compared.
 *
 * crates/fir-capi/tests/c.rs builds and runs it, with the toolchain in the environment:
 * FIR_E2E_CC (an AArch64 C compiler), FIR_E2E_RUN (the emulator, empty to run natively), and
 * FIR_E2E_DIR (a scratch directory). Without FIR_E2E_CC the native half is skipped. It prints
 * what it compared and "ok" when every check passes. */

#define _POSIX_C_SOURCE 200809L /* popen */

#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "fir.h"

static int failures = 0;
static FirModule *cur = NULL;

#define CHECK(cond)                                                                  \
  do {                                                                               \
    if (!(cond)) {                                                                   \
      fprintf(stderr, "%s:%d: check failed: %s\n", __FILE__, __LINE__, #cond);       \
      failures++;                                                                    \
    }                                                                                \
  } while (0)

#define ID(x) id_ok((x), __LINE__, #x)
#define OK(x) status_ok((x), __LINE__, #x)

static uint32_t id_ok(uint32_t x, int line, const char *what) {
  if (x == FIR_INVALID) {
    fprintf(stderr, "%s:%d: %s failed: %s\n", __FILE__, line, what, fir_module_error(cur));
    failures++;
  }
  return x;
}

static void status_ok(FirStatus s, int line, const char *what) {
  if (s != FIR_OK) {
    fprintf(stderr, "%s:%d: %s failed (%u): %s\n", __FILE__, line, what, s,
            fir_module_error(cur));
    failures++;
  }
}

static FirTarget to(FirRegion block, const FirValue *args, size_t nargs) {
  FirTarget t = {block, args, nargs};
  return t;
}

static FirValue result(FirBuilder *b, FirOp op, uint32_t i) {
  return ID(fir_op_result(b, op, i));
}

/* The module. */

static FirModule *build(void) {
  FirModule *m = cur = fir_module_new();
  FirType i32 = fir_type_int(32), i64 = fir_type_int(64), slice = FIR_TYPE_SLICE;
  FirType arr = ID(fir_type_array(m, 4, i32));
  FirType two[2] = {i32, i32};
  FirType pair = ID(fir_type_struct(m, FIR_POLICY_C, two, 2));
  FirType variants[2] = {i32, i64};
  FirType u = ID(fir_type_union(m, variants, 2));
  FirType step_sig = ID(fir_type_func(m, &i32, 1, &i32, 1));

  /* global @prices: array<4 x i32> = {3, 5, 7, 11} */
  FirInit items[4] = {ID(fir_init_int(m, 3)), ID(fir_init_int(m, 5)), ID(fir_init_int(m, 7)),
                      ID(fir_init_int(m, 11))};
  FirGlobal prices = ID(fir_global_declare(m, "prices", arr, false, 4,
                                           ID(fir_init_list(m, items, 4))));
  /* extern func @record(i64) -> i32 effects[] assume */
  FirFunc record = ID(fir_extern_declare(m, "record", &i64, 1, &i32, 1, NULL, 0,
                                         FIR_TRUST_ASSUME));
  FirFunc raise = ID(fir_func_declare(m, "raise", &i32, 1, NULL, 0));
  FirFunc sum = ID(fir_func_declare(m, "sum", &slice, 1, &i32, 1));
  FirFunc classify = ID(fir_func_declare(m, "classify", &i32, 1, &u, 1));
  FirFunc swap = ID(fir_func_declare(m, "swap", &pair, 1, &pair, 1));
  FirFunc steps = ID(fir_func_declare(m, "steps", &i32, 1, &i32, 1));
  FirType run_rets[3] = {i32, i32, i64};
  FirFunc run = ID(fir_func_declare(m, "e2e_run", &i32, 1, run_rets, 3));
  FirFunc pick = ID(fir_func_declare(m, "e2e_pick", &i64, 1, &i32, 1));

  /* @raise(%code: i32): throw a fresh heap object holding the code. */
  FirBuilder *b = fir_func_begin(m, raise);
  OK(fir_set_file(b, "e2e.c"));
  FirValue code = ID(fir_builder_param(b, 0));
  FirValue eight = ID(fir_int_const(b, i64, 8));
  OK(fir_set_loc(b, 10, 3));
  FirValue obj = ID(fir_mem_alloc(b, FIR_ALLOC_FAIL_TRAP, "c.malloc", eight, 8));
  ID(fir_mem_store(b, i32, code, obj, 8));
  ID(fir_exn_throw(b, obj));
  OK(fir_func_end(b));

  /* @sum(%s: slice) -> i32: a loop over the slice, with checked additions; overflow raises 2. */
  b = fir_func_begin(m, sum);
  FirValue s = ID(fir_builder_param(b, 0));
  FirValue n = ID(fir_slice_len(b, s));
  FirValue inits[2] = {ID(fir_int_const(b, i64, 0)), ID(fir_int_const(b, i32, 0))};
  FirOp loop = ID(fir_cf_loop_begin(b, &i32, 1, false, inits, 2));
  FirRegion body = ID(fir_op_region(b, loop, 0));
  FirValue i = ID(fir_region_param(b, body, 0)), acc = ID(fir_region_param(b, body, 1));
  OK(fir_position_at_end(b, body));
  FirOp done = ID(fir_cf_if_begin(b, NULL, 0, ID(fir_int_cmp(b, FIR_PRED_UGE, i, n))));
  OK(fir_position_at_end(b, ID(fir_op_region(b, done, 0))));
  ID(fir_cf_break(b, &acc, 1));
  OK(fir_position_at_end(b, ID(fir_op_region(b, done, 1))));
  ID(fir_cf_yield(b, NULL, 0));
  OK(fir_position_at_end(b, body));
  OK(fir_set_loc(b, 20, 5));
  FirValue x = ID(fir_slice_get(b, i32, true, s, i, 4));
  FirOp add = ID(fir_int_overflow(b, FIR_ARITH_OP_ADD, true, acc, x));
  FirOp over = ID(fir_cf_if_begin(b, NULL, 0, result(b, add, 1)));
  OK(fir_position_at_end(b, ID(fir_op_region(b, over, 0))));
  FirValue c2 = ID(fir_int_const(b, i32, 2));
  ID(fir_func_call(b, raise, &c2, 1));
  ID(fir_cf_yield(b, NULL, 0));
  OK(fir_position_at_end(b, ID(fir_op_region(b, over, 1))));
  ID(fir_cf_yield(b, NULL, 0));
  OK(fir_position_at_end(b, body));
  FirValue next[2] = {ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_WRAP, i,
                                       ID(fir_int_const(b, i64, 1)))),
                      result(b, add, 0)};
  ID(fir_cf_continue(b, next, 2));
  OK(fir_position_at_end(b, fir_builder_entry(b)));
  FirValue total = result(b, loop, 0);
  ID(fir_func_ret(b, &total, 1));
  OK(fir_func_end(b));

  /* @classify(%x: i32) -> union<i32, i64>: variant 0 holds a non-negative x, variant 1 -x. */
  b = fir_func_begin(m, classify);
  x = ID(fir_builder_param(b, 0));
  FirValue neg = ID(fir_int_cmp(b, FIR_PRED_SLT, x, ID(fir_int_const(b, i32, 0))));
  FirOp which = ID(fir_cf_if_begin(b, &u, 1, neg));
  OK(fir_position_at_end(b, ID(fir_op_region(b, which, 0))));
  FirValue wide = ID(fir_int_sext(b, i64, x));
  FirValue mag = ID(fir_int_arith(b, FIR_ARITH_OP_SUB, FIR_OVF_WRAP,
                                  ID(fir_int_const(b, i64, 0)), wide));
  FirValue u1 = ID(fir_union_make(b, u, mag, 1));
  ID(fir_cf_yield(b, &u1, 1));
  OK(fir_position_at_end(b, ID(fir_op_region(b, which, 1))));
  FirValue u0 = ID(fir_union_make(b, u, x, 0));
  ID(fir_cf_yield(b, &u0, 1));
  OK(fir_position_at_end(b, fir_builder_entry(b)));
  FirValue uv = result(b, which, 0);
  ID(fir_func_ret(b, &uv, 1));
  OK(fir_func_end(b));

  /* @swap(%p: struct<C>{i32, i32}) -> struct<C>{i32, i32} */
  b = fir_func_begin(m, swap);
  FirValue p = ID(fir_builder_param(b, 0));
  FirValue a0 = ID(fir_agg_extract(b, i32, p, 0)), a1 = ID(fir_agg_extract(b, i32, p, 1));
  FirValue sw = ID(fir_agg_insert(b, ID(fir_agg_insert(b, p, a1, 0)), a0, 1));
  ID(fir_func_ret(b, &sw, 1));
  OK(fir_func_end(b));

  /* @steps(%n: i32) -> i32: Collatz steps down to 1, as jumps between blocks. */
  b = fir_func_begin(m, steps);
  n = ID(fir_builder_param(b, 0));
  FirOp blocks = ID(fir_cf_blocks_begin(b, &i32, 1, false));
  FirType two32[2] = {i32, i32};
  FirRegion entry = ID(fir_block_new(b, blocks, "entry", NULL, 0));
  FirRegion top = ID(fir_block_new(b, blocks, "top", two32, 2));
  FirRegion step = ID(fir_block_new(b, blocks, "step", two32, 2));
  FirRegion up = ID(fir_block_new(b, blocks, "up", two32, 2));
  FirRegion down = ID(fir_block_new(b, blocks, "down", two32, 2));
  FirRegion out = ID(fir_block_new(b, blocks, "out", &i32, 1));
  OK(fir_position_at_end(b, entry));
  FirValue start[2] = {n, ID(fir_int_const(b, i32, 0))};
  ID(fir_cf_br(b, to(top, start, 2)));
  OK(fir_position_at_end(b, top));
  FirValue tx = ID(fir_region_param(b, top, 0)), tc = ID(fir_region_param(b, top, 1));
  FirValue small = ID(fir_int_cmp(b, FIR_PRED_SLE, tx, ID(fir_int_const(b, i32, 1))));
  FirValue both[2] = {tx, tc};
  ID(fir_cf_cond_br(b, small, to(out, &tc, 1), to(step, both, 2)));
  OK(fir_position_at_end(b, step));
  FirValue sx = ID(fir_region_param(b, step, 0)), sc = ID(fir_region_param(b, step, 1));
  FirValue one = ID(fir_int_const(b, i32, 1));
  FirValue odd = ID(fir_int_cmp(b, FIR_PRED_NE, ID(fir_int_bit(b, FIR_BIT_OP_AND, sx, one)),
                                ID(fir_int_const(b, i32, 0))));
  FirValue moved[2] = {sx, ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_WRAP, sc, one))};
  ID(fir_cf_cond_br(b, odd, to(up, moved, 2), to(down, moved, 2)));
  OK(fir_position_at_end(b, up));
  FirValue ux = ID(fir_region_param(b, up, 0));
  FirValue tripled = ID(fir_int_arith(b, FIR_ARITH_OP_MUL, FIR_OVF_WRAP, ux,
                                      ID(fir_int_const(b, i32, 3))));
  FirValue upn[2] = {ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_WRAP, tripled,
                                      ID(fir_int_const(b, i32, 1)))),
                     ID(fir_region_param(b, up, 1))};
  ID(fir_cf_br(b, to(top, upn, 2)));
  OK(fir_position_at_end(b, down));
  FirValue dx = ID(fir_region_param(b, down, 0));
  FirValue downn[2] = {ID(fir_int_shift(b, FIR_SHIFT_OP_SHR_S, FIR_SHIFT_EDGE_MASK, dx,
                                        ID(fir_int_const(b, i32, 1)))),
                       ID(fir_region_param(b, down, 1))};
  ID(fir_cf_br(b, to(top, downn, 2)));
  OK(fir_position_at_end(b, out));
  FirValue res = ID(fir_region_param(b, out, 0));
  ID(fir_cf_yield(b, &res, 1));
  OK(fir_blocks_end(b, blocks));
  OK(fir_position_at_end(b, fir_builder_entry(b)));
  FirValue nsteps = result(b, blocks, 0);
  ID(fir_func_ret(b, &nsteps, 1));
  OK(fir_func_end(b));

  /* @e2e_run(%k: i32) -> (i32, i32, i64): record k; fill a stack array with prices times k
   * (checked: overflow raises 1, which nothing catches); sum it as a slice in a cf.try (an
   * overflow there is caught: the total is minus the code); classify the total; swap a pair;
   * and count the Collatz steps of k through a function pointer. */
  b = fir_func_begin(m, run);
  OK(fir_set_file(b, "e2e.c"));
  FirValue k = ID(fir_builder_param(b, 0));
  OK(fir_value_set_name(b, k, "k"));
  FirValue k64 = ID(fir_int_sext(b, i64, k));
  ID(fir_func_call(b, record, &k64, 1));
  FirValue mem = ID(fir_mem_stack_of(b, arr, 4));
  FirValue four = ID(fir_int_const(b, i64, 4));
  s = ID(fir_slice_make(b, mem, four));
  FirValue g = ID(fir_mem_global(b, prices));
  FirValue z64 = ID(fir_int_const(b, i64, 0));
  loop = ID(fir_cf_loop_begin(b, NULL, 0, true, &z64, 1));
  body = ID(fir_op_region(b, loop, 0));
  i = ID(fir_region_param(b, body, 0));
  OK(fir_position_at_end(b, body));
  done = ID(fir_cf_if_begin(b, NULL, 0, ID(fir_int_cmp(b, FIR_PRED_UGE, i, four))));
  OK(fir_position_at_end(b, ID(fir_op_region(b, done, 0))));
  ID(fir_cf_break(b, NULL, 0));
  OK(fir_position_at_end(b, ID(fir_op_region(b, done, 1))));
  ID(fir_cf_yield(b, NULL, 0));
  OK(fir_position_at_end(b, body));
  FirValue price = ID(fir_mem_load(b, i32, ID(fir_ptr_index(b, true, i32, g, i)), 4));
  FirOp mul = ID(fir_int_overflow(b, FIR_ARITH_OP_MUL, true, price, k));
  over = ID(fir_cf_if_begin(b, NULL, 0, result(b, mul, 1)));
  OK(fir_position_at_end(b, ID(fir_op_region(b, over, 0))));
  FirValue c1 = ID(fir_int_const(b, i32, 1));
  ID(fir_func_call(b, raise, &c1, 1));
  ID(fir_cf_yield(b, NULL, 0));
  OK(fir_position_at_end(b, ID(fir_op_region(b, over, 1))));
  ID(fir_cf_yield(b, NULL, 0));
  OK(fir_position_at_end(b, body));
  ID(fir_slice_set(b, true, i32, result(b, mul, 0), s, i, 4));
  FirValue inext = ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_WRAP, i,
                                    ID(fir_int_const(b, i64, 1))));
  ID(fir_cf_continue(b, &inext, 1));
  OK(fir_position_at_end(b, fir_builder_entry(b)));
  FirOp tryop = ID(fir_cf_try_begin(b, &i32, 1));
  OK(fir_position_at_end(b, ID(fir_op_region(b, tryop, 0))));
  FirValue t = result(b, ID(fir_func_call(b, sum, &s, 1)), 0);
  ID(fir_cf_yield(b, &t, 1));
  FirRegion handler = ID(fir_op_region(b, tryop, 1));
  FirValue e = ID(fir_region_param(b, handler, 0));
  OK(fir_value_set_name(b, e, "e"));
  OK(fir_position_at_end(b, handler));
  FirValue ecode = ID(fir_mem_load(b, i32, e, 8));
  ID(fir_mem_free(b, "c.malloc", e));
  FirValue minus = ID(fir_int_arith(b, FIR_ARITH_OP_SUB, FIR_OVF_WRAP,
                                    ID(fir_int_const(b, i32, 0)), ecode));
  ID(fir_cf_yield(b, &minus, 1));
  OK(fir_position_at_end(b, fir_builder_entry(b)));
  total = result(b, tryop, 0);
  uv = result(b, ID(fir_func_call(b, classify, &total, 1)), 0);
  FirValue is1 = ID(fir_int_cmp(b, FIR_PRED_EQ, ID(fir_union_tag(b, uv)),
                                ID(fir_int_const(b, i32, 1))));
  FirOp get = ID(fir_cf_if_begin(b, &i64, 1, is1));
  OK(fir_position_at_end(b, ID(fir_op_region(b, get, 0))));
  FirValue w1 = ID(fir_union_get(b, i64, true, uv, 1));
  ID(fir_cf_yield(b, &w1, 1));
  OK(fir_position_at_end(b, ID(fir_op_region(b, get, 1))));
  FirValue w0 = ID(fir_int_sext(b, i64, ID(fir_union_get(b, i32, true, uv, 0))));
  ID(fir_cf_yield(b, &w0, 1));
  OK(fir_position_at_end(b, fir_builder_entry(b)));
  FirValue v64 = result(b, get, 0);
  FirValue parts[2] = {total, k};
  FirValue pt = ID(fir_agg_make(b, pair, parts, 2));
  FirValue swapped = result(b, ID(fir_func_call(b, swap, &pt, 1)), 0);
  FirValue first = ID(fir_agg_extract(b, i32, swapped, 0));
  FirValue fp = ID(fir_func_addr(b, steps));
  FirValue st = result(b, ID(fir_func_call_indirect(b, step_sig, fp, &first, 1)), 0);
  FirValue rets[3] = {total, st, v64};
  ID(fir_func_ret(b, rets, 3));
  OK(fir_func_end(b));

  /* @e2e_pick(%i: i64) -> i32: element i of @prices as a slice (a bounds trap past 3). */
  b = fir_func_begin(m, pick);
  i = ID(fir_builder_param(b, 0));
  s = ID(fir_slice_make(b, ID(fir_mem_global(b, prices)), ID(fir_int_const(b, i64, 4))));
  OK(fir_set_loc(b, 50, 7));
  x = ID(fir_slice_get(b, i32, true, s, i, 4));
  ID(fir_func_ret(b, &x, 1));
  OK(fir_func_end(b));

  return m;
}

/* The runs: the entry, its argument, and the C types of its results for the native main. */

struct Run {
  const char *func;
  const char *arg;
  int nrets;
};

static const struct Run runs[] = {
    {"e2e_run", "2", 3},         {"e2e_run", "-3", 3},  {"e2e_run", "7", 3},
    {"e2e_run", "100000000", 3}, {"e2e_run", "1000000000", 3},
    {"e2e_pick", "2", 1},        {"e2e_pick", "4", 1},
};
#define NRUNS (sizeof runs / sizeof runs[0])

static char *run_line(FirModule *m, const struct Run *r) {
  char *out = NULL;
  const char *args[1] = {r->arg};
  FirStatus s = fir_module_run(m, r->func, args, 1, FIR_DEFAULT_FUEL, &out);
  if (s != FIR_OK) {
    fprintf(stderr, "run @%s(%s) failed (%u): %s\n", r->func, r->arg, s, fir_module_error(m));
    failures++;
    return NULL;
  }
  return out;
}

/* fir run's line as the native program can print it: leak notes dropped, and an allocation's
 * pointer (`#3`, `#3+8`) as `?`. */
static void normalize(const char *in, char *out, size_t cap) {
  size_t o = 0;
  const char *p = in;
  while (*p && o + 1 < cap) {
    if (strncmp(p, "; leak:", 7) == 0) {
      const char *next = strstr(p + 2, "; ");
      if (next == NULL) break;
      p = next;
      continue;
    }
    if (*p == '#' && isdigit((unsigned char)p[1])) {
      out[o++] = '?';
      p++;
      while (isdigit((unsigned char)*p) || *p == '+') p++;
      continue;
    }
    out[o++] = *p++;
  }
  out[o] = '\0';
}

/* The native side: the runtime (traps, the exception slot, the external function) and a main
 * that performs run argv[1] and prints its outcome as fir run does. */
static const char *native_main =
    "#include <stdint.h>\n"
    "#include <stdio.h>\n"
    "#include <stdlib.h>\n"
    "struct fir_exn { void *flag; void *value; } __fir_exn;\n"
    "static const char *reasons[] = {\"div0\", \"overflow\", \"shift\", \"oom\", \"bounds\", "
    "\"tag\"};\n"
    "void __fir_trap(uint32_t r, uint32_t line, uint32_t col) {\n"
    "  printf(\"trap %s\", r < 6 ? reasons[r] : \"?\");\n"
    "  if (line != 0xffffffffu) printf(\" @%u:%u\", line, col);\n"
    "  printf(\"\\n\");\n"
    "  exit(0);\n"
    "}\n"
    "uint64_t record(uint64_t a) {\n"
    "  printf(\"@record(i64 %lld) -> i32 0; \", (long long)a);\n"
    "  return 0;\n"
    "}\n"
    "struct r3 { uint64_t r[3]; };\n"
    "struct r3 e2e_run(uint64_t k);\n"
    "uint64_t e2e_pick(uint64_t i);\n"
    "static int threw(void) {\n"
    "  if (!__fir_exn.flag) return 0;\n"
    "  printf(__fir_exn.value ? \"threw ptr ?\" : \"threw ptr null\");\n"
    "  return 1;\n"
    "}\n"
    "int main(int argc, char **argv) {\n"
    "  if (argc < 3) return 2;\n"
    "  long long a = atoll(argv[2]);\n"
    "  if (argv[1][4] == 'r') {\n"
    "    struct r3 r = e2e_run((uint64_t)a);\n"
    "    if (!threw())\n"
    "      printf(\"returned i32 %d, i32 %d, i64 %lld\", (int32_t)r.r[0], (int32_t)r.r[1],\n"
    "             (long long)r.r[2]);\n"
    "  } else {\n"
    "    uint64_t r = e2e_pick((uint64_t)a);\n"
    "    if (!threw()) printf(\"returned i32 %d\", (int32_t)r);\n"
    "  }\n"
    "  printf(\"\\n\");\n"
    "  return 0;\n"
    "}\n";

static int write_file(const char *path, const char *text) {
  FILE *f = fopen(path, "w");
  if (f == NULL) return 0;
  fputs(text, f);
  return fclose(f) == 0;
}

/* Build `dir/name` from the assembly and the main. */
static int link_native(const char *cc, const char *dir, const char *name, const char *asm_text) {
  char s[1024], c[1024], bin[1024], cmd[4096];
  snprintf(s, sizeof s, "%s/%s.s", dir, name);
  snprintf(c, sizeof c, "%s/%s_main.c", dir, name);
  snprintf(bin, sizeof bin, "%s/%s", dir, name);
  if (!write_file(s, asm_text) || !write_file(c, native_main)) return 0;
  snprintf(cmd, sizeof cmd, "\"%s\" -O0 -w \"%s\" \"%s\" -o \"%s\"", cc, c, s, bin);
  return system(cmd) == 0;
}

/* Run `dir/name func arg` and give its line. */
static void run_native(const char *runner, const char *dir, const char *name,
                       const struct Run *r, char *line, size_t cap) {
  char cmd[4096];
  snprintf(cmd, sizeof cmd, "%s%s\"%s/%s\" %s %s", runner, *runner ? " " : "", dir, name,
           r->func, r->arg);
  line[0] = '\0';
  FILE *p = popen(cmd, "r");
  if (p == NULL) return;
  if (fgets(line, (int)cap, p) == NULL) line[0] = '\0';
  pclose(p);
  line[strcspn(line, "\n")] = '\0';
}

int main(void) {
  FirModule *m = build();
  OK(fir_module_verify(m));
  if (failures > 0) return 1;
  printf("e2e: built through the C API and verified\n");

  /* The interpreter's lines are the expected outcomes. */
  char *want[NRUNS];
  for (size_t r = 0; r < NRUNS; r++) {
    want[r] = run_line(m, &runs[r]);
    printf("fir run @%s(%s): %s\n", runs[r].func, runs[r].arg, want[r] ? want[r] : "?");
  }

  /* Lowered to MFIR, and optimized: the same lines. */
  FirModule *l = NULL, *o = NULL;
  OK(fir_module_lower(m, &l));
  if (l != NULL) OK(fir_module_optimize(l, &o));
  int agree = 0;
  for (size_t r = 0; r < NRUNS && l != NULL && o != NULL; r++) {
    char *a = run_line(l, &runs[r]), *b = run_line(o, &runs[r]);
    if (a && b && want[r] && strcmp(a, want[r]) == 0 && strcmp(b, want[r]) == 0) {
      agree++;
    } else {
      fprintf(stderr, "@%s(%s): lowered '%s', optimized '%s', want '%s'\n", runs[r].func,
              runs[r].arg, a ? a : "?", b ? b : "?", want[r] ? want[r] : "?");
      failures++;
    }
    fir_string_free(a);
    fir_string_free(b);
  }
  printf("lowered and optimized: %d of %zu runs agree\n", agree, NRUNS);
  if (l) fir_module_free(l);
  if (o) fir_module_free(o);

  /* AArch64, with and without -O. */
  char *as[2] = {NULL, NULL};
  for (int opt = 0; opt < 2; opt++) {
    OK(fir_module_compile(m, "aarch64", opt == 1, FIR_OS_LINUX, &as[opt]));
    CHECK(as[opt] != NULL && strstr(as[opt], "__fir_exn") != NULL);
  }
  const char *cc = getenv("FIR_E2E_CC"), *runner = getenv("FIR_E2E_RUN"),
             *dir = getenv("FIR_E2E_DIR");
  if (cc == NULL || *cc == '\0' || dir == NULL) {
    printf("native: skipped (no AArch64 toolchain: FIR_E2E_CC is not set)\n");
  } else {
    if (runner == NULL) runner = "";
    int matched = 0, total = 0;
    const char *names[2] = {"e2e", "e2e-O"};
    for (int opt = 0; opt < 2; opt++) {
      if (as[opt] == NULL || !link_native(cc, dir, names[opt], as[opt])) {
        fprintf(stderr, "building %s/%s failed\n", dir, names[opt]);
        failures++;
        continue;
      }
      for (size_t r = 0; r < NRUNS; r++) {
        char got[4096], norm[4096];
        run_native(runner, dir, names[opt], &runs[r], got, sizeof got);
        normalize(want[r] ? want[r] : "", norm, sizeof norm);
        total++;
        if (strcmp(got, norm) == 0) {
          matched++;
        } else {
          fprintf(stderr, "%s @%s(%s): native '%s', want '%s'\n", names[opt], runs[r].func,
                  runs[r].arg, got, norm);
          failures++;
        }
        printf("native%s @%s(%s): %s\n", opt ? " -O" : "", runs[r].func, runs[r].arg, got);
      }
    }
    printf("native: %d of %d runs match fir run\n", matched, total);
  }
  for (int opt = 0; opt < 2; opt++) fir_string_free(as[opt]);
  for (size_t r = 0; r < NRUNS; r++) fir_string_free(want[r]);
  fir_module_free(m);
  if (failures > 0) {
    fprintf(stderr, "%d checks failed\n", failures);
    return 1;
  }
  puts("ok");
  return 0;
}
