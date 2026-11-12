/* The round's end-to-end test: a program built through the C API only, using every HFIR
 * building block (aggregate values, checked arithmetic, a tagged union, slices, exceptions)
 * with loops and cf.blocks, stack and heap memory, a global, an external call, and an indirect
 * call. It is verified and run in the interpreter (fir_module_run), which gives the expected
 * outcome lines; lowered and optimized, which must give them again; and compiled to AArch64
 * assembly (fir_module_compile, with and without -O), which is assembled and linked with a
 * generated main that prints each run's outcome in fir run's format, run (under qemu-aarch64
 * off AArch64), and compared.
 *
 * A second module, also built through the C API, checks floats across the C boundary: C calls
 * FIR float functions (arguments in registers and on the stack, a homogeneous float result pair
 * in d0/d1, a mixed pair in x0/x1, an f64 global initialized with 0.5), FIR calls libm's sqrt
 * and fabsf and a C function taking ten doubles, and an assembly helper checks that a FIR call
 * leaves d8-d15 as it found them. The native program compares every result with what C computes
 * itself, bit for bit, and the interpreter's run of the mixed function with C's too.
 *
 * A third module checks variadic functions across the C boundary (decision: Varargs): FIR calls
 * glibc's printf (directly and through a pointer) and snprintf with integers, pointers, and
 * doubles past the argument registers, and vprintf with a va_list it starts and copies itself;
 * C calls a variadic FIR function that forwards its arguments to vprintf, and one that sums
 * twelve ints and twelve doubles (beyond eight of each class) with va.arg. The native output must
 * be exactly what the host's snprintf makes of the same formats and arguments.
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

/* Floats across the C boundary. */
static FirModule *build_floats(void) {
  FirModule *m = cur = fir_module_new();
  FirType f32 = FIR_TYPE_F32, f64 = FIR_TYPE_F64, i32 = fir_type_int(32), i64 = fir_type_int(64);
  FirGlobal factor =
      ID(fir_global_declare(m, "factor", f64, true, 8, ID(fir_init_f64(m, 0.5))));
  FirFunc sqrt_ = ID(fir_extern_declare(m, "sqrt", &f64, 1, &f64, 1, NULL, 0, FIR_TRUST_ASSUME));
  FirFunc fabsf_ =
      ID(fir_extern_declare(m, "fabsf", &f32, 1, &f32, 1, NULL, 0, FIR_TRUST_ASSUME));
  FirType ten[10];
  for (int k = 0; k < 10; k++) ten[k] = f64;
  FirFunc sum10 =
      ID(fir_extern_declare(m, "sum10", ten, 10, &f64, 1, NULL, 0, FIR_TRUST_ASSUME));
  FirType norm_ps[3] = {f64, f64, f32};
  FirFunc norm = ID(fir_func_declare(m, "fnorm", norm_ps, 3, &f64, 1));
  FirType two[2] = {f64, f64};
  FirFunc spill = ID(fir_func_declare(m, "fspill", ten, 10, two, 2));
  FirType mixed_ps[4] = {i32, f32, i64, f64}, mixed_rets[2] = {i64, f64};
  FirFunc mixed = ID(fir_func_declare(m, "fmixed", mixed_ps, 4, mixed_rets, 2));

  /* @fnorm(%x, %y, %s) = sqrt(fma(y, y, x * x)) * fabsf(s) * @factor: the root lives across
   * the call to fabsf, in a callee-saved register. */
  FirBuilder *b = fir_func_begin(m, norm);
  FirValue x = ID(fir_builder_param(b, 0)), y = ID(fir_builder_param(b, 1)),
           sg = ID(fir_builder_param(b, 2));
  FirValue xx = ID(fir_float_bin(b, FIR_FBIN_OP_MUL, x, x));
  FirValue h = ID(fir_float_fma(b, y, y, xx));
  FirValue r = result(b, ID(fir_func_call(b, sqrt_, &h, 1)), 0);
  FirValue a = result(b, ID(fir_func_call(b, fabsf_, &sg, 1)), 0);
  FirValue e = ID(fir_float_ext(b, f64, a));
  FirValue f = ID(fir_mem_load(b, f64, ID(fir_mem_global(b, factor)), 8));
  FirValue out = ID(fir_float_bin(b, FIR_FBIN_OP_MUL, ID(fir_float_bin(b, FIR_FBIN_OP_MUL, r, e)), f));
  ID(fir_func_ret(b, &out, 1));
  OK(fir_func_end(b));

  /* @fspill(%a0 … %a9) = (sum10(a9, …, a0), a0 - a9): the last two arguments, both ways, are
   * on the stack. */
  b = fir_func_begin(m, spill);
  FirValue ps[10], rev[10];
  for (int k = 0; k < 10; k++) ps[k] = ID(fir_builder_param(b, (uint32_t)k));
  for (int k = 0; k < 10; k++) rev[k] = ps[9 - k];
  FirValue sum = result(b, ID(fir_func_call(b, sum10, rev, 10)), 0);
  FirValue outs[2] = {sum, ID(fir_float_bin(b, FIR_FBIN_OP_SUB, ps[0], ps[9]))};
  ID(fir_func_ret(b, outs, 2));
  OK(fir_func_end(b));

  /* @fmixed(%n, %x, %m, %y) = (m + to_int.s.sat(x) * n, y * n). */
  b = fir_func_begin(m, mixed);
  FirValue n = ID(fir_builder_param(b, 0)), fx = ID(fir_builder_param(b, 1)),
           mm = ID(fir_builder_param(b, 2)), fy = ID(fir_builder_param(b, 3));
  FirValue t = ID(fir_float_to_int(b, i64, true, FIR_CVT_EDGE_SAT, fx));
  FirValue k = ID(fir_int_sext(b, i64, n));
  FirValue p = ID(fir_int_arith(b, FIR_ARITH_OP_MUL, FIR_OVF_WRAP, t, k));
  FirValue mo[2] = {ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_WRAP, mm, p)),
                    ID(fir_float_bin(b, FIR_FBIN_OP_MUL, fy, ID(fir_int_to_float(b, f64, true, n))))};
  ID(fir_func_ret(b, mo, 2));
  OK(fir_func_end(b));
  return m;
}

/* The float module's native side: C calls the FIR functions and compares each result with its
 * own computation, bit for bit, printing one line per check. */
static const char *float_main =
    "#include <math.h>\n"
    "#include <stdint.h>\n"
    "#include <stdio.h>\n"
    "#include <string.h>\n"
    "void __fir_trap(uint32_t r, uint32_t line, uint32_t col) {\n"
    "  printf(\"trap %u @%u:%u\\n\", r, line, col);\n"
    "}\n"
    "double fnorm(double x, double y, float s);\n"
    "struct dd { double a, b; };\n"
    "struct dd fspill(double, double, double, double, double, double, double, double, double,\n"
    "                 double);\n"
    "struct id { int64_t a; double b; };\n"
    "struct id fmixed(int32_t n, float x, int64_t m, double y);\n"
    "/* Weighted, so the order of the arguments matters. */\n"
    "double sum10(double a, double b, double c, double d, double e, double f, double g,\n"
    "             double h, double i, double j) {\n"
    "  return a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f + 7 * g + 8 * h + 9 * i + 10 * j;\n"
    "}\n"
    "/* Set d8-d15, call fnorm, and give whether they survived (their sum is 36). */\n"
    "int check_saved(void);\n"
    "__asm__(\".text\\n.globl check_saved\\n.p2align 2\\ncheck_saved:\\n\"\n"
    "        \"stp x29, x30, [sp, #-80]!\\nmov x29, sp\\n\"\n"
    "        \"stp d8, d9, [sp, #16]\\nstp d10, d11, [sp, #32]\\n\"\n"
    "        \"stp d12, d13, [sp, #48]\\nstp d14, d15, [sp, #64]\\n\"\n"
    "        \"fmov d8, #1.0\\nfmov d9, #2.0\\nfmov d10, #3.0\\nfmov d11, #4.0\\n\"\n"
    "        \"fmov d12, #5.0\\nfmov d13, #6.0\\nfmov d14, #7.0\\nfmov d15, #8.0\\n\"\n"
    "        \"fmov d0, #3.0\\nfmov d1, #4.0\\nfmov s2, #-2.0\\nbl fnorm\\n\"\n"
    "        \"fadd d16, d8, d9\\nfadd d16, d16, d10\\nfadd d16, d16, d11\\n\"\n"
    "        \"fadd d16, d16, d12\\nfadd d16, d16, d13\\nfadd d16, d16, d14\\n\"\n"
    "        \"fadd d16, d16, d15\\nmov x0, #36\\nscvtf d17, x0\\nfcmp d16, d17\\n\"\n"
    "        \"cset w0, eq\\n\"\n"
    "        \"ldp d8, d9, [sp, #16]\\nldp d10, d11, [sp, #32]\\n\"\n"
    "        \"ldp d12, d13, [sp, #48]\\nldp d14, d15, [sp, #64]\\n\"\n"
    "        \"ldp x29, x30, [sp], #80\\nret\\n\");\n"
    "static uint64_t bits(double x) { uint64_t b; memcpy(&b, &x, 8); return b; }\n"
    "static void check(const char *what, double got, double want) {\n"
    "  if (bits(got) == bits(want)) printf(\"%s ok\\n\", what);\n"
    "  else printf(\"%s: got %a, want %a\\n\", what, got, want);\n"
    "}\n"
    "int main(void) {\n"
    "  volatile double x = 3.0, y = 4.0;\n"
    "  volatile float s = -2.0f;\n"
    "  check(\"fnorm\", fnorm(x, y, s), sqrt(fma(y, y, x * x)) * (double)fabsf(s) * 0.5);\n"
    "  check(\"fnorm of tiny\", fnorm(1e-200, 3e-200, 0.75f),\n"
    "        sqrt(fma(3e-200, 3e-200, 1e-200 * 1e-200)) * 0.75 * 0.5);\n"
    "  struct dd d = fspill(0.5, 1.5, 2.5, 3.5, 4.5, 5.5, 6.5, 7.5, 8.5, 9.75);\n"
    "  check(\"fspill sum\", d.a, sum10(9.75, 8.5, 7.5, 6.5, 5.5, 4.5, 3.5, 2.5, 1.5, 0.5));\n"
    "  check(\"fspill difference\", d.b, 0.5 - 9.75);\n"
    "  struct id e = fmixed(3, 2.5f, 10, 1.5);\n"
    "  check(\"fmixed integer\", (double)e.a, 16.0);\n"
    "  check(\"fmixed float\", e.b, 4.5);\n"
    "  printf(check_saved() ? \"d8-d15 ok\\n\" : \"d8-d15 clobbered\\n\");\n"
    "  return 0;\n"
    "}\n";

/* Variadic functions across the C boundary. */

static const char *va_fmt1 = "printf: %d %s %.3f %ld %c|";
static const char *va_fmt2 = "%d-%d-%d-%d-%d-%d-%d-%d-%d-%.1f-%.1f";
static const char *va_fmt3 = "snprintf: %s|";
static const char *va_fmt4 = "indirect: %d %.2f\n";
static const char *va_word = "words";

/* `global const @name: array<n x i8>` holding the string `s` and its terminating zero. */
static FirGlobal string_global(FirModule *m, const char *name, const char *s) {
  size_t n = strlen(s) + 1;
  FirType arr = ID(fir_type_array(m, n, fir_type_int(8)));
  return ID(fir_global_declare(m, name, arr, true, 1,
                               ID(fir_init_bytes(m, (const uint8_t *)s, n))));
}

static FirModule *build_varargs(void) {
  FirModule *m = cur = fir_module_new();
  OK(fir_module_set_va_list(m, 32, 8));
  FirType i8 = fir_type_int(8), i32 = fir_type_int(32), i64 = fir_type_int(64),
          f64 = FIR_TYPE_F64, ptr = FIR_TYPE_PTR, va = FIR_TYPE_VA_LIST;
  FirEffect all[8] = {FIR_EFFECT_READ_ARGS,     FIR_EFFECT_READ_EXPOSED, FIR_EFFECT_WRITE_ARGS,
                      FIR_EFFECT_WRITE_EXPOSED, FIR_EFFECT_ALLOC,        FIR_EFFECT_FREE,
                      FIR_EFFECT_TRAP,          FIR_EFFECT_DIVERGE};
  FirFunc printf_ =
      ID(fir_extern_declare_va(m, "printf", &ptr, 1, &i32, 1, true, all, 8, FIR_TRUST_ASSUME));
  FirType sn_ps[3] = {ptr, i64, ptr};
  FirFunc snprintf_ =
      ID(fir_extern_declare_va(m, "snprintf", sn_ps, 3, &i32, 1, true, all, 8, FIR_TRUST_ASSUME));
  FirType vp_ps[2] = {ptr, ptr};
  FirFunc vprintf_ =
      ID(fir_extern_declare_va(m, "vprintf", vp_ps, 2, &i32, 1, false, all, 8, FIR_TRUST_ASSUME));
  FirGlobal g1 = string_global(m, "fmt1", va_fmt1), g2 = string_global(m, "fmt2", va_fmt2),
            g3 = string_global(m, "fmt3", va_fmt3), g4 = string_global(m, "fmt4", va_fmt4),
            gw = string_global(m, "word", va_word);
  FirFunc show = ID(fir_func_declare_va(m, "va_show", NULL, 0, &i32, 1, false));
  FirFunc forward = ID(fir_func_declare_va(m, "vforward", &ptr, 1, &i32, 1, true));
  FirFunc vsum = ID(fir_func_declare_va(m, "vsum", &i32, 1, &f64, 1, true));
  FirType printf_sig = ID(fir_type_func_va(m, &ptr, 1, &i32, 1, true));

  /* @va_show() -> i32: printf with an int, a string, a double, a long, and a char; snprintf with
   * nine ints (four on the stack) and two doubles into a buffer, then printf of the buffer; and
   * printf through a pointer. Gives snprintf's count. */
  FirBuilder *b = fir_func_begin(m, show);
  FirValue a1[6] = {ID(fir_mem_global(b, g1)), ID(fir_int_const(b, i32, -7)),
                    ID(fir_mem_global(b, gw)), ID(fir_float_const_f64(b, 2.5)),
                    ID(fir_int_const(b, i64, -1234567890123)), ID(fir_int_const(b, i8, 'Z'))};
  ID(fir_func_call(b, printf_, a1, 6));
  FirValue buf = ID(fir_mem_stack(b, 64, 1));
  FirValue a2[14];
  a2[0] = buf;
  a2[1] = ID(fir_int_const(b, i64, 64));
  a2[2] = ID(fir_mem_global(b, g2));
  for (int k = 1; k <= 9; k++) a2[2 + k] = ID(fir_int_const(b, i32, k));
  a2[12] = ID(fir_float_const_f64(b, 0.5));
  a2[13] = ID(fir_float_const_f64(b, 1.5));
  FirValue n = result(b, ID(fir_func_call(b, snprintf_, a2, 14)), 0);
  FirValue a3[2] = {ID(fir_mem_global(b, g3)), buf};
  ID(fir_func_call(b, printf_, a3, 2));
  FirValue p = ID(fir_func_addr(b, printf_));
  FirValue a4[3] = {ID(fir_mem_global(b, g4)), ID(fir_int_const(b, i32, 42)),
                    ID(fir_float_const_f64(b, 0.25))};
  ID(fir_func_call_indirect(b, printf_sig, p, a4, 3));
  ID(fir_func_ret(b, &n, 1));
  OK(fir_func_end(b));

  /* @vforward(%fmt: ptr, ...) -> i32: vprintf of its variadic arguments, twice: once through
   * the va_list it starts, once through a copy (C's va_copy is a copy of the bytes). */
  b = fir_func_begin(m, forward);
  FirValue fmt = ID(fir_builder_param(b, 0));
  FirValue ap = ID(fir_mem_stack_of(b, va, 8)), aq = ID(fir_mem_stack_of(b, va, 8));
  ID(fir_va_start(b, ap));
  ID(fir_mem_copy(b, va, aq, ap, 8));
  FirValue v1[2] = {fmt, ap}, v2[2] = {fmt, aq};
  FirValue r1 = result(b, ID(fir_func_call(b, vprintf_, v1, 2)), 0);
  FirValue r2 = result(b, ID(fir_func_call(b, vprintf_, v2, 2)), 0);
  ID(fir_va_end(b, aq));
  ID(fir_va_end(b, ap));
  FirValue rs = ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_WRAP, r1, r2));
  ID(fir_func_ret(b, &rs, 1));
  OK(fir_func_end(b));

  /* @vsum(%n: i32, ...) -> f64: n pairs of an int and a double, acc = 2 acc + int + double. */
  b = fir_func_begin(m, vsum);
  FirValue count = ID(fir_builder_param(b, 0));
  FirValue list = ID(fir_mem_stack_of(b, va, 8));
  ID(fir_va_start(b, list));
  FirValue inits[2] = {ID(fir_int_const(b, i32, 0)), ID(fir_float_const_f64(b, 0.0))};
  FirOp loop = ID(fir_cf_loop_begin(b, &f64, 1, false, inits, 2));
  FirRegion body = ID(fir_op_region(b, loop, 0));
  FirValue i = ID(fir_region_param(b, body, 0)), acc = ID(fir_region_param(b, body, 1));
  OK(fir_position_at_end(b, body));
  FirOp done = ID(fir_cf_if_begin(b, NULL, 0, ID(fir_int_cmp(b, FIR_PRED_SGE, i, count))));
  OK(fir_position_at_end(b, ID(fir_op_region(b, done, 0))));
  ID(fir_cf_break(b, &acc, 1));
  OK(fir_position_at_end(b, body));
  FirValue x = ID(fir_va_arg(b, i32, list)), y = ID(fir_va_arg(b, f64, list));
  FirValue twice = ID(fir_float_bin(b, FIR_FBIN_OP_ADD, acc, acc));
  FirValue fx = ID(fir_int_to_float(b, f64, true, x));
  FirValue plus = ID(fir_float_bin(b, FIR_FBIN_OP_ADD, twice, fx));
  FirValue next[2] = {ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_WRAP, i,
                                       ID(fir_int_const(b, i32, 1)))),
                      ID(fir_float_bin(b, FIR_FBIN_OP_ADD, plus, y))};
  ID(fir_cf_continue(b, next, 2));
  OK(fir_position_at_end(b, ID(fir_builder_entry(b))));
  FirValue total = result(b, loop, 0);
  ID(fir_va_end(b, list));
  ID(fir_func_ret(b, &total, 1));
  OK(fir_func_end(b));
  return m;
}

/* The varargs module's native side: C calls the FIR functions, the output must match the host's
 * snprintf of the same formats (`va_expected`). */
static const char *va_main =
    "#include <stdio.h>\n"
    "#include <stdint.h>\n"
    "void __fir_trap(uint32_t r, uint32_t line, uint32_t col) {\n"
    "  printf(\"trap %u @%u:%u\\n\", r, line, col);\n"
    "}\n"
    "int va_show(void);\n"
    "int vforward(const char *fmt, ...);\n"
    "double vsum(int n, ...);\n"
    "int main(void) {\n"
    "  int n = va_show();\n"
    "  printf(\"va_show %d\\n\", n);\n"
    "  int k = vforward(\"vforward: %d %s %.2f %ld %d %d %d %d %d %d %.1f|\\n\", 1, \"two\",\n"
    "                   3.5, 4L, 5, 6, 7, 8, 9, 10, -0.5);\n"
    "  printf(\"vforward %d\\n\", k);\n"
    "  double s = vsum(12, 1, 0.5, 2, 1.5, 3, 2.5, 4, 3.5, 5, 4.5, 6, 5.5, 7, 6.5, 8, 7.5, 9,\n"
    "                  8.5, 10, 9.5, 11, 10.5, -12, 11.5);\n"
    "  double want = 0;\n"
    "  for (int i = 1; i <= 12; i++) want = 2 * want + (i == 12 ? -12 : i) + (i - 0.5);\n"
    "  printf(s == want ? \"vsum ok\\n\" : \"vsum: got %a, want %a\\n\", s, want);\n"
    "  return 0;\n"
    "}\n";

/* What va_main must print, from the host's snprintf. */
static void va_expected(char *out, size_t cap) {
  char buf[64], line[256];
  size_t len = 0;
  snprintf(line, sizeof line, va_fmt1, -7, va_word, 2.5, -1234567890123L, 'Z');
  len += (size_t)snprintf(out + len, cap - len, "%s", line);
  int n = snprintf(buf, sizeof buf, va_fmt2, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0.5, 1.5);
  len += (size_t)snprintf(out + len, cap - len, va_fmt3, buf);
  len += (size_t)snprintf(out + len, cap - len, va_fmt4, 42, 0.25);
  len += (size_t)snprintf(out + len, cap - len, "va_show %d\n", n);
  int k = 0;
  for (int t = 0; t < 2; t++) {
    int w = snprintf(line, sizeof line, "vforward: %d %s %.2f %ld %d %d %d %d %d %d %.1f|\n", 1,
                     "two", 3.5, 4L, 5, 6, 7, 8, 9, 10, -0.5);
    len += (size_t)snprintf(out + len, cap - len, "%s", line);
    k += w;
  }
  len += (size_t)snprintf(out + len, cap - len, "vforward %d\nvsum ok\n", k);
}

/* Structs and arrays by value across the C boundary (decision: C ABI for aggregates): every
 * AAPCS64 class as an argument and a result of FIR functions C calls and of C functions FIR
 * calls, directly and through `...`. */
static FirModule *build_structs(void) {
  FirModule *m = cur = fir_module_new();
  FirType i16 = fir_type_int(16), i32 = fir_type_int(32), i64 = fir_type_int(64),
          f32 = FIR_TYPE_F32, f64 = FIR_TYPE_F64, ptr = FIR_TYPE_PTR;
  FirType pf[2] = {i32, f32};
  FirType pair = ID(fir_type_struct(m, FIR_POLICY_C, pf, 2)); /* 8 bytes: x0 */
  FirType hf[3] = {f64, f64, f64};
  FirType hfa = ID(fir_type_struct(m, FIR_POLICY_C, hf, 3)); /* HFA: d0-d2 */
  FirType shorts = ID(fir_type_array(m, 4, i16));
  FirType bf[3] = {i64, ptr, shorts};
  FirType big = ID(fir_type_struct(m, FIR_POLICY_C, bf, 3)); /* 24 bytes: by reference */
  FirType two = ID(fir_type_array(m, 2, f32));               /* HFA: s0, s1 */
  FirEffect rd[1] = {FIR_EFFECT_READ_ARGS};
  FirType cps[4] = {pair, hfa, big, two};
  FirFunc c_mix = ID(fir_extern_declare(m, "c_mix", cps, 4, &hfa, 1, rd, 1, FIR_TRUST_ASSUME));
  FirFunc c_va = ID(fir_extern_declare_va(m, "c_va", &i32, 1, &i64, 1, true, rd, 1,
                                          FIR_TRUST_ASSUME));
  FirType mps[5] = {pair, hfa, big, two, i32};
  FirFunc fir_mix = ID(fir_func_declare(m, "fir_mix", mps, 5, &big, 1));
  FirFunc fir_calls = ID(fir_func_declare(m, "fir_calls", &ptr, 1, &f64, 1));
  FirFunc fir_va = ID(fir_func_declare_va(m, "fir_va", &i32, 1, &pair, 1, true));

  /* @fir_mix(%p: pair, %h: hfa, %b: big, %t: two, %k: i32) -> big: {b.0 + p.0 + k, b.1,
   * [i16 of h.2, b.2[1], b.2[2], i16 of t.1 + load(b.1)]}: every class in, a large one out. */
  FirBuilder *b = fir_func_begin(m, fir_mix);
  FirValue p = ID(fir_builder_param(b, 0)), h = ID(fir_builder_param(b, 1)),
           bg = ID(fir_builder_param(b, 2)), t = ID(fir_builder_param(b, 3)),
           k = ID(fir_builder_param(b, 4));
  FirValue p0 = ID(fir_int_sext(b, i64, ID(fir_agg_extract(b, i32, p, 0))));
  FirValue b0 = ID(fir_agg_extract(b, i64, bg, 0)), b1 = ID(fir_agg_extract(b, ptr, bg, 1));
  FirValue b2 = ID(fir_agg_extract(b, shorts, bg, 2));
  FirValue s0 = ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_WRAP, b0, p0));
  s0 = ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_WRAP, s0, ID(fir_int_sext(b, i64, k))));
  FirValue h2 = ID(fir_agg_extract(b, f64, h, 2));
  FirValue e0 = ID(fir_float_to_int(b, i16, true, FIR_CVT_EDGE_SAT, h2));
  FirValue t1 = ID(fir_agg_extract(b, f32, t, 1));
  FirValue e3 = ID(fir_float_to_int(b, i16, true, FIR_CVT_EDGE_SAT, t1));
  e3 = ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_WRAP, e3, ID(fir_mem_load(b, i16, b1, 2))));
  FirValue es[4] = {e0, ID(fir_agg_extract(b, i16, b2, 1)), ID(fir_agg_extract(b, i16, b2, 2)),
                    e3};
  FirValue bs[3] = {s0, b1, ID(fir_agg_make(b, shorts, es, 4))};
  FirValue r = ID(fir_agg_make(b, big, bs, 3));
  ID(fir_func_ret(b, &r, 1));
  OK(fir_func_end(b));

  /* @fir_calls(%q: ptr) -> f64: c_mix of constants (the sum of the HFA it gives back), plus
   * c_va(3, ... pair, big, hfa) converted. */
  b = fir_func_begin(m, fir_calls);
  FirValue q = ID(fir_builder_param(b, 0));
  FirValue pv[2] = {ID(fir_int_const(b, i32, -40)), ID(fir_float_const_f32(b, 2.5f))};
  FirValue pr = ID(fir_agg_make(b, pair, pv, 2));
  FirValue hv[3] = {ID(fir_float_const_f64(b, 0.25)), ID(fir_float_const_f64(b, 1e10)),
                    ID(fir_float_const_f64(b, -3.0))};
  FirValue hh = ID(fir_agg_make(b, hfa, hv, 3));
  FirValue sv[4] = {ID(fir_int_const(b, i16, 1)), ID(fir_int_const(b, i16, -2)),
                    ID(fir_int_const(b, i16, 3)), ID(fir_int_const(b, i16, -4))};
  FirValue bv[3] = {ID(fir_int_const(b, i64, 1234567890123)), q, ID(fir_agg_make(b, shorts, sv, 4))};
  FirValue bb = ID(fir_agg_make(b, big, bv, 3));
  FirValue tv[2] = {ID(fir_float_const_f32(b, 0.5f)), ID(fir_float_const_f32(b, -8.0f))};
  FirValue tt = ID(fir_agg_make(b, two, tv, 2));
  FirValue ca[4] = {pr, hh, bb, tt};
  FirValue got = result(b, ID(fir_func_call(b, c_mix, ca, 4)), 0);
  FirValue g0 = ID(fir_agg_extract(b, f64, got, 0)), g1 = ID(fir_agg_extract(b, f64, got, 1)),
           g2 = ID(fir_agg_extract(b, f64, got, 2));
  FirValue sum = ID(fir_float_bin(b, FIR_FBIN_OP_ADD, g0, g1));
  sum = ID(fir_float_bin(b, FIR_FBIN_OP_ADD, sum, g2));
  FirValue va[4] = {ID(fir_int_const(b, i32, 3)), pr, bb, hh};
  FirValue n = result(b, ID(fir_func_call(b, c_va, va, 4)), 0);
  FirValue nf = ID(fir_int_to_float(b, f64, true, n));
  sum = ID(fir_float_bin(b, FIR_FBIN_OP_ADD, sum, nf));
  ID(fir_func_ret(b, &sum, 1));
  OK(fir_func_end(b));

  /* @fir_va(%n: i32, ...) -> pair: reads a pair, a big, and an HFA; gives {pair.0 + n + big.0
   * (as i32), pair.1 + hfa.1 (as f32)}. */
  b = fir_func_begin(m, fir_va);
  FirValue cnt = ID(fir_builder_param(b, 0));
  FirValue ap = ID(fir_mem_stack_of(b, FIR_TYPE_VA_LIST, 8));
  ID(fir_va_start(b, ap));
  FirValue vp = ID(fir_va_arg(b, pair, ap)), vb = ID(fir_va_arg(b, big, ap)),
           vh = ID(fir_va_arg(b, hfa, ap));
  ID(fir_va_end(b, ap));
  FirValue x = ID(fir_agg_extract(b, i32, vp, 0));
  x = ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_WRAP, x, cnt));
  FirValue big0 = ID(fir_int_trunc(b, i32, FIR_TRUNC_MODE_WRAP, ID(fir_agg_extract(b, i64, vb, 0))));
  x = ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_WRAP, x, big0));
  FirValue y = ID(fir_float_bin(b, FIR_FBIN_OP_ADD, ID(fir_float_ext(b, f64, ID(fir_agg_extract(b, f32, vp, 1)))),
                                ID(fir_agg_extract(b, f64, vh, 1))));
  FirValue xy[2] = {x, ID(fir_float_trunc(b, f32, y))};
  FirValue out = ID(fir_agg_make(b, pair, xy, 2));
  ID(fir_func_ret(b, &out, 1));
  OK(fir_func_end(b));
  return m;
}

/* The structs module's native side: C calls the FIR functions with constants, and defines the
 * C functions FIR calls; each check prints `ok` or what differs. */
static const char *struct_main =
    "#include <stdarg.h>\n"
    "#include <stdint.h>\n"
    "#include <stdio.h>\n"
    "void __fir_trap(uint32_t r, uint32_t line, uint32_t col) {\n"
    "  printf(\"trap %u @%u:%u\\n\", r, line, col);\n"
    "}\n"
    "struct pair { int32_t a; float b; };\n"
    "struct hfa { double a, b, c; };\n"
    "struct big { int64_t a; int16_t *p; int16_t s[4]; };\n"
    "struct two { float e[2]; };\n"
    "struct big fir_mix(struct pair, struct hfa, struct big, struct two, int32_t);\n"
    "double fir_calls(int16_t *);\n"
    "struct pair fir_va(int32_t, ...);\n"
    "static int bad = 0;\n"
    "static void check(int ok, const char *what) { printf(\"%s %s\\n\", what, ok ? \"ok\" : \"WRONG\"); bad |= !ok; }\n"
    "struct hfa c_mix(struct pair p, struct hfa h, struct big b, struct two t) {\n"
    "  check(p.a == -40 && p.b == 2.5f, \"c_mix pair\");\n"
    "  check(h.a == 0.25 && h.b == 1e10 && h.c == -3.0, \"c_mix hfa\");\n"
    "  check(b.a == 1234567890123 && b.p[0] == 77 && b.s[0] == 1 && b.s[1] == -2 && b.s[2] == 3 && b.s[3] == -4, \"c_mix big\");\n"
    "  check(t.e[0] == 0.5f && t.e[1] == -8.0f, \"c_mix array\");\n"
    "  b.a = 0; /* the callee's copy */\n"
    "  return (struct hfa){1.5, 2.5, -0.5};\n"
    "}\n"
    "int64_t c_va(int32_t n, ...) {\n"
    "  va_list ap;\n"
    "  va_start(ap, n);\n"
    "  struct pair p = va_arg(ap, struct pair);\n"
    "  struct big b = va_arg(ap, struct big);\n"
    "  struct hfa h = va_arg(ap, struct hfa);\n"
    "  va_end(ap);\n"
    "  check(n == 3 && p.a == -40 && p.b == 2.5f && b.a == 1234567890123 && b.s[3] == -4 && h.b == 1e10, \"c_va\");\n"
    "  return p.a + b.s[2] + (int64_t)h.c;\n"
    "}\n"
    "int main(void) {\n"
    "  int16_t cell[1] = {77};\n"
    "  struct big b = {5000000000, cell, {10, 20, 30, 40}};\n"
    "  struct big r = fir_mix((struct pair){7, 0.5f}, (struct hfa){1.0, 2.0, 300.75}, b, (struct two){{9.0f, 41.5f}}, -3);\n"
    "  check(r.a == 5000000004 && r.p == cell && r.s[0] == 300 && r.s[1] == 20 && r.s[2] == 30 && r.s[3] == 118, \"fir_mix\");\n"
    "  check(b.a == 5000000000, \"fir_mix leaves the caller's copy\");\n"
    "  double d = fir_calls(cell);\n"
    "  check(d == 3.5 + (-40 + 3 - 3), \"fir_calls\");\n"
    "  struct pair v = fir_va(5, (struct pair){100, 1.25f}, b, (struct hfa){0, 0.5, 0});\n"
    "  check(v.a == 100 + 5 + (int32_t)5000000000 && v.b == 1.75f, \"fir_va\");\n"
    "  return bad;\n"
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

  /* Floats across the C boundary. */
  FirModule *fm = build_floats();
  OK(fir_module_verify(fm));
  char *fout = NULL;
  const char *margs[4] = {"3", "2.5", "10", "1.5"};
  OK(fir_module_run(fm, "fmixed", margs, 4, FIR_DEFAULT_FUEL, &fout));
  CHECK(fout != NULL && strcmp(fout, "returned i64 16, f64 4.5") == 0);
  printf("fir run @fmixed(3, 2.5, 10, 1.5): %s\n", fout ? fout : "?");
  fir_string_free(fout);
  if (cc != NULL && *cc != '\0' && dir != NULL) {
    int checks = 0;
    for (int opt = 0; opt < 2; opt++) {
      char *fas = NULL;
      OK(fir_module_compile(fm, "aarch64", opt == 1, FIR_OS_LINUX, &fas));
      char s[1024], c[1024], bin[1024], cmd[4096];
      const char *name = opt ? "floats-O" : "floats";
      snprintf(s, sizeof s, "%s/%s.s", dir, name);
      snprintf(c, sizeof c, "%s/%s_main.c", dir, name);
      snprintf(bin, sizeof bin, "%s/%s", dir, name);
      if (fas == NULL || !write_file(s, fas) || !write_file(c, float_main)) {
        failures++;
        fir_string_free(fas);
        continue;
      }
      fir_string_free(fas);
      snprintf(cmd, sizeof cmd, "\"%s\" -O1 -w \"%s\" \"%s\" -o \"%s\" -lm", cc, c, s, bin);
      if (system(cmd) != 0) {
        fprintf(stderr, "building %s failed\n", bin);
        failures++;
        continue;
      }
      snprintf(cmd, sizeof cmd, "%s%s\"%s\"", runner ? runner : "", runner && *runner ? " " : "",
               bin);
      FILE *pipe = popen(cmd, "r");
      char line[1024];
      int lines = 0;
      while (pipe != NULL && fgets(line, sizeof line, pipe) != NULL) {
        line[strcspn(line, "\n")] = '\0';
        printf("native%s: %s\n", opt ? " -O" : "", line);
        lines++;
        size_t len = strlen(line);
        if (len >= 3 && strcmp(line + len - 3, " ok") == 0) {
          checks++;
        } else {
          fprintf(stderr, "%s: %s\n", name, line);
          failures++;
        }
      }
      if (pipe != NULL) pclose(pipe);
      CHECK(lines == 7);
    }
    printf("native floats: %d of 14 checks pass\n", checks);
  }
  fir_module_free(fm);

  /* Varargs across the C boundary. */
  FirModule *vm = build_varargs();
  OK(fir_module_verify(vm));
  char *vout = NULL;
  const char *vargs[7] = {"3", "i32 1", "f64 0.5", "i32 2", "f64 1.5", "i32 3", "f64 2.5"};
  OK(fir_module_run(vm, "vsum", vargs, 7, FIR_DEFAULT_FUEL, &vout));
  CHECK(vout != NULL && strcmp(vout, "returned f64 18.5") == 0);
  printf("fir run @vsum(3, i32 1, f64 0.5, i32 2, f64 1.5, i32 3, f64 2.5): %s\n",
         vout ? vout : "?");
  fir_string_free(vout);
  vout = NULL;
  OK(fir_module_run(vm, "va_show", NULL, 0, FIR_DEFAULT_FUEL, &vout));
  CHECK(vout != NULL && strncmp(vout, "@printf(ptr #", 13) == 0 &&
        strstr(vout, "i64 -1234567890123, i8 90) -> i32 0; @snprintf(") != NULL &&
        strstr(vout, "f64 0.25) -> i32 0; returned i32 0") != NULL);
  printf("fir run @va_show(): %s\n", vout ? vout : "?");
  fir_string_free(vout);
  char *dar = NULL;
  CHECK(fir_module_compile(vm, "aarch64", false, FIR_OS_DARWIN, &dar) == FIR_ERR_COMPILE &&
        strstr(fir_module_error(vm), "macOS") != NULL);
  cur = vm;
  if (cc != NULL && *cc != '\0' && dir != NULL) {
    char want_out[2048];
    va_expected(want_out, sizeof want_out);
    int matched = 0;
    for (int opt = 0; opt < 2; opt++) {
      char *vas = NULL;
      OK(fir_module_compile(vm, "aarch64", opt == 1, FIR_OS_LINUX, &vas));
      char sf[1024], cf[1024], bin[1024], cmd[4096];
      const char *name = opt ? "varargs-O" : "varargs";
      snprintf(sf, sizeof sf, "%s/%s.s", dir, name);
      snprintf(cf, sizeof cf, "%s/%s_main.c", dir, name);
      snprintf(bin, sizeof bin, "%s/%s", dir, name);
      if (vas == NULL || !write_file(sf, vas) || !write_file(cf, va_main)) {
        failures++;
        fir_string_free(vas);
        continue;
      }
      fir_string_free(vas);
      snprintf(cmd, sizeof cmd, "\"%s\" -O1 -w \"%s\" \"%s\" -o \"%s\"", cc, cf, sf, bin);
      if (system(cmd) != 0) {
        fprintf(stderr, "building %s failed\n", bin);
        failures++;
        continue;
      }
      snprintf(cmd, sizeof cmd, "%s%s\"%s\"", runner ? runner : "", runner && *runner ? " " : "",
               bin);
      FILE *pipe = popen(cmd, "r");
      char got[2048];
      size_t len = pipe != NULL ? fread(got, 1, sizeof got - 1, pipe) : 0;
      got[len] = '\0';
      if (pipe != NULL) pclose(pipe);
      printf("native%s varargs:\n%s", opt ? " -O" : "", got);
      if (strcmp(got, want_out) == 0) {
        matched++;
      } else {
        fprintf(stderr, "%s: got\n%s\nwant\n%s\n", name, got, want_out);
        failures++;
      }
    }
    printf("native varargs: %d of 2 programs match the host's printf\n", matched);
  }
  fir_module_free(vm);

  /* Structs and arrays by value across the C boundary. */
  FirModule *sm = build_structs();
  OK(fir_module_verify(sm));
  char *sout = NULL;
  OK(fir_module_run(sm, "fir_calls", (const char *[]){"null"}, 1, FIR_DEFAULT_FUEL, &sout));
  CHECK(sout != NULL &&
        strstr(sout, "@c_mix({i32 -40, f32 2.5}, {f64 0.25, f64 10000000000.0, f64 -3.0}, {i64 "
                     "1234567890123, ptr null, {i16 1, i16 -2, i16 3, i16 -4}}, {f32 0.5, f32 "
                     "-8.0}) -> {f64 0.0, f64 0.0, f64 0.0}") != NULL);
  printf("fir run @fir_calls(null): %s\n", sout ? sout : "?");
  fir_string_free(sout);
  /* Apple's ABI packs stack arguments: a struct passed on the stack is a compile error there. */
  {
    FirModule *dm = cur = fir_module_new();
    FirType i64 = fir_type_int(64), fs[2] = {i64, i64};
    FirType w2 = ID(fir_type_struct(dm, FIR_POLICY_C, fs, 2));
    FirType ps[5] = {w2, w2, w2, w2, w2};
    FirFunc f = ID(fir_func_declare(dm, "five", ps, 5, NULL, 0));
    FirBuilder *b = fir_func_begin(dm, f);
    ID(fir_func_ret(b, NULL, 0));
    OK(fir_func_end(b));
    char *das = NULL;
    CHECK(fir_module_compile(dm, "aarch64", false, FIR_OS_DARWIN, &das) == FIR_ERR_COMPILE &&
          strstr(fir_module_error(dm), "on the stack") != NULL);
    OK(fir_module_compile(dm, "aarch64", false, FIR_OS_LINUX, &das));
    fir_string_free(das);
    fir_module_free(dm);
  }
  cur = sm;
  if (cc != NULL && *cc != '\0' && dir != NULL) {
    int matched = 0;
    for (int opt = 0; opt < 2; opt++) {
      char *sas = NULL;
      OK(fir_module_compile(sm, "aarch64", opt == 1, FIR_OS_LINUX, &sas));
      char sf[1024], cf[1024], bin[1024], cmd[4096];
      const char *name = opt ? "structs-O" : "structs";
      snprintf(sf, sizeof sf, "%s/%s.s", dir, name);
      snprintf(cf, sizeof cf, "%s/%s_main.c", dir, name);
      snprintf(bin, sizeof bin, "%s/%s", dir, name);
      if (sas == NULL || !write_file(sf, sas) || !write_file(cf, struct_main)) {
        failures++;
        fir_string_free(sas);
        continue;
      }
      fir_string_free(sas);
      snprintf(cmd, sizeof cmd, "\"%s\" -O1 -w \"%s\" \"%s\" -o \"%s\"", cc, cf, sf, bin);
      if (system(cmd) != 0) {
        fprintf(stderr, "building %s failed\n", bin);
        failures++;
        continue;
      }
      snprintf(cmd, sizeof cmd, "%s%s\"%s\"", runner ? runner : "", runner && *runner ? " " : "",
               bin);
      FILE *pipe = popen(cmd, "r");
      char got[2048];
      size_t len = pipe != NULL ? fread(got, 1, sizeof got - 1, pipe) : 0;
      got[len] = '\0';
      int status = pipe != NULL ? pclose(pipe) : -1;
      printf("native%s structs:\n%s", opt ? " -O" : "", got);
      if (status == 0 && strstr(got, "WRONG") == NULL && strstr(got, "fir_va ok") != NULL) {
        matched++;
      } else {
        failures++;
      }
    }
    printf("native structs: %d of 2 programs pass every check\n", matched);
  }
  fir_module_free(sm);
  if (failures > 0) {
    fprintf(stderr, "%d checks failed\n", failures);
    return 1;
  }
  puts("ok");
  return 0;
}
