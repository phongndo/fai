/* Builds FIR modules through the C API, then verifies, prints, and runs them.
 *
 * crates/fir-capi/tests/c.rs compiles this file against include/fir.h and the static library,
 * runs it, and checks that it calls every function the header declares. It prints "ok" and
 * exits 0 when every check passes. */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "fir.h"

static int failures = 0;
/* The module being built, for error messages. */
static FirModule *cur = NULL;

#define CHECK(cond)                                                                  \
  do {                                                                               \
    if (!(cond)) {                                                                   \
      fprintf(stderr, "%s:%d: check failed: %s\n", __FILE__, __LINE__, #cond);       \
      failures++;                                                                    \
    }                                                                                \
  } while (0)

/* A call that returns an id, which must not be FIR_INVALID. */
#define ID(x) id_ok((x), __LINE__, #x)
/* A call that returns a status, which must be FIR_OK. */
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

/* Check the module's last error message. */
static void expect_error(const char *want, int line) {
  const char *got = fir_module_error(cur);
  if (strcmp(got, want) != 0) {
    fprintf(stderr, "%s:%d: error '%s', want '%s'\n", __FILE__, line, got, want);
    failures++;
  }
}

static void expect_run(FirModule *m, const char *func, const char **args, size_t nargs,
                       const char *want) {
  char *out = NULL;
  FirStatus s = fir_module_run(m, func, args, nargs, FIR_DEFAULT_FUEL, &out);
  if (s != FIR_OK) {
    fprintf(stderr, "run @%s failed (%u): %s\n", func, s, fir_module_error(m));
    failures++;
    return;
  }
  if (strcmp(out, want) != 0) {
    fprintf(stderr, "run @%s: got '%s', want '%s'\n", func, out, want);
    failures++;
  }
  fir_string_free(out);
}

static void expect_text(FirModule *m, bool show_locs, const char *want) {
  char *text = fir_module_print(m, show_locs);
  if (text == NULL || strcmp(text, want) != 0) {
    fprintf(stderr, "printed:\n%s\nwant:\n%s\n", text ? text : "(null)", want);
    failures++;
  }
  fir_string_free(text);
}

static FirTarget to(FirRegion block, const FirValue *args, size_t nargs) {
  FirTarget t = {block, args, nargs};
  return t;
}

/* @sum(%n) = 0 + 1 + ... + (n - 1), as a loop of cf.blocks. */
static void blocks_loop(void) {
  FirModule *m = cur = fir_module_new();
  FirType i32 = fir_type_int(32);
  FirType two[2] = {i32, i32};
  FirFunc sum = ID(fir_func_declare(m, "sum", &i32, 1, &i32, 1));
  CHECK(fir_func_find(m, "sum") == sum);
  FirBuilder *b = fir_func_begin(m, sum);
  CHECK(b != NULL);
  FirValue n = ID(fir_builder_param(b, 0));
  OK(fir_value_set_name(b, n, "n"));
  FirValue zero = ID(fir_int_const(b, i32, 0));
  OK(fir_value_set_name(b, zero, "zero"));
  FirOp blocks = ID(fir_cf_blocks_begin(b, &i32, 1, false));
  FirRegion entry = ID(fir_block_new(b, blocks, "entry", NULL, 0));
  FirRegion loop = ID(fir_block_new(b, blocks, "loop", two, 2));
  FirRegion body = ID(fir_block_new(b, blocks, "body", two, 2));
  FirRegion done = ID(fir_block_new(b, blocks, "done", &i32, 1));

  OK(fir_position_at_end(b, entry));
  FirValue init[2] = {zero, zero};
  ID(fir_cf_br(b, to(loop, init, 2)));

  OK(fir_position_at_end(b, loop));
  FirValue i = ID(fir_region_param(b, loop, 0));
  FirValue acc = ID(fir_region_param(b, loop, 1));
  OK(fir_value_set_name(b, i, "i"));
  OK(fir_value_set_name(b, acc, "acc"));
  FirValue more = ID(fir_int_cmp(b, FIR_PRED_SLT, i, n));
  FirValue state[2] = {i, acc};
  ID(fir_cf_cond_br(b, more, to(body, state, 2), to(done, &acc, 1)));

  OK(fir_position_at_end(b, body));
  FirValue bi = ID(fir_region_param(b, body, 0));
  FirValue bacc = ID(fir_region_param(b, body, 1));
  OK(fir_value_set_name(b, bi, "bi"));
  OK(fir_value_set_name(b, bacc, "bacc"));
  FirValue acc2 = ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_NSW, bacc, bi));
  FirValue one = ID(fir_int_const(b, i32, 1));
  FirValue i2 = ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_NSW, bi, one));
  FirValue next[2] = {i2, acc2};
  ID(fir_cf_br(b, to(loop, next, 2)));

  OK(fir_position_at_end(b, done));
  FirValue r = ID(fir_region_param(b, done, 0));
  OK(fir_value_set_name(b, r, "r"));
  ID(fir_cf_yield(b, &r, 1));
  OK(fir_blocks_end(b, blocks));

  OK(fir_position_at_end(b, ID(fir_builder_entry(b))));
  FirValue total = ID(fir_op_result(b, blocks, 0));
  OK(fir_value_set_name(b, total, "total"));
  CHECK(fir_value_op(b, total) == blocks);
  ID(fir_func_ret(b, &total, 1));
  OK(fir_func_end(b));

  OK(fir_module_verify(m));
  expect_text(m, true,
              "func @sum(%n: i32) -> i32 {\n"
              "  %zero: i32 = int.const 0\n"
              "  %total: i32 = cf.blocks {\n"
              "  ^entry:\n"
              "    cf.br ^loop(%zero, %zero)\n"
              "  ^loop(%i: i32, %acc: i32):\n"
              "    %8: i1 = int.cmp.slt %i, %n\n"
              "    cf.cond_br %8, ^body(%i, %acc), ^done(%acc)\n"
              "  ^body(%bi: i32, %bacc: i32):\n"
              "    %9: i32 = int.add.nsw %bacc, %bi\n"
              "    %10: i32 = int.const 1\n"
              "    %11: i32 = int.add.nsw %bi, %10\n"
              "    cf.br ^loop(%11, %9)\n"
              "  ^done(%r: i32):\n"
              "    cf.yield %r\n"
              "  }\n"
              "  func.ret %total\n"
              "}\n");
  const char *ten[] = {"10"};
  expect_run(m, "sum", ten, 1, "returned i32 45");
  const char *zero_arg[] = {"0"};
  expect_run(m, "sum", zero_arg, 1, "returned i32 0");
  fir_module_free(m);
}

/* Structs, stack and heap memory, pointers, and a run that goes out of bounds. */
static void memory(void) {
  FirModule *m = cur = fir_module_new();
  FirType i32 = fir_type_int(32), i64 = fir_type_int(64), b8 = fir_type_byte(8);
  FirType fields[2] = {i32, i64};
  FirType pair = ID(fir_type_struct(m, FIR_POLICY_C, fields, 2));
  FirType bytes = ID(fir_type_array(m, 4, b8));

  FirBuilder *b = fir_func_begin(m, ID(fir_func_declare(m, "mem", &i32, 1, &i64, 1)));
  FirValue v = ID(fir_builder_param(b, 0));
  FirValue s = ID(fir_mem_stack_of(b, pair, 8));
  FirValue f0 = ID(fir_ptr_field(b, true, pair, s, 0));
  ID(fir_mem_store(b, i32, v, f0, 4));
  FirValue f1 = ID(fir_ptr_field(b, true, pair, s, 1));
  FirValue w = ID(fir_int_sext(b, i64, v));
  ID(fir_mem_store(b, i64, w, f1, 8));
  FirValue size = ID(fir_ty_size(b, pair));
  FirValue h = ID(fir_mem_alloc(b, FIR_ALLOC_FAIL_NULL, "c.malloc", size, 8));
  ID(fir_mem_copy(b, pair, h, s, 8));
  FirValue h1 = ID(fir_ptr_field(b, true, pair, h, 1));
  FirValue x = ID(fir_mem_load(b, i64, h1, 8));
  FirValue off = ID(fir_ty_offset(b, pair, 1));
  FirValue al = ID(fir_ty_align(b, pair));
  FirValue h1b = ID(fir_ptr_offset(b, true, h, off));
  FirValue y = ID(fir_mem_load(b, i64, h1b, 8));
  FirValue arr = ID(fir_mem_stack(b, 16, 4));
  FirValue three = ID(fir_int_const(b, i64, 3));
  FirValue e3 = ID(fir_ptr_index(b, true, i32, arr, three));
  ID(fir_mem_store(b, i32, v, e3, 4));
  FirValue z = ID(fir_mem_load(b, i32, e3, 4));
  FirValue raw = ID(fir_mem_stack_of(b, bytes, 1));
  ID(fir_mem_copy(b, bytes, raw, e3, 1));
  FirValue a = ID(fir_ptr_addr(b, h));
  FirValue e = ID(fir_ptr_expose(b, h));
  FirValue back = ID(fir_ptr_from_exposed(b, e));
  FirValue same = ID(fir_ptr_with_addr(b, h, a));
  FirValue nul = ID(fir_ptr_null(b));
  FirValue ne = ID(fir_ptr_cmp(b, FIR_PRED_NE, back, nul));
  FirValue eq = ID(fir_ptr_cmp(b, FIR_PRED_EQ, same, h));
  FirValue both = ID(fir_int_bit(b, FIR_BIT_OP_AND, ne, eq));
  ID(fir_mem_free(b, "c.malloc", same));
  FirValue t = ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_NSW, x, y));
  t = ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_NSW, t, al));
  FirValue z64 = ID(fir_int_zext(b, i64, z));
  t = ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_NSW, t, z64));
  FirValue both64 = ID(fir_int_zext(b, i64, both));
  t = ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_NSW, t, both64));
  ID(fir_func_ret(b, &t, 1));
  OK(fir_func_end(b));

  /* @oob(%i): element %i of a 4-element array. */
  b = fir_func_begin(m, ID(fir_func_declare(m, "oob", &i64, 1, &i32, 1)));
  FirValue i = ID(fir_builder_param(b, 0));
  FirValue four = ID(fir_mem_stack(b, 16, 4));
  OK(fir_set_loc(b, 3, 5));
  FirValue at = ID(fir_ptr_index(b, false, i32, four, i));
  FirValue got = ID(fir_mem_load(b, i32, at, 4));
  OK(fir_clear_loc(b));
  ID(fir_func_ret(b, &got, 1));
  OK(fir_func_end(b));

  OK(fir_module_verify(m));
  const char *seven[] = {"7"};
  /* 7 + 7 (the copied field, twice) + 8 (the struct's alignment) + 7 + 1 (both tests). */
  expect_run(m, "mem", seven, 1, "returned i64 30");
  const char *four_arg[] = {"4"};
  expect_run(m, "oob", four_arg, 1, "ub out-of-bounds @3:5 (offset 16, 4 bytes, allocation size 16)");
  fir_module_free(m);
}

/* Globals, an external function, and calls through function pointers. */
static void globals_and_calls(void) {
  FirModule *m = cur = fir_module_new();
  FirType i8 = fir_type_int(8), i32 = fir_type_int(32), i64 = fir_type_int(64);
  FirType ptr = FIR_TYPE_PTR;
  FirType sig = ID(fir_type_func(m, &i32, 1, &i32, 1));
  FirFunc inc = ID(fir_func_declare(m, "inc", &i32, 1, &i32, 1));
  FirFunc dec = ID(fir_func_declare(m, "dec", &i32, 1, &i32, 1));
  FirEffect reads = FIR_EFFECT_READ_ARGS;
  FirFunc puts_ = ID(fir_extern_declare(m, "puts", &ptr, 1, &i32, 1, &reads, 1, FIR_TRUST_ASSUME));

  const uint8_t hi[3] = {'h', 'i', 0};
  FirGlobal msg = ID(fir_global_declare(m, "msg", ID(fir_type_array(m, 3, i8)), true, 1,
                                        ID(fir_init_bytes(m, hi, 3))));
  FirGlobal counter =
      ID(fir_global_declare(m, "counter", i32, false, 4, ID(fir_init_int(m, 5))));
  FirGlobal table = ID(fir_global_declare(m, "table", ID(fir_type_array(m, 2, ptr)), true, 1,
                                          ID(fir_init_zero(m))));
  FirInit fns[2] = {ID(fir_init_func(m, inc)), ID(fir_init_func(m, dec))};
  OK(fir_global_set_init(m, table, ID(fir_init_list(m, fns, 2))));
  FirType pair[2] = {ptr, ptr};
  FirGlobal self = ID(fir_global_declare(m, "self", ID(fir_type_struct(m, FIR_POLICY_C, pair, 2)),
                                         false, 8, ID(fir_init_zero(m))));
  FirInit links[2] = {ID(fir_init_global(m, self)), ID(fir_init_null(m))};
  OK(fir_global_set_init(m, self, ID(fir_init_list(m, links, 2))));

  for (int k = 0; k < 2; k++) {
    FirBuilder *b = fir_func_begin(m, k == 0 ? inc : dec);
    FirValue x = ID(fir_builder_param(b, 0));
    FirValue one = ID(fir_int_const(b, i32, 1));
    FirValue r = ID(fir_int_arith(b, k == 0 ? FIR_ARITH_OP_ADD : FIR_ARITH_OP_SUB, FIR_OVF_NSW,
                                  x, one));
    ID(fir_func_ret(b, &r, 1));
    OK(fir_func_end(b));
  }

  FirBuilder *b = fir_func_begin(m, ID(fir_func_declare(m, "hello", NULL, 0, &i32, 1)));
  FirValue p = ID(fir_mem_global(b, msg));
  FirOp call = ID(fir_func_call(b, puts_, &p, 1));
  FirValue r = ID(fir_op_result(b, call, 0));
  ID(fir_func_ret(b, &r, 1));
  OK(fir_func_end(b));

  b = fir_func_begin(m, ID(fir_func_declare(m, "bump", NULL, 0, &i32, 1)));
  FirValue cp = ID(fir_mem_global(b, counter));
  FirValue c = ID(fir_mem_load(b, i32, cp, 4));
  FirValue c2 = ID(fir_op_result(b, ID(fir_func_call(b, inc, &c, 1)), 0));
  ID(fir_mem_store(b, i32, c2, cp, 4));
  ID(fir_func_ret(b, &c2, 1));
  OK(fir_func_end(b));

  FirType kx[2] = {i64, i32};
  b = fir_func_begin(m, ID(fir_func_declare(m, "dispatch", kx, 2, &i32, 1)));
  FirValue k = ID(fir_builder_param(b, 0)), x = ID(fir_builder_param(b, 1));
  FirValue tp = ID(fir_mem_global(b, table));
  FirValue slot = ID(fir_ptr_index(b, true, ptr, tp, k));
  FirValue fp = ID(fir_mem_load(b, ptr, slot, 8));
  FirValue dr = ID(fir_op_result(b, ID(fir_func_call_indirect(b, sig, fp, &x, 1)), 0));
  ID(fir_func_ret(b, &dr, 1));
  OK(fir_func_end(b));

  b = fir_func_begin(m, ID(fir_func_declare(m, "direct", &i32, 1, &i32, 1)));
  x = ID(fir_builder_param(b, 0));
  FirValue ip = ID(fir_func_addr(b, inc));
  FirValue ir = ID(fir_op_result(b, ID(fir_func_call_indirect(b, sig, ip, &x, 1)), 0));
  ID(fir_func_ret(b, &ir, 1));
  OK(fir_func_end(b));

  OK(fir_module_verify(m));
  expect_run(m, "hello", NULL, 0, "@puts(ptr #1) -> i32 0; returned i32 0");
  expect_run(m, "bump", NULL, 0, "returned i32 6");
  const char *one_ten[] = {"1", "10"};
  expect_run(m, "dispatch", one_ten, 2, "returned i32 9");
  const char *ten[] = {"10"};
  expect_run(m, "direct", ten, 1, "returned i32 11");
  char *text = fir_module_print(m, false);
  CHECK(text != NULL && strstr(text, "global const @table: array<2 x ptr> = {@inc, @dec}\n"));
  CHECK(text != NULL && strstr(text, "global @self: struct<C>{ptr, ptr} align 8 = {@self, null}\n"));
  CHECK(text != NULL &&
        strstr(text, "extern func @puts(ptr) -> i32 effects[read(args)] assume\n"));
  fir_string_free(text);
  fir_module_free(m);
}

/* Every integer op, structured control flow, facts, locations, holes, and a data layout. */
static void control_and_ints(void) {
  FirModule *m = cur = fir_module_new();
  FirIntAlign ints[3] = {{8, 1}, {32, 4}, {64, 4}};
  OK(fir_module_set_space(m, 32, 32, 0, ints, 3));
  FirType i1 = fir_type_int(1), i32 = fir_type_int(32), i64 = fir_type_int(64);
  FirType i128 = fir_type_int(128);
  FirType ab[2] = {i32, i32};

  /* @ints(%a, %b), as tests/fir1/generic.fir writes it. */
  FirBuilder *b = fir_func_begin(m, ID(fir_func_declare(m, "ints", ab, 2, &i32, 1)));
  OK(fir_set_file(b, "ints.c"));
  OK(fir_set_loc(b, 1, 1));
  FirValue a = ID(fir_builder_param(b, 0)), bb = ID(fir_builder_param(b, 1));
  FirValue c = ID(fir_int_const(b, i32, 5));
  FirValue s = ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_NSW, a, bb));
  FirValue d = ID(fir_int_arith(b, FIR_ARITH_OP_SUB, FIR_OVF_WRAP, s, c));
  FirValue mu = ID(fir_int_arith(b, FIR_ARITH_OP_MUL, FIR_OVF_S_TRAP, d, bb));
  FirValue q = ID(fir_int_div(b, FIR_DIV_OP_DIV_S, FIR_EDGE_TRAP, FIR_EDGE_WRAP, mu, bb));
  FirValue r = ID(fir_int_div(b, FIR_DIV_OP_REM_U, FIR_EDGE_UB, FIR_EDGE_UB, q, c));
  FirValue x = ID(fir_int_bit(b, FIR_BIT_OP_XOR, r, a));
  FirValue sh = ID(fir_int_shift(b, FIR_SHIFT_OP_SHL, FIR_SHIFT_EDGE_MASK, x, bb));
  FirValue lt = ID(fir_int_cmp(b, FIR_PRED_SLT, a, bb));
  FirValue sel = ID(fir_select(b, lt, sh, x));
  FirValue w = ID(fir_int_sext(b, i64, sel));
  ID(fir_int_zext(b, i64, a));
  FirValue t = ID(fir_int_trunc(b, i32, FIR_TRUNC_MODE_WRAP, w));
  FirValue p = ID(fir_poison(b, i32));
  FirValue f = ID(fir_freeze(b, p));
  FirValue y = ID(fir_copy(b, t));
  FirValue res = ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_WRAP, y, f));
  FirOp ret = ID(fir_func_ret(b, &res, 1));
  /* An op put in before the return. */
  OK(fir_position_before(b, ret));
  OK(fir_clear_loc(b));
  FirValue unused = ID(fir_int_shift(b, FIR_SHIFT_OP_SHR_S, FIR_SHIFT_EDGE_TOTAL, a, c));
  OK(fir_value_set_name(b, unused, "unused"));
  OK(fir_func_end(b));

  /* @count(%n): a cf.loop with a cf.if that breaks, built with the _begin forms. */
  b = fir_func_begin(m, ID(fir_func_declare(m, "count", &i32, 1, &i32, 1)));
  FirValue n = ID(fir_builder_param(b, 0));
  FirFact positive = {FIR_FACT_RANGE_S, FIR_TRUST_CHECK, 0, 1000};
  OK(fir_value_set_facts(b, n, &positive, 1));
  FirValue zero = ID(fir_int_const(b, i32, 0));
  FirOp loop = ID(fir_cf_loop_begin(b, &i32, 1, true, &zero, 1));
  FirRegion body = ID(fir_op_region(b, loop, 0));
  OK(fir_position_at_end(b, body));
  FirValue i = ID(fir_region_param(b, body, 0));
  OK(fir_value_set_name(b, i, "i"));
  FirFact small = {FIR_FACT_RANGE_S, FIR_TRUST_ASSUME, 0, 1000};
  OK(fir_value_set_facts(b, i, &small, 1));
  FirValue done = ID(fir_int_cmp(b, FIR_PRED_SGE, i, n));
  FirOp brk = ID(fir_cf_if_begin(b, NULL, 0, done));
  OK(fir_position_at_end(b, ID(fir_op_region(b, brk, 0))));
  ID(fir_cf_break(b, &i, 1));
  OK(fir_position_at_end(b, body));
  FirValue one = ID(fir_int_const(b, i32, 1));
  FirValue next = ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_NSW, i, one));
  ID(fir_cf_continue(b, &next, 1));
  OK(fir_position_at_end(b, ID(fir_builder_entry(b))));
  FirValue counted = ID(fir_op_result(b, loop, 0));
  ID(fir_func_ret(b, &counted, 1));
  OK(fir_func_end(b));

  /* @pick(%c, %a, %b): cf.if with results. */
  FirType cab[3] = {i1, i32, i32};
  b = fir_func_begin(m, ID(fir_func_declare(m, "pick", cab, 3, &i32, 1)));
  FirValue cc = ID(fir_builder_param(b, 0));
  FirValue pa = ID(fir_builder_param(b, 1)), pb = ID(fir_builder_param(b, 2));
  FirOp choice = ID(fir_cf_if_begin(b, &i32, 1, cc));
  OK(fir_position_at_end(b, ID(fir_op_region(b, choice, 0))));
  ID(fir_cf_yield(b, &pa, 1));
  OK(fir_position_at_end(b, ID(fir_op_region(b, choice, 1))));
  ID(fir_cf_yield(b, &pb, 1));
  OK(fir_position_at_end(b, ID(fir_builder_entry(b))));
  FirValue picked = ID(fir_op_result(b, choice, 0));
  ID(fir_func_ret(b, &picked, 1));
  OK(fir_func_end(b));

  /* @classify(%x): cf.switch over blocks. */
  b = fir_func_begin(m, ID(fir_func_declare(m, "classify", &i32, 1, &i32, 1)));
  FirValue cx = ID(fir_builder_param(b, 0));
  FirOp blocks = ID(fir_cf_blocks_begin(b, &i32, 1, true));
  FirRegion entry = ID(fir_block_new(b, blocks, NULL, NULL, 0));
  FirRegion ten = ID(fir_block_new(b, blocks, "ten", NULL, 0));
  FirRegion other = ID(fir_block_new(b, blocks, "other", &i32, 1));
  OK(fir_position_at_end(b, entry));
  FirCase cases[2] = {{1, to(ten, NULL, 0)}, {-1, to(other, &cx, 1)}};
  ID(fir_cf_switch(b, cx, to(other, &cx, 1), cases, 2));
  OK(fir_position_at_end(b, ten));
  FirValue tenv = ID(fir_int_const(b, i32, 10));
  ID(fir_cf_yield(b, &tenv, 1));
  OK(fir_position_at_end(b, other));
  FirValue ov = ID(fir_region_param(b, other, 0));
  ID(fir_cf_yield(b, &ov, 1));
  OK(fir_position_at_end(b, ID(fir_builder_entry(b))));
  FirValue cls = ID(fir_op_result(b, blocks, 0));
  ID(fir_func_ret(b, &cls, 1));
  OK(fir_func_end(b)); /* gives the blocks to their op */

  /* @wide(): a constant wider than 64 bits, and the pointer size of this layout. */
  FirType two[2] = {i128, i32};
  b = fir_func_begin(m, ID(fir_func_declare(m, "wide", NULL, 0, two, 2)));
  FirValue big = ID(fir_int_const_dec(b, i128, "-170141183460469231731687303715884105728"));
  FirValue psize = ID(fir_ty_size(b, FIR_TYPE_PTR));
  FirValue outs[2] = {big, psize};
  ID(fir_func_ret(b, outs, 2));
  OK(fir_func_end(b));

  /* @partial(%x): a hole stands for a value not written yet. */
  b = fir_func_begin(m, ID(fir_func_declare(m, "partial", &i32, 1, &i32, 1)));
  FirValue px = ID(fir_builder_param(b, 0));
  FirValue hole = ID(fir_hole(b, "todo", i32));
  FirValue sum = ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_NSW, px, hole));
  ID(fir_func_ret(b, &sum, 1));
  OK(fir_func_end(b));

  OK(fir_module_verify(m));
  const char *three_seven[] = {"3", "7"};
  expect_run(m, "ints", three_seven, 2, "returned i32 384");
  const char *four[] = {"4"};
  expect_run(m, "count", four, 1, "returned i32 4");
  const char *pick_args[] = {"0", "1", "2"};
  expect_run(m, "pick", pick_args, 3, "returned i32 2");
  const char *x1[] = {"1"}, *x5[] = {"5"}, *xm1[] = {"-1"};
  expect_run(m, "classify", x1, 1, "returned i32 10");
  expect_run(m, "classify", x5, 1, "returned i32 5");
  expect_run(m, "classify", xm1, 1, "returned i32 -1");
  expect_run(m, "wide", NULL, 0,
             "returned i128 -170141183460469231731687303715884105728, i32 4");

  char *text = fir_module_print(m, true);
  if (getenv("FIR_CAPI_SHOW")) fputs(text, stderr);
  CHECK(text != NULL && strncmp(text, "memspace default ptr 32 addr 32 int 8:1 32:4 64:4\n", 50) == 0);
  CHECK(text != NULL && strstr(text, "func @ints(%0: i32, %1: i32) -> i32 loc \"ints.c\" {\n"));
  CHECK(text != NULL && strstr(text, "  %2: i32 = int.const 5 @1:1\n"));
  CHECK(text != NULL && strstr(text, "  %unused: i32 = int.shr.s.total %0, %2\n  func.ret %18 @1:1\n"));
  CHECK(text != NULL && strstr(text, "func @count(%0: i32 [range.s(0, 1000) check]) -> i32 {\n"));
  CHECK(text != NULL && strstr(text, "cf.loop progress iter(%i: i32 [range.s(0, 1000) assume] = %1) {\n"));
  CHECK(text != NULL && strstr(text, "  ^1:\n    cf.switch %0, default ^other(%0), [1: ^ten, -1: ^other(%0)]\n"));
  CHECK(text != NULL && strstr(text, "%1: i32 = int.add.nsw %0, ?todo: i32\n"));
  fir_string_free(text);
  fir_module_free(m);
}

/* What fails, fails without changing anything, and says why. */
static void errors(void) {
  FirModule *m = cur = fir_module_new();
  FirType i32 = fir_type_int(32), i64 = fir_type_int(64);
  CHECK(fir_type_int(0) == FIR_INVALID);
  FirType both[2] = {i32, i64};
  FirBuilder *b = fir_func_begin(m, ID(fir_func_declare(m, "f", both, 2, &i32, 1)));
  FirValue a = ID(fir_builder_param(b, 0)), w = ID(fir_builder_param(b, 1));
  CHECK(fir_builder_param(b, 2) == FIR_INVALID);
  expect_error("the function has no parameter 2", __LINE__);
  CHECK(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_NSW, a, w) == FIR_INVALID);
  expect_error("int.add.nsw: operands: expected (i32) but got (i64)", __LINE__);
  CHECK(fir_int_arith(b, 7, FIR_OVF_NSW, a, a) == FIR_INVALID);
  expect_error("7 is not a FirArithOp", __LINE__);
  CHECK(fir_int_div(b, FIR_DIV_OP_DIV_S, 99, FIR_EDGE_UB, a, a) == FIR_INVALID);
  expect_error("99 is not a FirEdge", __LINE__);
  CHECK(fir_copy(b, 12345) == FIR_INVALID);
  expect_error("copy: value 12345 does not exist in this function", __LINE__);
  CHECK(fir_mem_load(b, i32, a, 4) == FIR_INVALID);
  expect_error("mem.load: operands: expected (ptr) but got (i32)", __LINE__);
  CHECK(fir_func_begin(m, 0) == NULL);
  expect_error("@f is still being built", __LINE__);
  CHECK(fir_func_declare(m, "f", NULL, 0, NULL, 0) == FIR_INVALID);
  expect_error("@f is defined more than once", __LINE__);
  CHECK(fir_func_declare(m, "9lives", NULL, 0, NULL, 0) == FIR_INVALID);
  expect_error("'9lives' is not a valid name", __LINE__);
  /* No terminator: building allows it, verifying doesn't. */
  ID(fir_int_const(b, i32, 1));
  OK(fir_func_end(b));
  CHECK(fir_module_verify(m) == FIR_ERR_VERIFY);
  expect_error("in @f: @?: the function body must end with func.ret", __LINE__);
  char *out = NULL;
  CHECK(fir_module_run(m, "f", NULL, 0, 10, &out) == FIR_ERR_VERIFY && out == NULL);

  /* A function can be dropped and built again. */
  FirFunc g = ID(fir_func_declare(m, "g", NULL, 0, NULL, 0));
  b = fir_func_begin(m, g);
  ID(fir_int_const(b, i32, 1));
  fir_func_abandon(b);
  b = fir_func_begin(m, g);
  ID(fir_func_ret(b, NULL, 0));
  OK(fir_func_end(b));
  CHECK(fir_module_run(m, "nope", NULL, 0, 10, &out) == FIR_ERR_VERIFY);
  fir_module_free(m);

  /* Layers: ops are checked against the module's layer as they are built. */
  m = cur = fir_module_new();
  CHECK(fir_module_set_layer(m, FIR_LAYER_LFIR, "x86") == FIR_ERR_INVALID);
  expect_error("unknown target 'x86'", __LINE__);
  CHECK(fir_module_set_layer(m, 9, NULL) == FIR_ERR_INVALID);
  expect_error("9 is not a FirLayer", __LINE__);
  OK(fir_module_set_layer(m, FIR_LAYER_LFIR, "aarch64"));
  OK(fir_module_set_layer(m, FIR_LAYER_MFIR, NULL));
  FirType pair = ID(fir_type_struct(m, FIR_POLICY_C, both, 2));
  FirType ptr = FIR_TYPE_PTR;
  b = fir_func_begin(m, ID(fir_func_declare(m, "field", &ptr, 1, &ptr, 1)));
  FirValue p = ID(fir_builder_param(b, 0));
  CHECK(fir_ptr_field(b, true, pair, p, 1) == FIR_INVALID);
  expect_error("ptr.field.inbounds is not allowed in layer mfir; it is allowed in hfir", __LINE__);
  FirValue off = ID(fir_ty_offset(b, pair, 1));
  FirValue q = ID(fir_ptr_offset(b, true, p, off));
  ID(fir_func_ret(b, &q, 1));
  OK(fir_func_end(b));
  OK(fir_module_verify(m));
  char *ltext = fir_module_print(m, false);
  CHECK(ltext != NULL && strncmp(ltext, "layer mfir\n", 11) == 0);
  fir_string_free(ltext);
  fir_module_free(m);

  /* Parsing. */
  FirModule *parsed = NULL;
  char *msg = NULL;
  CHECK(fir_module_parse("func @f(", &parsed, &msg) == FIR_ERR_PARSE && parsed == NULL);
  CHECK(msg != NULL && strcmp(msg, "1:9: expected a %value but found end of input") == 0);
  fir_string_free(msg);
  CHECK(fir_module_parse("func @id(%x: i32) -> i32 {\n  func.ret %x\n}\n", &parsed, &msg) ==
        FIR_OK);
  cur = parsed;
  const char *args[] = {"5"};
  expect_run(parsed, "id", args, 1, "returned i32 5");
  CHECK(fir_module_run(parsed, "id", NULL, 0, 10, &out) == FIR_ERR_RUN);
  expect_error("@id takes 1 arguments but got 0", __LINE__);
  /* A parsed module can be built on: call @id from a new function. */
  FirFunc id = ID(fir_func_find(parsed, "id"));
  b = fir_func_begin(parsed, ID(fir_func_declare(parsed, "twice", &i32, 1, &i32, 1)));
  FirValue x = ID(fir_builder_param(b, 0));
  FirValue once = ID(fir_op_result(b, ID(fir_func_call(b, id, &x, 1)), 0));
  ID(fir_func_ret(b, &once, 1));
  OK(fir_func_end(b));
  expect_run(parsed, "twice", args, 1, "returned i32 5");
  fir_module_free(parsed);
  /* Null handles are reported, not followed. */
  CHECK(fir_func_end(NULL) == FIR_ERR_INVALID);
  CHECK(fir_int_const(NULL, i32, 0) == FIR_INVALID);
  CHECK(strcmp(fir_module_error(NULL), "no module") == 0);
}

/* AArch64 LFIR: machine code on registers, with a function's code as the labeled blocks of
 * aarch64.code. Virtual registers (FIR_REG_V0 + n) need no allocation to run. */
static void lfir(void) {
  FirModule *m = cur = fir_module_new();
  OK(fir_module_set_layer(m, FIR_LAYER_LFIR, "aarch64"));
  FirType i64 = fir_type_int(64);
  FirType two[2] = {i64, i64};
  const FirReg x0 = 0, x1 = 1, x9 = 9;
  FirReg v[8];
  for (int k = 0; k < 8; k++) v[k] = FIR_REG_V0 + (FirReg)k;
  FirGlobal cell = ID(fir_global_declare(m, "cell", i64, false, 8, ID(fir_init_int(m, 0))));
  FirFunc five = ID(fir_func_declare(m, "five", NULL, 0, &i64, 1));
  FirFunc calc = ID(fir_func_declare(m, "calc", two, 2, &i64, 1));
  FirFunc heap = ID(fir_func_declare(m, "heap", NULL, 0, &i64, 1));

  FirBuilder *b = fir_func_begin(m, five);
  FirOp code = ID(fir_aarch64_code_begin(b));
  OK(fir_position_at_end(b, ID(fir_block_new(b, code, "entry", NULL, 0))));
  ID(fir_aarch64_mov_wide(b, FIR_MOV_OP_MOVZ, FIR_SF_X, x0, 5, 0));
  ID(fir_aarch64_ret(b));
  OK(fir_blocks_end(b, code));
  OK(fir_func_end(b));

  b = fir_func_begin(m, calc);
  OK(fir_value_set_name(b, ID(fir_builder_param(b, 0)), "a"));
  OK(fir_value_set_name(b, ID(fir_builder_param(b, 1)), "b"));
  code = ID(fir_aarch64_code_begin(b));
  FirRegion entry = ID(fir_block_new(b, code, "entry", NULL, 0));
  FirRegion small = ID(fir_block_new(b, code, "small", NULL, 0));
  FirRegion big = ID(fir_block_new(b, code, "big", NULL, 0));
  FirRegion done = ID(fir_block_new(b, code, "done", NULL, 0));
  OK(fir_position_at_end(b, entry));
  ID(fir_aarch64_alu(b, FIR_ALU_OP_ADD, FIR_SF_X, v[0], x0, x1));
  ID(fir_aarch64_alu_imm(b, FIR_ALU_IMM_OP_ADD, FIR_SF_X, v[1], v[0], 5));
  ID(fir_aarch64_shift_imm(b, FIR_SHIFT_IMM_OP_LSL, FIR_SF_X, v[2], v[1], 1));
  ID(fir_aarch64_ext(b, true, FIR_SF_X, v[3], v[2], 8));
  ID(fir_aarch64_mov_wide(b, FIR_MOV_OP_MOVZ, FIR_SF_X, v[4], 3, 0));
  ID(fir_aarch64_mov_wide(b, FIR_MOV_OP_MOVK, FIR_SF_X, v[4], 0, 16));
  ID(fir_aarch64_alu(b, FIR_ALU_OP_SUBS, FIR_SF_X, FIR_REG_XZR, v[3], v[4]));
  ID(fir_aarch64_csel(b, FIR_CSEL_OP_CSEL, FIR_COND_GT, FIR_SF_X, v[5], v[3], v[4]));
  ID(fir_aarch64_adrl(b, x9, cell));
  ID(fir_aarch64_str(b, FIR_MEM_SIZE_X, v[5], x9, 0));
  ID(fir_aarch64_ldr(b, FIR_MEM_SIZE_X, v[6], x9, 0));
  ID(fir_aarch64_b_cond(b, FIR_COND_GE, to(big, NULL, 0), to(small, NULL, 0)));
  OK(fir_position_at_end(b, small));
  ID(fir_aarch64_mov(b, FIR_SF_X, x0, v[6]));
  ID(fir_aarch64_b(b, to(done, NULL, 0)));
  OK(fir_position_at_end(b, big));
  ID(fir_aarch64_adrl_func(b, v[7], five));
  ID(fir_aarch64_blr(b, ID(fir_type_func(m, NULL, 0, &i64, 1)), v[7]));
  ID(fir_aarch64_alu(b, FIR_ALU_OP_ADD, FIR_SF_X, x0, x0, v[6]));
  ID(fir_aarch64_b(b, to(done, NULL, 0)));
  OK(fir_position_at_end(b, done));
  ID(fir_aarch64_ret(b));
  /* Registers and modifiers are checked. */
  CHECK(fir_aarch64_mov(b, FIR_SF_X, 40, x0) == FIR_INVALID);
  expect_error("40 is not a register", __LINE__);
  CHECK(fir_aarch64_alu(b, 99, FIR_SF_X, x0, x0, x0) == FIR_INVALID);
  expect_error("99 is not a FirAluOp", __LINE__);
  OK(fir_blocks_end(b, code));
  OK(fir_func_end(b));

  b = fir_func_begin(m, heap);
  code = ID(fir_aarch64_code_begin(b));
  entry = ID(fir_block_new(b, code, "entry", NULL, 0));
  FirRegion ok = ID(fir_block_new(b, code, "ok", NULL, 0));
  FirRegion oom = ID(fir_block_new(b, code, "oom", NULL, 0));
  OK(fir_position_at_end(b, entry));
  ID(fir_aarch64_mov_wide(b, FIR_MOV_OP_MOVZ, FIR_SF_X, x0, 16, 0));
  ID(fir_aarch64_bl_alloc(b, "c.malloc", 16));
  ID(fir_aarch64_alu_imm(b, FIR_ALU_IMM_OP_SUBS, FIR_SF_X, FIR_REG_XZR, x0, 0));
  ID(fir_aarch64_b_cond(b, FIR_COND_EQ, to(oom, NULL, 0), to(ok, NULL, 0)));
  OK(fir_position_at_end(b, ok));
  ID(fir_aarch64_bl_free(b, "c.malloc"));
  ID(fir_aarch64_bl(b, five));
  ID(fir_aarch64_ret(b));
  OK(fir_position_at_end(b, oom));
  OK(fir_set_loc(b, 7, 9));
  ID(fir_aarch64_trap(b, FIR_TRAP_REASON_OOM));
  OK(fir_blocks_end(b, code));
  OK(fir_func_end(b));

  OK(fir_module_verify(m));
  expect_text(m, true,
              "layer lfir aarch64\n"
              "\n"
              "global @cell: i64 align 8 = 0\n"
              "\n"
              "func @five() -> i64 {\n"
              "  aarch64.code {\n"
              "  ^entry:\n"
              "    aarch64.movz.x x0, 5, 0\n"
              "    aarch64.ret\n"
              "  }\n"
              "}\n"
              "\n"
              "func @calc(%a: i64, %b: i64) -> i64 {\n"
              "  aarch64.code {\n"
              "  ^entry:\n"
              "    aarch64.add.x v0, x0, x1\n"
              "    aarch64.add.imm.x v1, v0, 5\n"
              "    aarch64.lsl.imm.x v2, v1, 1\n"
              "    aarch64.sbfx.x v3, v2, 8\n"
              "    aarch64.movz.x v4, 3, 0\n"
              "    aarch64.movk.x v4, 0, 16\n"
              "    aarch64.subs.x xzr, v3, v4\n"
              "    aarch64.csel.gt.x v5, v3, v4\n"
              "    aarch64.adrl x9, @cell\n"
              "    aarch64.str.x v5, x9, 0\n"
              "    aarch64.ldr.x v6, x9, 0\n"
              "    aarch64.b.ge ^big, ^small\n"
              "  ^small:\n"
              "    aarch64.mov.x x0, v6\n"
              "    aarch64.b ^done\n"
              "  ^big:\n"
              "    aarch64.adrl.func v7, @five\n"
              "    aarch64.blr func<() -> i64> v7\n"
              "    aarch64.add.x x0, x0, v6\n"
              "    aarch64.b ^done\n"
              "  ^done:\n"
              "    aarch64.ret\n"
              "  }\n"
              "}\n"
              "\n"
              "func @heap() -> i64 {\n"
              "  aarch64.code {\n"
              "  ^entry:\n"
              "    aarch64.movz.x x0, 16, 0\n"
              "    aarch64.bl.alloc c.malloc, align 16\n"
              "    aarch64.subs.imm.x xzr, x0, 0\n"
              "    aarch64.b.eq ^oom, ^ok\n"
              "  ^ok:\n"
              "    aarch64.bl.free c.malloc\n"
              "    aarch64.bl @five\n"
              "    aarch64.ret\n"
              "  ^oom:\n"
              "    aarch64.trap.oom @7:9\n"
              "  }\n"
              "}\n");
  const char *small_args[] = {"-10", "2"}, *big_args[] = {"1", "2"};
  expect_run(m, "calc", small_args, 2, "returned i64 3");
  expect_run(m, "calc", big_args, 2, "returned i64 21");
  expect_run(m, "heap", NULL, 0, "returned i64 5");
  fir_module_free(m);
}

/* An HFIR module using every building block: aggregate values (and an aggregate parameter and
 * result), checked arithmetic, a tagged union, a slice, and a check. It runs, lowers to MFIR,
 * optimizes, and compiles to AArch64 assembly through the C API. */
static void building_blocks(void) {
  FirModule *m = cur = fir_module_new();
  FirType i1 = fir_type_int(1), i32 = fir_type_int(32), i64 = fir_type_int(64);
  FirType two[2] = {i32, i32};
  FirType pair = ID(fir_type_struct(m, FIR_POLICY_C, two, 2));
  FirType vs[2] = {i32, i64};
  FirType u = ID(fir_type_union(m, vs, 2));
  CHECK(fir_type_union(m, NULL, 0) == FIR_INVALID);
  expect_error("a union needs at least one variant", __LINE__);
  FirType arr = ID(fir_type_array(m, 4, i32));

  /* @swap(%s: struct<C>{i32, i32}) -> struct<C>{i32, i32} */
  FirFunc swap = ID(fir_func_declare(m, "swap", &pair, 1, &pair, 1));
  FirBuilder *b = fir_func_begin(m, swap);
  FirValue s = ID(fir_builder_param(b, 0));
  OK(fir_value_set_name(b, s, "s"));
  FirValue a = ID(fir_agg_extract(b, i32, s, 0));
  FirValue c = ID(fir_agg_extract(b, i32, s, 1));
  FirValue t = ID(fir_agg_insert(b, s, a, 1));
  FirValue w = ID(fir_agg_insert(b, t, c, 0));
  ID(fir_func_ret(b, &w, 1));
  OK(fir_func_end(b));

  /* @len(%s: slice) -> i64 */
  FirType slice = FIR_TYPE_SLICE;
  FirFunc lenf = ID(fir_func_declare(m, "len", &slice, 1, &i64, 1));
  b = fir_func_begin(m, lenf);
  FirValue n = ID(fir_slice_len(b, ID(fir_builder_param(b, 0))));
  ID(fir_func_ret(b, &n, 1));
  OK(fir_func_end(b));

  /* @blocks(%x: i32, %i: i64) -> (i32, i1, i32, i32, i64, i32) */
  FirType params[2] = {i32, i64};
  FirType rets[6] = {i32, i1, i32, i32, i64, i32};
  FirFunc f = ID(fir_func_declare(m, "blocks", params, 2, rets, 6));
  b = fir_func_begin(m, f);
  FirValue x = ID(fir_builder_param(b, 0));
  FirValue i = ID(fir_builder_param(b, 1));
  OK(fir_value_set_name(b, x, "x"));
  OK(fir_value_set_name(b, i, "i"));
  FirValue one = ID(fir_int_const(b, i32, 1));
  FirValue y = ID(fir_int_arith(b, FIR_ARITH_OP_ADD, FIR_OVF_WRAP, x, one));
  FirValue xy[2] = {x, y};
  FirValue sv = ID(fir_agg_make(b, pair, xy, 2));
  FirOp call = ID(fir_func_call(b, swap, &sv, 1));
  FirValue r = ID(fir_op_result(b, call, 0));
  FirValue r0 = ID(fir_agg_extract(b, i32, r, 0));
  FirOp add = ID(fir_int_overflow(b, FIR_ARITH_OP_ADD, true, x, y));
  FirValue ovf = ID(fir_op_result(b, add, 1));
  FirValue uv = ID(fir_union_make(b, u, x, 0));
  FirValue tag = ID(fir_union_tag(b, uv));
  FirValue ux = ID(fir_union_get(b, i32, true, uv, 0));
  FirValue p = ID(fir_mem_stack_of(b, arr, 4));
  FirValue four = ID(fir_int_const(b, i64, 4));
  FirValue sl = ID(fir_slice_make(b, p, four));
  CHECK(fir_slice_make(b, x, four) == FIR_INVALID);
  ID(fir_slice_set(b, true, i32, x, sl, i, 4));
  FirValue g = ID(fir_slice_get(b, i32, true, sl, i, 4));
  FirValue len = ID(fir_op_result(b, ID(fir_func_call(b, lenf, &sl, 1)), 0));
  FirValue sp = ID(fir_slice_ptr(b, sl));
  FirValue same = ID(fir_ptr_cmp(b, FIR_PRED_EQ, sp, p));
  ID(fir_cf_check(b, FIR_TRAP_REASON_TAG, same));
  FirValue t1 = ID(fir_int_const(b, i1, 1));
  FirValue nov = ID(fir_int_bit(b, FIR_BIT_OP_XOR, ovf, t1));
  ID(fir_cf_check(b, FIR_TRAP_REASON_OVERFLOW, nov));
  FirValue out[6] = {r0, ovf, tag, ux, len, g};
  ID(fir_func_ret(b, out, 6));
  OK(fir_func_end(b));
  OK(fir_module_verify(m));

  const char *ok_args[] = {"5", "2"};
  const char *ovf_args[] = {"1073741824", "0"};
  const char *oob_args[] = {"5", "4"};
  const char *ret = "returned i32 6, i1 0, i32 0, i32 5, i64 4, i32 5";
  expect_run(m, "blocks", ok_args, 2, ret);
  expect_run(m, "blocks", ovf_args, 2, "trap overflow");
  expect_run(m, "blocks", oob_args, 2, "trap bounds");

  /* Lowered to MFIR: the same runs, and @swap passes its struct as two i32s. */
  FirModule *l = NULL;
  OK(fir_module_lower(m, &l));
  CHECK(l != NULL);
  if (l != NULL) {
    expect_run(l, "blocks", ok_args, 2, ret);
    expect_run(l, "blocks", ovf_args, 2, "trap overflow");
    expect_run(l, "blocks", oob_args, 2, "trap bounds");
    char *text = fir_module_print(l, false);
    CHECK(text != NULL && strncmp(text, "layer mfir\n", 11) == 0);
    CHECK(text != NULL && strstr(text, "func @swap(%s.0: i32, %s.1: i32) -> (i32, i32)") != NULL);
    fir_string_free(text);
    cur = l;
    FirModule *again = NULL;
    CHECK(fir_module_lower(l, &again) == FIR_ERR_INVALID && again == NULL);
    expect_error("only an HFIR module can be lowered", __LINE__);

    /* Optimized: the same runs again. */
    FirModule *o = NULL;
    OK(fir_module_optimize(l, &o));
    CHECK(o != NULL);
    if (o != NULL) {
      expect_run(o, "blocks", ok_args, 2, ret);
      expect_run(o, "blocks", oob_args, 2, "trap bounds");
      fir_module_free(o);
    }
    fir_module_free(l);
    cur = m;
  }

  /* Compiled to AArch64 assembly, from the HFIR, with and without -O. */
  for (int opt = 0; opt < 2; opt++) {
    char *as = NULL;
    OK(fir_module_compile(m, "aarch64", opt == 1, FIR_OS_LINUX, &as));
    CHECK(as != NULL && strstr(as, "blocks:") != NULL && strstr(as, "__fir_trap") != NULL);
    fir_string_free(as);
  }
  char *as = NULL;
  CHECK(fir_module_compile(m, "x86", false, FIR_OS_LINUX, &as) == FIR_ERR_INVALID && as == NULL);
  expect_error("unknown target 'x86'", __LINE__);
  CHECK(fir_module_compile(m, "aarch64", false, 7, &as) == FIR_ERR_INVALID && as == NULL);
  expect_error("7 is not a FirOs", __LINE__);
  fir_module_free(m);

  /* What the backend can't compile yet is FIR_ERR_COMPILE. */
  m = cur = fir_module_new();
  FirType i128 = fir_type_int(128);
  FirFunc wide = ID(fir_func_declare(m, "wide", &i128, 1, &i128, 1));
  b = fir_func_begin(m, wide);
  FirValue z = ID(fir_builder_param(b, 0));
  ID(fir_func_ret(b, &z, 1));
  OK(fir_func_end(b));
  CHECK(fir_module_compile(m, "aarch64", false, FIR_OS_DARWIN, &as) == FIR_ERR_COMPILE);
  expect_error("@wide: i128 is wider than 64 bits, which the AArch64 backend doesn't support yet",
               __LINE__);
  fir_module_free(m);
}

/* Exceptions in each layer. HFIR: @thrower throws a pointer to @err when its argument is 0;
 * @catch catches it with cf.try and loads what it points to; @uncaught lets it leave (the run's
 * outcome is `threw`). MFIR: calls name a handler block (func.invoke, func.invoke.indirect).
 * LFIR: the exception slot's ops. The HFIR module also lowers, optimizes, and compiles. */
static FirTarget to(FirRegion block, const FirValue *args, size_t nargs);

static void exceptions(void) {
  FirModule *m = cur = fir_module_new();
  FirType i1 = fir_type_int(1), i32 = fir_type_int(32), ptr = FIR_TYPE_PTR;
  FirGlobal err = ID(fir_global_declare(m, "err", i32, false, 4, ID(fir_init_int(m, 7))));
  FirFunc thrower = ID(fir_func_declare(m, "thrower", &i32, 1, &i32, 1));
  FirFunc catcher = ID(fir_func_declare(m, "catch", &i32, 1, &i32, 1));
  FirFunc uncaught = ID(fir_func_declare(m, "uncaught", &i32, 1, &i32, 1));

  FirBuilder *b = fir_func_begin(m, thrower);
  FirValue k = ID(fir_builder_param(b, 0));
  OK(fir_value_set_name(b, k, "k"));
  FirValue zero = ID(fir_int_const(b, i32, 0));
  FirValue is0 = ID(fir_int_cmp(b, FIR_PRED_EQ, k, zero));
  FirOp ifop = ID(fir_cf_if_begin(b, NULL, 0, is0));
  OK(fir_position_at_end(b, ID(fir_op_region(b, ifop, 0))));
  FirValue e = ID(fir_mem_global(b, err));
  ID(fir_exn_throw(b, e));
  OK(fir_position_at_end(b, ID(fir_op_region(b, ifop, 1))));
  ID(fir_cf_yield(b, NULL, 0));
  OK(fir_position_at_end(b, fir_builder_entry(b)));
  /* What is thrown is a pointer. */
  CHECK(fir_exn_throw(b, k) == FIR_INVALID);
  ID(fir_func_ret(b, &k, 1));
  OK(fir_func_end(b));

  b = fir_func_begin(m, catcher);
  k = ID(fir_builder_param(b, 0));
  OK(fir_value_set_name(b, k, "k"));
  FirOp tryop = ID(fir_cf_try_begin(b, &i32, 1));
  OK(fir_position_at_end(b, ID(fir_op_region(b, tryop, 0))));
  FirValue v = ID(fir_op_result(b, ID(fir_func_call(b, thrower, &k, 1)), 0));
  ID(fir_cf_yield(b, &v, 1));
  FirRegion handler = ID(fir_op_region(b, tryop, 1));
  FirValue ex = ID(fir_region_param(b, handler, 0));
  OK(fir_value_set_name(b, ex, "e"));
  OK(fir_position_at_end(b, handler));
  FirValue x = ID(fir_mem_load(b, i32, ex, 4));
  ID(fir_cf_yield(b, &x, 1));
  OK(fir_position_at_end(b, fir_builder_entry(b)));
  FirValue r = ID(fir_op_result(b, tryop, 0));
  ID(fir_func_ret(b, &r, 1));
  OK(fir_func_end(b));

  b = fir_func_begin(m, uncaught);
  k = ID(fir_builder_param(b, 0));
  v = ID(fir_op_result(b, ID(fir_func_call(b, thrower, &k, 1)), 0));
  ID(fir_func_ret(b, &v, 1));
  OK(fir_func_end(b));
  OK(fir_module_verify(m));

  const char *three[] = {"3"}, *zero_arg[] = {"0"};
  expect_run(m, "catch", three, 1, "returned i32 3");
  expect_run(m, "catch", zero_arg, 1, "returned i32 7");
  expect_run(m, "uncaught", zero_arg, 1, "threw ptr #1");

  /* Lowered: cf.try is a cf.blocks whose handler block the call names. */
  FirModule *l = NULL;
  OK(fir_module_lower(m, &l));
  CHECK(l != NULL);
  if (l != NULL) {
    char *text = fir_module_print(l, false);
    CHECK(text != NULL && strstr(text, "func.invoke @thrower(%k) unwind ^.x1") != NULL);
    fir_string_free(text);
    expect_run(l, "catch", zero_arg, 1, "returned i32 7");
    expect_run(l, "uncaught", zero_arg, 1, "threw ptr #1");
    FirModule *o = NULL;
    OK(fir_module_optimize(l, &o));
    CHECK(o != NULL);
    if (o != NULL) {
      expect_run(o, "catch", zero_arg, 1, "returned i32 7");
      expect_run(o, "catch", three, 1, "returned i32 3");
      fir_module_free(o);
    }
    fir_module_free(l);
  }
  char *as = NULL;
  OK(fir_module_compile(m, "aarch64", true, FIR_OS_LINUX, &as));
  CHECK(as != NULL && strstr(as, "__fir_exn") != NULL);
  fir_string_free(as);
  fir_module_free(m);

  /* MFIR: @handle calls @thrower directly or through a pointer, naming block ^h. */
  m = cur = fir_module_new();
  OK(fir_module_set_layer(m, FIR_LAYER_MFIR, NULL));
  err = ID(fir_global_declare(m, "err", i32, false, 4, ID(fir_init_int(m, 7))));
  thrower = ID(fir_func_declare(m, "thrower", &i32, 1, &i32, 1));
  FirType params[2] = {i32, i1};
  FirFunc handle = ID(fir_func_declare(m, "handle", params, 2, &i32, 1));
  b = fir_func_begin(m, thrower);
  k = ID(fir_builder_param(b, 0));
  zero = ID(fir_int_const(b, i32, 0));
  is0 = ID(fir_int_cmp(b, FIR_PRED_EQ, k, zero));
  ifop = ID(fir_cf_if_begin(b, NULL, 0, is0));
  OK(fir_position_at_end(b, ID(fir_op_region(b, ifop, 0))));
  ID(fir_exn_throw(b, ID(fir_mem_global(b, err))));
  OK(fir_position_at_end(b, ID(fir_op_region(b, ifop, 1))));
  ID(fir_cf_yield(b, NULL, 0));
  OK(fir_position_at_end(b, fir_builder_entry(b)));
  ID(fir_func_ret(b, &k, 1));
  OK(fir_func_end(b));

  b = fir_func_begin(m, handle);
  k = ID(fir_builder_param(b, 0));
  FirValue indirect = ID(fir_builder_param(b, 1));
  FirValue fp = ID(fir_func_addr(b, thrower));
  FirOp blocks = ID(fir_cf_blocks_begin(b, &i32, 1, false));
  FirRegion entry = ID(fir_block_new(b, blocks, "entry", NULL, 0));
  FirRegion dir = ID(fir_block_new(b, blocks, "dir", NULL, 0));
  FirRegion ind = ID(fir_block_new(b, blocks, "ind", NULL, 0));
  FirRegion h = ID(fir_block_new(b, blocks, "h", &ptr, 1));
  OK(fir_position_at_end(b, entry));
  ID(fir_cf_cond_br(b, indirect, to(ind, NULL, 0), to(dir, NULL, 0)));
  OK(fir_position_at_end(b, dir));
  v = ID(fir_op_result(b, ID(fir_func_invoke(b, thrower, &k, 1, to(h, NULL, 0))), 0));
  ID(fir_cf_yield(b, &v, 1));
  OK(fir_position_at_end(b, ind));
  FirType sig = ID(fir_type_func(m, &i32, 1, &i32, 1));
  v = ID(fir_op_result(b, ID(fir_func_invoke_indirect(b, sig, fp, &k, 1, to(h, NULL, 0))), 0));
  ID(fir_cf_yield(b, &v, 1));
  OK(fir_position_at_end(b, h));
  x = ID(fir_mem_load(b, i32, ID(fir_region_param(b, h, 0)), 4));
  FirValue z = ID(fir_int_const(b, i32, 0));
  FirValue neg = ID(fir_int_arith(b, FIR_ARITH_OP_SUB, FIR_OVF_WRAP, z, x));
  ID(fir_cf_yield(b, &neg, 1));
  OK(fir_blocks_end(b, blocks));
  OK(fir_position_at_end(b, fir_builder_entry(b)));
  r = ID(fir_op_result(b, blocks, 0));
  ID(fir_func_ret(b, &r, 1));
  OK(fir_func_end(b));
  OK(fir_module_verify(m));
  const char *dir0[] = {"0", "0"}, *ind0[] = {"0", "1"}, *ind4[] = {"4", "1"};
  expect_run(m, "handle", dir0, 2, "returned i32 -7");
  expect_run(m, "handle", ind0, 2, "returned i32 -7");
  expect_run(m, "handle", ind4, 2, "returned i32 4");
  fir_module_free(m);

  /* LFIR: @raise makes @err pending and returns; @take checks after the call and takes it. */
  m = cur = fir_module_new();
  OK(fir_module_set_layer(m, FIR_LAYER_LFIR, "aarch64"));
  err = ID(fir_global_declare(m, "err", i32, false, 4, ID(fir_init_int(m, 7))));
  FirFunc raise = ID(fir_func_declare(m, "raise", NULL, 0, &i32, 1));
  FirFunc take = ID(fir_func_declare(m, "take", NULL, 0, &i32, 1));
  b = fir_func_begin(m, raise);
  FirOp code = ID(fir_aarch64_code_begin(b));
  OK(fir_position_at_end(b, ID(fir_block_new(b, code, "entry", NULL, 0))));
  ID(fir_aarch64_adrl(b, 0, err));
  ID(fir_aarch64_exn_set(b, 0));
  ID(fir_aarch64_ret(b));
  OK(fir_blocks_end(b, code));
  OK(fir_func_end(b));
  b = fir_func_begin(m, take);
  code = ID(fir_aarch64_code_begin(b));
  entry = ID(fir_block_new(b, code, "entry", NULL, 0));
  FirRegion land = ID(fir_block_new(b, code, "land", NULL, 0));
  FirRegion none = ID(fir_block_new(b, code, "none", NULL, 0));
  OK(fir_position_at_end(b, entry));
  ID(fir_aarch64_bl(b, raise));
  ID(fir_aarch64_b_exn(b, to(land, NULL, 0), to(none, NULL, 0)));
  OK(fir_position_at_end(b, land));
  ID(fir_aarch64_exn_take(b, 1));
  ID(fir_aarch64_ldr(b, FIR_MEM_SIZE_W, 0, 1, 0));
  ID(fir_aarch64_ret(b));
  OK(fir_position_at_end(b, none));
  ID(fir_aarch64_ret(b));
  OK(fir_blocks_end(b, code));
  OK(fir_func_end(b));
  OK(fir_module_verify(m));
  expect_run(m, "raise", NULL, 0, "threw ptr #1");
  expect_run(m, "take", NULL, 0, "returned i32 7");
  fir_module_free(m);
}

/* Layout queries: a frontend checks its own layout (such as Clang's) against FIR's. */
static void layout(void) {
  FirModule *m = cur = fir_module_new();
  FirType i8 = fir_type_int(8), i32 = fir_type_int(32), i64 = fir_type_int(64);
  /* struct<C>{i8, i64, i32}: offsets 0, 8, 16; size 24, alignment 8. */
  FirType fields[3] = {i8, i64, i32};
  FirType s = ID(fir_type_struct(m, FIR_POLICY_C, fields, 3));
  uint64_t size = 0, off = 0;
  uint32_t align = 0;
  OK(fir_type_layout(m, s, &size, &align));
  CHECK(size == 24 && align == 8);
  uint64_t want[3] = {0, 8, 16};
  for (uint32_t i = 0; i < 3; i++) {
    OK(fir_type_field_offset(m, s, i, &off));
    CHECK(off == want[i]);
  }
  /* A zero-length array adds alignment and no size; arrays and scalars have layouts too. */
  FirType aligned[2] = {ID(fir_type_array(m, 0, i64)), i8};
  OK(fir_type_layout(m, ID(fir_type_struct(m, FIR_POLICY_C, aligned, 2)), &size, &align));
  CHECK(size == 8 && align == 8);
  OK(fir_type_layout(m, ID(fir_type_array(m, 3, s)), &size, &align));
  CHECK(size == 72 && align == 8);
  OK(fir_type_layout(m, FIR_TYPE_PTR, &size, NULL));
  CHECK(size == 8);
  /* Packed structs. */
  FirType p = ID(fir_type_struct(m, FIR_POLICY_PACKED, fields, 3));
  OK(fir_type_field_offset(m, p, 2, &off));
  CHECK(off == 9);
  /* No field 3, and function types have no layout. */
  CHECK(fir_type_field_offset(m, s, 3, &off) == FIR_ERR_INVALID);
  expect_error("struct<C>{i8, i64, i32} has no field 3", __LINE__);
  CHECK(fir_type_layout(m, ID(fir_type_func(m, &i32, 1, NULL, 0)), &size, &align) ==
        FIR_ERR_INVALID);
  expect_error("func<(i32)> has no layout in memory", __LINE__);
  fir_module_free(m);
  /* Another data layout. */
  FirModule *m32 = cur = fir_module_new();
  OK(fir_module_set_space(m32, 32, 32, 0, NULL, 0));
  FirType pi[2] = {FIR_TYPE_PTR, i64};
  OK(fir_type_layout(m32, ID(fir_type_struct(m32, FIR_POLICY_C, pi, 2)), &size, &align));
  CHECK(size == 16 && align == 8);
  fir_module_free(m32);
}

int main(void) {
  CHECK(fir_api_version() == FIR_API_VERSION);
  blocks_loop();
  memory();
  globals_and_calls();
  control_and_ints();
  errors();
  lfir();
  building_blocks();
  exceptions();
  layout();
  if (failures > 0) {
    fprintf(stderr, "%d checks failed\n", failures);
    return 1;
  }
  puts("ok");
  return 0;
}
