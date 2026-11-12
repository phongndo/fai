/* Calls to libm (external functions with float arguments and results, some through pointers),
 * the <math.h> classification and comparison macros (Clang's float builtins, which are FIR
 * ops), and the __builtin_ functions and constants with a FIR op. */
#include "fai_test.h"
#include <math.h>

double in[] = {2.0, -2.5, 0.5, 10.0, 1e-310, -0.0, 3.75, 100.0};
float fin[] = {2.0f, -2.5f, 0.5f, 7.25f};
unsigned long snan_bits = 0x7ff0000000000001UL;

void classify(double x) {
  fai_put_long(isnan(x));
  fai_put_long(isinf(x) != 0);
  fai_put_long(isfinite(x) != 0);
  fai_put_long(isnormal(x) != 0);
  fai_put_long(signbit(x) != 0);
  fai_put_long(fpclassify(x) == FP_ZERO);
  fai_put_long(fpclassify(x) == FP_SUBNORMAL);
  fai_put_char('\n');
}

void fclassify(float x) {
  fai_put_long(isnan(x));
  fai_put_long(isinf(x) != 0);
  fai_put_long(isfinite(x) != 0);
  fai_put_long(isnormal(x) != 0);
  fai_put_long(signbit(x) != 0);
  fai_put_char('\n');
}

int main(void) {
  for (int i = 0; i < 8; i++) {
    double x = in[i];
    show_d("x", x);
    show_d("sqrt", sqrt(x));
    show_d("fabs", fabs(x));
    show_d("floor", floor(x));
    show_d("ceil", ceil(x));
    show_d("trunc", trunc(x));
    show_d("round", round(x));
    show_d("pow", pow(x, 3.0));
    show_d("pow half", pow(fabs(x), 0.5));
    show_d("exp", exp(x));
    show_d("log", log(x));
    show_d("sin", sin(x));
    show_d("cos", cos(x));
    show_d("atan2", atan2(x, 1.5));
    show_d("fmod", fmod(x, 0.75));
    show_d("hypot", hypot(x, 4.0));
    show_d("fmin", fmin(x, 1.0));
    show_d("fmax", fmax(x, 1.0));
    show_d("copysign", copysign(1.0, x));
    show_d("ldexp", ldexp(x, 5));
    int e;
    double m = frexp(x, &e);
    show_d("frexp", m);
    show("exponent", e);
    double ip;
    show_d("modf", modf(x, &ip));
    show_d("modf int", ip);
    classify(x);
  }
  for (int i = 0; i < 4; i++) {
    float f = fin[i];
    show_f("sqrtf", sqrtf(f));
    show_f("fabsf", fabsf(f));
    show_f("floorf", floorf(f));
    show_f("powf", powf(f, 2.5f));
    show_f("expf", expf(f));
    fclassify(f);
  }
  classify(HUGE_VAL);
  classify(-INFINITY);
  classify(NAN);
  fclassify(-NAN);
  fclassify(HUGE_VALF);
  fclassify(1e-40f);
  /* The quiet comparisons (<math.h>'s macros for them are statement expressions under Clang,
   * which fai-cc doesn't support yet). */
  double nan = in[0] - INFINITY + INFINITY;
  show("isgreater", __builtin_isgreater(in[0], in[1]));
  show("isless", __builtin_isless(in[0], nan));
  show("islessequal", __builtin_islessequal(in[2], in[2]));
  show("isgreaterequal", __builtin_isgreaterequal(in[1], in[0]));
  show("islessgreater", __builtin_islessgreater(in[1], in[0]));
  show("isunordered", __builtin_isunordered(nan, 1.0));
  /* The builtins that are FIR ops. */
  show_d("__builtin_fabs", __builtin_fabs(in[1]));
  show_f("__builtin_fabsf", __builtin_fabsf(fin[1]));
  show_d("__builtin_sqrt", __builtin_sqrt(in[3]));
  show_f("__builtin_sqrtf", __builtin_sqrtf(fin[3]));
  show_d("__builtin_sqrt(-1)", __builtin_sqrt(-in[2]));
  show_d("__builtin_copysign", __builtin_copysign(in[3], in[5]));
  show_f("__builtin_copysignf", __builtin_copysignf(fin[3], fin[1]));
  show_d("__builtin_fma", __builtin_fma(in[0], in[6], in[2]));
  show_f("__builtin_fmaf", __builtin_fmaf(fin[0], fin[3], fin[1]));
  show_d("fma", fma(0.1, 10.0, -1.0));
  show_d("0.1*10-1", in[7] / 1000 * in[3] - 1.0);
  show_d("__builtin_inf", __builtin_inf());
  show_f("__builtin_inff", __builtin_inff());
  show_d("__builtin_huge_val", __builtin_huge_val());
  show_d("__builtin_nan", __builtin_nan(""));
  show_d("__builtin_nan(0x15)", __builtin_nan("0x15"));
  show_f("__builtin_nanf(7)", __builtin_nanf("7"));
  show_d("-__builtin_nans", -__builtin_nans("3"));
  show_d("NAN", NAN);
  show_d("INFINITY", INFINITY);
  /* A signaling NaN through copysign and fabs keeps its payload and signal bit. */
  union {
    unsigned long u;
    double d;
  } s = {snan_bits};
  show_d("fabs snan", __builtin_fabs(-s.d));
  show_d("copysign snan", __builtin_copysign(s.d, -1.0));
  /* Function pointers to libm. */
  double (*fns[])(double) = {sqrt, exp, log1p, cbrt, tanh};
  for (int i = 0; i < 5; i++) show_d("fn", fns[i](in[6]));
  return 0;
}
