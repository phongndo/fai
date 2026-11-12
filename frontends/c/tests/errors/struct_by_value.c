/* Structs and unions by value that FIR can't pass as GCC does: a 16-byte aligned HFA (GCC puts
 * it on the stack 16-byte aligned), a 16-byte aligned struct or floats beside a zero-length
 * array through `...` (FIR's variadic composites have neither), and a struct holding a va_list
 * (its cursor). */
#include <stdarg.h>

struct h16 { _Alignas(16) double a; double b; };
struct al16 { _Alignas(16) long a; };
struct holder { va_list ap; int n; };
struct z0 { float a; float none[0]; };

double hfa16(struct h16 x) { return x.a; }

void sink(int n, ...);
void pass(struct al16 *p) { sink(1, *p); }

long read(int n, ...) {
  va_list ap;
  va_start(ap, n);
  struct al16 a = va_arg(ap, struct al16);
  va_end(ap);
  return a.a;
}

int count(struct holder h) { return h.n; }

void pass_z0(struct z0 z) { sink(2, z); }

int main(void) { return 0; }

// expect: 12:8: 16-byte aligned homogeneous float aggregates by value
// expect: 15:37: 16-byte aligned structs and unions as variadic arguments
// expect: 20:19: 16-byte aligned structs and unions as variadic arguments
// expect: 25:5: structs and unions holding a 'va_list' by value
// expect: 27:37: structs of floats with a zero-length array as variadic arguments
