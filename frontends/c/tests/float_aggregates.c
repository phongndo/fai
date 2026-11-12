/* Floats in memory: struct fields, arrays, globals with float initializers (signed zeros,
 * infinities, NaNs, subnormals, exact bits), static locals, compound literals, unions that pun
 * floats and integers, a struct mixing floats and bitfields, and struct copies. */
#include "fai_test.h"

struct vec3 {
  float x, y, z;
};

struct particle {
  char tag;
  double mass;
  struct vec3 pos, vel;
  float charge;
  short id;
};

struct mixed {
  unsigned flags : 3;
  float f;
  unsigned more : 5;
  double d;
};

union pun {
  double d;
  unsigned long u;
  float f[2];
  unsigned w[2];
};

double table[8] = {0.0, -0.0, 1.0 / 0.0, -1.0 / 0.0, 4.9406564584124654e-324,
                   1.7976931348623157e308, 0.1};
float ftable[] = {1.0f / 0.0f, 1.401298464e-45f, 3.40282347e38f, -0.0f, 0.3f};
struct particle world[3] = {
    {'a', 1.5, {1, 2, 3}, {0.5f, -0.5f, 0}, -1.0f, 7},
    {'b', 2.25, {-1, -2, -3}, {0, 0, 1e-3f}, 2.0f, 8},
};
struct mixed mx = {5, 1.25f, 17, -2.5};
union pun pun_global = {.d = -1.0};
union pun pun_floats = {.f = {1.5f, -2.0f}};
const double nan_global = 0.0 / 0.0;
struct vec3 *origin = &(struct vec3){0.0f, -0.0f, 0.5f};

double dot(struct vec3 *a, struct vec3 *b) { return a->x * b->x + a->y * b->y + a->z * b->z; }

void step(struct particle *p, float dt) {
  p->pos.x += p->vel.x * dt;
  p->pos.y += p->vel.y * dt;
  p->pos.z += p->vel.z * dt;
  p->mass *= 0.999;
}

double running_mean(double x) {
  static double sum = 0.0;
  static int n;
  sum += x;
  return sum / ++n;
}

int main(void) {
  for (int i = 0; i < 8; i++) show_d("table", table[i]);
  for (unsigned i = 0; i < sizeof ftable / sizeof ftable[0]; i++) show_f("ftable", ftable[i]);
  show("nan_global is nan", nan_global != nan_global);
  show_d("nan_global", nan_global);

  for (int t = 0; t < 4; t++)
    for (int i = 0; i < 3; i++) step(&world[i], 0.25f);
  for (int i = 0; i < 3; i++) {
    struct particle p = world[i];
    show("tag", p.tag);
    show_d("mass", p.mass);
    show_f("pos.x", p.pos.x);
    show_f("pos.y", p.pos.y);
    show_f("pos.z", p.pos.z);
    show_f("charge", p.charge);
    show("id", p.id);
    show_d("pos.vel", dot(&p.pos, &p.vel));
  }

  show("mx.flags", mx.flags);
  show_f("mx.f", mx.f);
  show("mx.more", mx.more);
  show_d("mx.d", mx.d);
  mx.more = 30;
  mx.f *= -4;
  struct mixed copy = mx;
  show("copy.more", copy.more);
  show_f("copy.f", copy.f);

  print_hex(pun_global.u, 16);
  fai_put_char('\n');
  print_hex(pun_floats.w[0], 8);
  print_hex(pun_floats.w[1], 8);
  fai_put_char('\n');
  union pun p;
  p.u = 0x3ff0000000000001UL;
  show_d("pun.d", p.d);
  p.d = 0.1;
  show("pun.u low", (long)(p.u & 0xffffffff));
  p.w[0] = 0x80000000u;
  p.w[1] = 0x7f800000u;
  show_f("pun.f[0]", p.f[0]);
  show_f("pun.f[1]", p.f[1]);

  show_f("origin.y", origin->y);
  struct vec3 local = {.z = 2.0f};
  show_f("local.x", local.x);
  show_f("local.z", local.z);
  float grid[3][4] = {{1, 2}, {[3] = 4.5f}};
  float total = 0;
  for (int i = 0; i < 3; i++)
    for (int j = 0; j < 4; j++) total += grid[i][j] * (i + 1);
  show_f("grid total", total);
  double *dp = (double[]){0.5, 0.25, 0.125};
  show_d("compound", dp[0] + dp[1] + dp[2]);
  for (int i = 1; i <= 5; i++) show_d("mean", running_mean(i * 1.5));
  double arr[5];
  for (int i = 0; i < 5; i++) arr[i] = 1.0 / (i + 1);
  double *q = arr + 4;
  show_d("arr", *q - q[-4]);
  return 0;
}
