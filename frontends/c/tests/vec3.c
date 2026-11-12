/* 3D vector and matrix math by value: vectors are HFAs of three doubles (d0-d2), 3x3 matrices
 * 72-byte structs (by reference, results through x8), rays and hits nested structs. Rotations,
 * Gram-Schmidt, a matrix inverse, and a small ray caster over spheres drawn as ASCII. */
#include "fai_test.h"

typedef struct { double x, y, z; } vec3;
typedef struct { vec3 r[3]; } mat3;
typedef struct { vec3 o, d; } ray;
typedef struct { int hit; double t; vec3 n; } hit;
typedef struct { vec3 c; double r; char shade; } sphere;

static vec3 v3(double x, double y, double z) { return (vec3){x, y, z}; }
static vec3 vadd(vec3 a, vec3 b) { return v3(a.x + b.x, a.y + b.y, a.z + b.z); }
static vec3 vsub(vec3 a, vec3 b) { return v3(a.x - b.x, a.y - b.y, a.z - b.z); }
static vec3 vscale(vec3 a, double k) { return v3(a.x * k, a.y * k, a.z * k); }
static double vdot(vec3 a, vec3 b) { return a.x * b.x + a.y * b.y + a.z * b.z; }
static vec3 vcross(vec3 a, vec3 b) {
  return v3(a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x);
}
static double vlen(vec3 a) { return __builtin_sqrt(vdot(a, a)); }
static vec3 vnorm(vec3 a) { return vscale(a, 1.0 / vlen(a)); }

static mat3 mident(void) {
  mat3 m = {{{1, 0, 0}, {0, 1, 0}, {0, 0, 1}}};
  return m;
}
static mat3 mmul(mat3 a, mat3 b) {
  mat3 r;
  for (int i = 0; i < 3; i++) {
    vec3 col0 = v3(b.r[0].x, b.r[1].x, b.r[2].x);
    vec3 col1 = v3(b.r[0].y, b.r[1].y, b.r[2].y);
    vec3 col2 = v3(b.r[0].z, b.r[1].z, b.r[2].z);
    r.r[i] = v3(vdot(a.r[i], col0), vdot(a.r[i], col1), vdot(a.r[i], col2));
  }
  return r;
}
static vec3 mapply(mat3 m, vec3 v) { return v3(vdot(m.r[0], v), vdot(m.r[1], v), vdot(m.r[2], v)); }
static mat3 transpose(mat3 m) {
  mat3 t;
  t.r[0] = v3(m.r[0].x, m.r[1].x, m.r[2].x);
  t.r[1] = v3(m.r[0].y, m.r[1].y, m.r[2].y);
  t.r[2] = v3(m.r[0].z, m.r[1].z, m.r[2].z);
  return t;
}
/* A rotation about the z axis by the angle whose cosine and sine are given. */
static mat3 rotz(double c, double s) {
  mat3 m = mident();
  m.r[0] = v3(c, -s, 0);
  m.r[1] = v3(s, c, 0);
  return m;
}
static mat3 rotx(double c, double s) {
  mat3 m = mident();
  m.r[1] = v3(0, c, -s);
  m.r[2] = v3(0, s, c);
  return m;
}
static double det(mat3 m) { return vdot(m.r[0], vcross(m.r[1], m.r[2])); }
/* The inverse through the adjugate: rows of cofactors are cross products of the rows. */
static mat3 inverse(mat3 m) {
  double d = det(m);
  mat3 adj = {{vcross(m.r[1], m.r[2]), vcross(m.r[2], m.r[0]), vcross(m.r[0], m.r[1])}};
  mat3 t = transpose(adj);
  for (int i = 0; i < 3; i++) t.r[i] = vscale(t.r[i], 1.0 / d);
  return t;
}

/* Gram-Schmidt: an orthonormal basis from three independent vectors. */
static mat3 orthonormal(vec3 a, vec3 b, vec3 c) {
  vec3 e0 = vnorm(a);
  vec3 e1 = vnorm(vsub(b, vscale(e0, vdot(b, e0))));
  vec3 e2 = vnorm(vsub(vsub(c, vscale(e0, vdot(c, e0))), vscale(e1, vdot(c, e1))));
  return (mat3){{e0, e1, e2}};
}

static hit intersect(ray r, sphere s) {
  hit h = {0, 0, {0, 0, 0}};
  vec3 oc = vsub(r.o, s.c);
  double b = vdot(oc, r.d);
  double c = vdot(oc, oc) - s.r * s.r;
  double disc = b * b - c;
  if (disc < 0) return h;
  double t = -b - __builtin_sqrt(disc);
  if (t <= 1e-9) return h;
  h.hit = 1;
  h.t = t;
  h.n = vnorm(vsub(vadd(r.o, vscale(r.d, t)), s.c));
  return h;
}

static void show_v(const char *label, vec3 v) {
  print_str(label);
  print_str(": ");
  show_d("x", v.x);
  show_d("  y", v.y);
  show_d("  z", v.z);
}

int main(void) {
  vec3 a = v3(1, 2, 3), b = v3(-4, 0.5, 2);
  show_v("a+b", vadd(a, b));
  show_v("axb", vcross(a, b));
  show_d("a.b", vdot(a, b));
  show_d("|axb|", vlen(vcross(a, b)));
  show_v("norm a", vnorm(a));

  /* 3-4-5 rotations: exact cosines and sines. */
  mat3 rz = rotz(0.6, 0.8), rx = rotx(0.8, -0.6);
  mat3 m = mmul(rz, rx);
  show_d("det", det(m));
  show_v("m*a", mapply(m, a));
  show_v("m^T*m*a", mapply(mmul(transpose(m), m), a));
  mat3 skew = {{{2, 1, 0}, {0, 3, 1}, {1, 0, 4}}};
  mat3 inv = inverse(skew);
  show_d("det skew", det(skew));
  show_v("inv row 0", inv.r[0]);
  show_v("skew*inv*b", mapply(mmul(skew, inv), b));
  mat3 q = orthonormal(v3(1, 1, 0), v3(1, 0, 1), v3(0, 1, 1));
  show_d("q0.q1", vdot(q.r[0], q.r[1]));
  show_d("q1.q2", vdot(q.r[1], q.r[2]));
  show_d("|q2|", vlen(q.r[2]));
  show_d("det q", det(q));

  sphere scene[3] = {
      {{0, 0, 5}, 2.0, '#'},
      {{-2.5, 1, 7}, 1.5, '+'},
      {{2, -1.5, 4}, 0.75, 'o'},
  };
  vec3 light = vnorm(v3(-1, 1, -1));
  long lit = 0;
  for (int row = 0; row < 20; row++) {
    for (int col = 0; col < 40; col++) {
      ray r = {v3(0, 0, 0), vnorm(v3((col - 20) / 10.0, (10 - row) / 5.0, 2.0))};
      hit best = {0, 1e30, {0, 0, 0}};
      char ch = '.';
      for (int i = 0; i < 3; i++) {
        hit h = intersect(r, scene[i]);
        if (h.hit && h.t < best.t) {
          best = h;
          ch = scene[i].shade;
        }
      }
      if (best.hit && vdot(best.n, light) > 0.5) {
        ch = '*';
        lit++;
      }
      fai_put_char(ch);
    }
    fai_put_char('\n');
  }
  show("lit", lit);
  return 0;
}
