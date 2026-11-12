/* A small 2D geometry kernel whose functions take and return structs: points (an HFA of two
 * doubles), integer points (8 bytes), segments, boxes, a segment intersection that returns a
 * hit flag with the point, a convex hull returned whole in a 1 KB struct, a polygon's area and
 * centroid returned together, and a closest pair by divide and conquer returning the pair. */
#include "fai_test.h"

typedef struct { double x, y; } pt;
typedef struct { int x, y; } ipt;
typedef struct { pt a, b; } seg;
typedef struct { pt lo, hi; } box;
typedef struct { int hit; pt at; } crossing;
typedef struct { int n; ipt v[64]; } poly;
typedef struct { double area; pt centroid; } shape;
typedef struct { double d2; ipt a, b; } pair;

static pt P(double x, double y) { return (pt){x, y}; }
static pt psub(pt a, pt b) { return P(a.x - b.x, a.y - b.y); }
static pt padd(pt a, pt b) { return P(a.x + b.x, a.y + b.y); }
static pt pscale(pt a, double k) { return P(a.x * k, a.y * k); }
static double cross(pt a, pt b) { return a.x * b.y - a.y * b.x; }
static long icross(ipt o, ipt a, ipt b) {
  return (long)(a.x - o.x) * (b.y - o.y) - (long)(a.y - o.y) * (b.x - o.x);
}
static ipt ip(int x, int y) { return (ipt){x, y}; }

static crossing intersect(seg s, seg t) {
  pt r = psub(s.b, s.a), q = psub(t.b, t.a);
  double den = cross(r, q);
  crossing none = {0, {0, 0}};
  if (den == 0) return none;
  double u = cross(psub(t.a, s.a), q) / den;
  double v = cross(psub(t.a, s.a), r) / den;
  if (u < 0 || u > 1 || v < 0 || v > 1) return none;
  return (crossing){1, padd(s.a, pscale(r, u))};
}

static box bbox(const pt *ps, int n) {
  box b = {ps[0], ps[0]};
  for (int i = 1; i < n; i++) {
    if (ps[i].x < b.lo.x) b.lo.x = ps[i].x;
    if (ps[i].y < b.lo.y) b.lo.y = ps[i].y;
    if (ps[i].x > b.hi.x) b.hi.x = ps[i].x;
    if (ps[i].y > b.hi.y) b.hi.y = ps[i].y;
  }
  return b;
}
static box grow(box b, double m) { return (box){psub(b.lo, P(m, m)), padd(b.hi, P(m, m))}; }

static int less(ipt a, ipt b) { return a.x < b.x || (a.x == b.x && a.y < b.y); }
static void sort(ipt *v, int n) {
  for (int i = 1; i < n; i++) {
    ipt k = v[i];
    int j = i - 1;
    for (; j >= 0 && less(k, v[j]); j--) v[j + 1] = v[j];
    v[j + 1] = k;
  }
}
/* Andrew's monotone chain, counter-clockwise, without collinear points. */
static poly hull(poly in) {
  sort(in.v, in.n);
  poly h = {0, {{0, 0}}};
  for (int pass = 0; pass < 2; pass++) {
    int start = h.n;
    for (int k = 0; k < in.n; k++) {
      ipt p = in.v[pass ? in.n - 1 - k : k];
      while (h.n >= start + 2 && icross(h.v[h.n - 2], h.v[h.n - 1], p) <= 0) h.n--;
      h.v[h.n++] = p;
    }
    h.n--;
  }
  return h;
}
static shape measure(poly p) {
  double a = 0, cx = 0, cy = 0;
  for (int i = 0; i < p.n; i++) {
    ipt u = p.v[i], w = p.v[(i + 1) % p.n];
    double c = (double)u.x * w.y - (double)w.x * u.y;
    a += c;
    cx += (u.x + w.x) * c;
    cy += (u.y + w.y) * c;
  }
  a /= 2;
  return (shape){a, P(cx / (6 * a), cy / (6 * a))};
}

static double d2(ipt a, ipt b) {
  double dx = a.x - b.x, dy = a.y - b.y;
  return dx * dx + dy * dy;
}
static pair better(pair p, pair q) { return q.d2 < p.d2 ? q : p; }
/* Closest pair among v[lo..hi) sorted by x. */
static pair closest(const ipt *v, int lo, int hi) {
  pair best = {1e300, {0, 0}, {0, 0}};
  if (hi - lo <= 3) {
    for (int i = lo; i < hi; i++)
      for (int j = i + 1; j < hi; j++) best = better(best, (pair){d2(v[i], v[j]), v[i], v[j]});
    return best;
  }
  int mid = (lo + hi) / 2;
  best = better(closest(v, lo, mid), closest(v, mid, hi));
  for (int i = lo; i < hi; i++)
    for (int j = i + 1; j < hi; j++) {
      double dx = v[j].x - v[i].x;
      if (dx * dx >= best.d2) break;
      if ((i < mid) != (j < mid)) best = better(best, (pair){d2(v[i], v[j]), v[i], v[j]});
    }
  return best;
}

int main(void) {
  seg s = {P(0, 0), P(4, 4)}, t = {P(0, 4), P(4, 0)}, u = {P(5, 0), P(6, 1)};
  crossing c = intersect(s, t);
  show("hit", c.hit);
  show_d("at x", c.at.x);
  show_d("at y", c.at.y);
  show("miss", intersect(s, u).hit);
  show("parallel", intersect(s, (seg){P(1, 0), P(5, 4)}).hit);
  show_d("hit y", intersect((seg){P(-1, 0.5), P(3, 0.5)}, (seg){P(0.25, -2), P(0.25, 9)}).at.y);

  pt ps[5] = {{1, 2}, {-3, 0.5}, {4, -1}, {0.25, 7}, {2, 2}};
  box b = grow(bbox(ps, 5), 0.5);
  show_d("box lo x", b.lo.x);
  show_d("box hi y", b.hi.y);

  poly cloud = {0, {{0, 0}}};
  unsigned seed = 12345;
  for (int i = 0; i < 60; i++) {
    seed = seed * 1103515245u + 12345u;
    int x = (int)(seed >> 16) % 41 - 20;
    seed = seed * 1103515245u + 12345u;
    int y = (int)(seed >> 16) % 41 - 20;
    cloud.v[cloud.n++] = ip(x, y);
  }
  poly h = hull(cloud);
  show("hull n", h.n);
  for (int i = 0; i < h.n; i++) {
    fai_put_long(h.v[i].x);
    fai_put_char(',');
    fai_put_long(h.v[i].y);
    fai_put_char(' ');
  }
  fai_put_char('\n');
  shape sh = measure(h);
  show_d("area", sh.area);
  show_d("centroid x", sh.centroid.x);
  show_d("centroid y", sh.centroid.y);
  show_d("square area", measure((poly){4, {{0, 0}, {3, 0}, {3, 3}, {0, 3}}}).area);

  ipt sorted[60];
  for (int i = 0; i < 60; i++) sorted[i] = cloud.v[i];
  sort(sorted, 60);
  pair p = closest(sorted, 0, 60);
  show_d("closest d2", p.d2);
  show("closest a", p.a.x * 100 + p.a.y);
  show("closest b", p.b.x * 100 + p.b.y);
  return 0;
}
