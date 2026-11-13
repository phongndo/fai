// A five-body gravity simulation with doubles: an array of structs, square roots, division.
#include <stdio.h>
#include <stdlib.h>

struct body {
  double x, y, z, vx, vy, vz, mass;
};

#define NB 5
static struct body bodies[NB] = {
    {0, 0, 0, 0, 0, 0, 39.47841760435743},
    {4.84, -1.16, -0.10, 0.606, 2.81, -0.025, 0.0377},
    {8.34, 4.12, -0.40, -1.01, 1.82, 0.0084, 0.0113},
    {12.89, -15.11, -0.22, 1.08, 0.868, -0.0108, 0.00172},
    {15.37, -25.91, 0.179, 0.979, 0.594, -0.0347, 0.00203},
};

static double energy(void) {
  double e = 0.0;
  for (int i = 0; i < NB; i++) {
    struct body *b = &bodies[i];
    e += 0.5 * b->mass * (b->vx * b->vx + b->vy * b->vy + b->vz * b->vz);
    for (int j = i + 1; j < NB; j++) {
      struct body *c = &bodies[j];
      double dx = b->x - c->x, dy = b->y - c->y, dz = b->z - c->z;
      e -= b->mass * c->mass / __builtin_sqrt(dx * dx + dy * dy + dz * dz);
    }
  }
  return e;
}

static void advance(double dt) {
  for (int i = 0; i < NB; i++) {
    struct body *b = &bodies[i];
    for (int j = i + 1; j < NB; j++) {
      struct body *c = &bodies[j];
      double dx = b->x - c->x, dy = b->y - c->y, dz = b->z - c->z;
      double d2 = dx * dx + dy * dy + dz * dz;
      double mag = dt / (d2 * __builtin_sqrt(d2));
      b->vx -= dx * c->mass * mag;
      b->vy -= dy * c->mass * mag;
      b->vz -= dz * c->mass * mag;
      c->vx += dx * b->mass * mag;
      c->vy += dy * b->mass * mag;
      c->vz += dz * b->mass * mag;
    }
  }
  for (int i = 0; i < NB; i++) {
    bodies[i].x += dt * bodies[i].vx;
    bodies[i].y += dt * bodies[i].vy;
    bodies[i].z += dt * bodies[i].vz;
  }
}

int main(int argc, char **argv) {
  int steps = argc > 1 ? atoi(argv[1]) : 1000;
  printf("nbody %.9f\n", energy());
  for (int s = 0; s < steps; s++)
    advance(0.01);
  printf("nbody %.9f\n", energy());
  return 0;
}
