/* A ring buffer queue of structs (copied in and out by assignment), and breadth-first search over a grid maze with it. */
#include "fai_test.h"

#define CAP 64
struct cell { int r, c; };
struct queue { struct cell items[CAP]; int head, tail, count; };

static int push(struct queue *q, int r, int c) {
  if (q->count == CAP) return 0;
  q->items[q->tail] = (struct cell){r, c};
  q->tail = (q->tail + 1) % CAP;
  q->count++;
  return 1;
}

static struct cell *pop(struct queue *q) {
  struct cell *v = &q->items[q->head];
  q->head = (q->head + 1) % CAP;
  q->count--;
  return v;
}

static const char *maze[] = {
    "S..#......",
    ".#.#.####.",
    ".#...#....",
    ".####.#.#.",
    "......#.#E",
};

int main(void) {
  static struct queue q;
  int dist[5][10];
  for (int r = 0; r < 5; r++)
    for (int c = 0; c < 10; c++) dist[r][c] = -1;
  dist[0][0] = 0;
  push(&q, 0, 0);
  int dr[] = {1, -1, 0, 0}, dc[] = {0, 0, 1, -1};
  int visited = 0, maxq = 0;
  while (q.count) {
    if (q.count > maxq) maxq = q.count;
    struct cell cur = *pop(&q);
    visited++;
    for (int k = 0; k < 4; k++) {
      int r = cur.r + dr[k], c = cur.c + dc[k];
      if (r < 0 || r >= 5 || c < 0 || c >= 10) continue;
      if (maze[r][c] == '#' || dist[r][c] >= 0) continue;
      dist[r][c] = dist[cur.r][cur.c] + 1;
      push(&q, r, c);
    }
  }
  show("visited", visited);
  show("distance to E", dist[4][9]);
  show("max queue", maxq);
  struct queue small = {0};
  int pushed = 0;
  for (int i = 0; i < 100; i++) pushed += push(&small, i, -i);
  show("pushed", pushed);
  long s = 0;
  for (int i = 0; i < 10; i++) s += pop(&small)->r;
  push(&small, 1000, 0);
  show("popped", s);
  show("count", small.count);
  return 0;
}
