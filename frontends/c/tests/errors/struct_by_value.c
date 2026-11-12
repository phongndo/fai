/* Structs passed and returned by value come with track A. */
struct pair { int a, b; };

int first(struct pair p) { return p.a; }
struct pair make(void) { struct pair p = {1, 2}; return p; }

int main(void) {
  struct pair *q = 0;
  return q ? first(*q) : 0;
}

// expect: 4:5: structs and unions passed by value (track A)
// expect: 5:13: structs and unions returned by value (track A)
// expect: 9:20: structs and unions passed by value (track A)
