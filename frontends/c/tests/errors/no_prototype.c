/* A call with arguments through a declaration without a prototype. */
int f();

int main(void) { return f(1, 2); }

int f(a, b) int a, b; { return a + b; }

// expect: 4:25: calls with arguments to a function declared without a prototype
// expect: 6:5: old-style (K&R) function definitions
