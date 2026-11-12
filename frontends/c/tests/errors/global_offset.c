/* A global's initializer that points into the middle of another object: FIR's initializers
 * name only the start of a global. */
int table[4] = {1, 2, 3, 4};
int *third = &table[2];
const char *tail = "abcdef" + 3;

int main(void) { return *third + *tail; }

// expect: 4:14: a global's initializer pointing inside another object
// expect: 5:20: a global's initializer pointing inside another object
