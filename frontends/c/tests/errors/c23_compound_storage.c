/* C23's storage-class specifiers in compound literals: Clang doesn't parse them yet, so fcc
 * can't compile them (GCC 16 does). */
int *counter(void) { return &(static int){0}; }
int seven(void) { return (constexpr int){7}; }

// expect: 3:31: expected expression
// expect: 4:27: expected expression
