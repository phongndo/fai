/* C23's interchange floating types (Annex H, optional): Clang doesn't provide _Float32 or
 * _Float64 in C, so fcc can't compile them (GCC 16 does). */
_Float32 single;
_Float64 twice(_Float64 x) { return x * 2; }

// expect: 3:1: unknown type name '_Float32'
// expect: 4:1: unknown type name '_Float64'
// expect: 4:16: unknown type name '_Float64'
