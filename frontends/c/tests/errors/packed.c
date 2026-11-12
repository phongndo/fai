/* Packed structs: FIR's struct<packed> exists, but fai-cc doesn't map them yet. */
struct __attribute__((packed)) header {
  char kind;
  int length;
};

int main(void) {
  struct header h = {1, 2};
  return h.length;
}

// expect: 2:32: packed structs
