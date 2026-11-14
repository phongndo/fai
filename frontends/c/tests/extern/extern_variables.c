/* The variables extern_variables.c uses, defined here and compiled by the reference compiler. */
long ext_counter = 40;
int ext_table[4] = {1, 2, 3, 4};
const char ext_name[] = "external";
struct ext_pair {
  int a;
  long b;
} ext_pair = {5, 6};
int *ext_ptr = &ext_table[2];

/* A constructor that runs before main reads a pointer extern_variables.c initializes with the
 * address of a variable defined here: fcc fills it before every program constructor. */
extern long *counter_ptr;
int ext_seen_early;
__attribute__((constructor(101))) static void early(void) {
  ext_seen_early = counter_ptr == &ext_counter && *counter_ptr == 40;
}
