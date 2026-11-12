/* Statement expressions, _Complex, and ++ on _Bool, each reported, in one file: the other
 * functions still compile, and every error is listed. */
int ok(int x) { return x + 1; }

int stmt_expr(int x) { return ({ int y = x; y * 2; }); }

int complex_part(void) {
  _Complex double z = 0;
  return (int)__real__ z;
}

int bool_inc(void) {
  _Bool b = 0;
  b++;
  return b;
}

int main(void) { return ok(1); }

// expect: 5:31: statement expressions
// expect: 8:19: '_Complex'
// expect: 14:4: '++' and '--' on '_Bool'
