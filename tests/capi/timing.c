/* The timing report through the C API (version 1.7): with FIR_TIME set, fir_time_report gives
 * the library's phases and the caller's own (fir_time_record), and starts afresh after each
 * report; bad arguments to fir_time_record are ignored.
 *
 * sdk/c/tests/c.rs compiles this file against include/fir.h and the static library and runs
 * it. It prints "ok" and exits 0 when every check passes. FIR_TIME is read once, at the first
 * timed call, so this sets it before anything else. */

#define _POSIX_C_SOURCE 200809L /* setenv */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "fir.h"

static int failures = 0;

#define CHECK(cond)                                                                                \
  do {                                                                                             \
    if (!(cond)) {                                                                                 \
      fprintf(stderr, "%s:%d: check failed: %s\n", __FILE__, __LINE__, #cond);                     \
      failures++;                                                                                  \
    }                                                                                              \
  } while (0)

int main(void) {
  setenv("FIR_TIME", "1", 1);
  FirModule *m = NULL;
  char *err = NULL;
  CHECK(fir_module_parse("func @add(%x: i64, %y: i64) -> i64 {\n"
                         "  %s: i64 = int.add.wrap %x, %y\n"
                         "  func.ret %s\n"
                         "}\n",
                         &m, &err) == FIR_OK);
  fir_string_free(err);
  char *asm_text = NULL;
  CHECK(fir_module_compile(m, "aarch64", true, FIR_OS_LINUX, &asm_text) == FIR_OK);
  CHECK(asm_text != NULL && strstr(asm_text, "add:") != NULL);
  fir_string_free(asm_text);
  fir_time_record("frontend: parse C", 0.002);
  fir_time_record("frontend: parse C", 0.001);
  /* Ignored: no name, a negative or infinite time. */
  fir_time_record(NULL, 1.0);
  fir_time_record("negative", -1.0);
  fir_time_record("infinite", 1.0 / 0.0);

  char *report = fir_time_report();
  CHECK(report != NULL);
  if (report) {
    const char *want[] = {"parse",        "verify",
                          "lower",        "opt.dce",
                          "aarch64.isel", "aarch64.regcheck *",
                          "aarch64.emit", "frontend: parse C",
                          "total"};
    for (size_t i = 0; i < sizeof want / sizeof want[0]; i++) {
      if (!strstr(report, want[i])) {
        fprintf(stderr, "the report lacks '%s':\n%s", want[i], report);
        failures++;
      }
    }
    /* The caller's phase ran twice, 3 ms in all: "fir: time: MS SHARE% CALLS NAME". */
    const char *line = strstr(report, "frontend: parse C");
    while (line && line > report && line[-1] != '\n')
      line--;
    double ms = 0;
    int share = 0, calls = 0;
    CHECK(line && sscanf(line, "fir: time: %lf %d%% %d", &ms, &share, &calls) == 3);
    CHECK(calls == 2 && ms > 2.999 && ms < 3.001);
    CHECK(strstr(report, "negative") == NULL && strstr(report, "infinite") == NULL);
    fir_string_free(report);
  }
  /* Recording started afresh: only what happens next. */
  fir_time_record("second", 0.5);
  report = fir_time_report();
  CHECK(report != NULL && strstr(report, "second") != NULL &&
        strstr(report, "frontend: parse C") == NULL && strstr(report, "aarch64.isel") == NULL);
  fir_string_free(report);
  fir_module_free(m);
  if (failures > 0) {
    fprintf(stderr, "%d checks failed\n", failures);
    return 1;
  }
  puts("ok");
  return 0;
}
