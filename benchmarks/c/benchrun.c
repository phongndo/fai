// The native timing driver for `cbench.py time`, built as a static AArch64 binary so it runs on
// any AArch64 Linux machine with nothing installed. It refuses to time under qemu-user, the
// emulator the dev shell provides (see native_aarch64 for exactly what it can and can't tell).
//
//   benchrun RUNS WARMUP EXPECTED_STDOUT_FILE PROGRAM [ARG...]
//
// runs PROGRAM WARMUP times untimed and RUNS times timed (each with stdout to a pipe it checks
// against EXPECTED_STDOUT_FILE), and prints one JSON object: wall, user, and system seconds of
// every timed run, and the peak resident set size in KiB.
#define _GNU_SOURCE
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static char expected[1 << 16];
static size_t expected_len;

static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (double)t.tv_sec + (double)t.tv_nsec * 1e-9;
}

// The CPU's identity, from /proc/cpuinfo: "CPU implementer" and "CPU part" of the first CPU.
// Native AArch64 (also in a hardware-virtualized VM) reports the silicon's implementer: 0x41
// Arm, 0x61 Apple, 0x51 Qualcomm, and so on. qemu-user's CPU (`max`) reports 0x00, which Arm
// reserves for software, and x86 fields mean an x86 host; both are refused. What this can't tell:
// a full-system emulator modelling a named CPU (`qemu-system-aarch64 -cpu cortex-a72` under TCG)
// reports that CPU's implementer and passes. No check from inside a guest can rule that out, so
// the operator vouches for the machine, and the results record its identity (`cbench.py time`
// also records the SSH host's own CPU and Docker's server architecture).
static unsigned implementer = 0, part = 0;

static int native_aarch64(void) {
  FILE *f = fopen("/proc/cpuinfo", "r");
  if (!f)
    return 0;
  char line[4096];
  int seen = 0, x86 = 0;
  while (fgets(line, sizeof line, f)) {
    char *colon = strchr(line, ':');
    if (strncmp(line, "CPU implementer", 15) == 0 && colon && !seen) {
      implementer = (unsigned)strtoul(colon + 1, 0, 0);
      seen = 1;
    }
    if (strncmp(line, "CPU part", 8) == 0 && colon && !part)
      part = (unsigned)strtoul(colon + 1, 0, 0);
    if (strncmp(line, "vendor_id", 9) == 0)
      x86 = 1;
  }
  fclose(f);
  return seen && implementer != 0 && !x86;
}

static int run_once(char **argv, double *wall, double *user, double *sys, long *rss) {
  int fds[2];
  if (pipe(fds) != 0)
    return -1;
  double t0 = now();
  pid_t pid = fork();
  if (pid == 0) {
    dup2(fds[1], 1);
    close(fds[0]);
    close(fds[1]);
    execv(argv[0], argv);
    _exit(127);
  }
  close(fds[1]);
  // Compare the output with the expected bytes as it arrives, through EOF: a mismatch or any
  // byte past the expected ones fails the run (reading continues, so the child never blocks).
  char buf[4096];
  size_t pos = 0;
  int differs = 0;
  for (;;) {
    ssize_t k = read(fds[0], buf, sizeof buf);
    if (k < 0 && errno == EINTR)
      continue;
    if (k <= 0)
      break;
    if (!differs &&
        (pos + (size_t)k > expected_len || memcmp(buf, expected + pos, (size_t)k) != 0))
      differs = 1;
    pos += (size_t)k;
  }
  close(fds[0]);
  int status;
  struct rusage ru;
  wait4(pid, &status, 0, &ru);
  *wall = now() - t0;
  *user = (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec * 1e-6;
  *sys = (double)ru.ru_stime.tv_sec + (double)ru.ru_stime.tv_usec * 1e-6;
  *rss = ru.ru_maxrss;
  if (!WIFEXITED(status) || WEXITSTATUS(status) != 0)
    return -2;
  if (differs || pos != expected_len)
    return -3;
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 5) {
    fprintf(stderr, "usage: benchrun RUNS WARMUP EXPECTED PROGRAM [ARG...]\n");
    return 2;
  }
  if (!native_aarch64()) {
    fprintf(stderr, "benchrun: not native AArch64 (CPU implementer 0x%02x: emulated?): refusing "
                    "to time\n",
            implementer);
    return 3;
  }
  int runs = atoi(argv[1]), warmup = atoi(argv[2]);
  FILE *f = fopen(argv[3], "rb");
  if (!f) {
    fprintf(stderr, "benchrun: can't read %s\n", argv[3]);
    return 2;
  }
  expected_len = fread(expected, 1, sizeof expected, f);
  int more = fgetc(f) != EOF;
  fclose(f);
  if (more) {
    fprintf(stderr, "benchrun: %s is longer than %zu bytes\n", argv[3], sizeof expected);
    return 2;
  }
  double wall, user, sys;
  long rss;
  for (int i = 0; i < warmup; i++)
    if (run_once(argv + 4, &wall, &user, &sys, &rss) != 0) {
      fprintf(stderr, "benchrun: %s failed or printed something else\n", argv[4]);
      return 1;
    }
  printf("{\"wall\": [");
  long maxrss = 0;
  double users[256], syss[256];
  if (runs > 256)
    runs = 256;
  for (int i = 0; i < runs; i++) {
    int r = run_once(argv + 4, &wall, &user, &sys, &rss);
    if (r != 0) {
      fprintf(stderr, "benchrun: %s failed (%d)\n", argv[4], r);
      return 1;
    }
    printf("%s%.6f", i ? ", " : "", wall);
    users[i] = user;
    syss[i] = sys;
    if (rss > maxrss)
      maxrss = rss;
  }
  printf("], \"user\": [");
  for (int i = 0; i < runs; i++)
    printf("%s%.6f", i ? ", " : "", users[i]);
  printf("], \"sys\": [");
  for (int i = 0; i < runs; i++)
    printf("%s%.6f", i ? ", " : "", syss[i]);
  printf("], \"maxrss_kib\": %ld, \"cpu_implementer\": %u, \"cpu_part\": %u}\n", maxrss,
         implementer, part);
  return 0;
}
