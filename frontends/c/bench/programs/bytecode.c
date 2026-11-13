// A stack-machine interpreter: switch dispatch in a loop over an array of instruction structs.
// The program computes sum_{i<n} (i*i mod 7) plus a Fibonacci-like recurrence.
#include <stdio.h>
#include <stdlib.h>

enum op { PUSH, LOAD, STORE, ADD, SUB, MUL, MOD, LT, JZ, JMP, HALT };

struct insn {
  enum op op;
  int arg;
};

static long run(const struct insn *code, long *vars) {
  long stack[64];
  int sp = 0, pc = 0;
  for (;;) {
    struct insn in = code[pc++];
    switch (in.op) {
    case PUSH: stack[sp++] = in.arg; break;
    case LOAD: stack[sp++] = vars[in.arg]; break;
    case STORE: vars[in.arg] = stack[--sp]; break;
    case ADD: sp--; stack[sp - 1] = stack[sp - 1] + stack[sp]; break;
    case SUB: sp--; stack[sp - 1] = stack[sp - 1] - stack[sp]; break;
    case MUL: sp--; stack[sp - 1] = stack[sp - 1] * stack[sp]; break;
    case MOD: sp--; stack[sp - 1] = stack[sp - 1] % stack[sp]; break;
    case LT: sp--; stack[sp - 1] = stack[sp - 1] < stack[sp]; break;
    case JZ: if (stack[--sp] == 0) pc = in.arg; break;
    case JMP: pc = in.arg; break;
    case HALT: return vars[1];
    }
  }
}

int main(int argc, char **argv) {
  int n = argc > 1 ? atoi(argv[1]) : 1000;
  // vars: 0 = i, 1 = acc, 2 = n, 3 = a, 4 = b
  struct insn code[] = {
      /* 0 */ {LOAD, 0},  {LOAD, 2}, {LT, 0},    {JZ, 26},
      /* 4 */ {LOAD, 1},  {LOAD, 0}, {LOAD, 0},  {MUL, 0},  {PUSH, 7}, {MOD, 0}, {ADD, 0},
      /* 11 */ {STORE, 1},
      /* 12 */ {LOAD, 3}, {LOAD, 4}, {ADD, 0},   {PUSH, 1000003}, {MOD, 0},
      /* 17 */ {LOAD, 4}, {STORE, 3}, {STORE, 4},
      /* 20 */ {LOAD, 0}, {PUSH, 1}, {ADD, 0},   {STORE, 0}, {JMP, 0}, {HALT, 0},
      /* 26 */ {LOAD, 1}, {LOAD, 4}, {ADD, 0},   {STORE, 1}, {HALT, 0},
  };
  long vars[5] = {0, 0, n, 0, 1};
  printf("bytecode %ld\n", run(code, vars));
  return 0;
}
