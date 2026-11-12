/* A small stack-machine interpreter: bytecode built by a tiny assembler with patched jump
 * targets, then run by a switch in a loop, with calls and per-frame locals. It computes
 * factorials (recursively), Fibonacci numbers, and a GCD. */
#include "fai_test.h"

enum op { PUSH, LOAD, STORE, ADD, SUB, MUL, MOD, LT, JZ, JMP, CALL, RET, PRINT, HALT, DUP };

static long code[256];
static int len;

static int emit(long x) {
  code[len] = x;
  return len++;
}
static int emit2(enum op op, long arg) {
  emit(op);
  return emit(arg);
}

struct vm {
  long stack[64];
  int sp;
  long locals[32][8];
  int ret[32];
  int fp;
};

static long run(struct vm *vm, int pc) {
  long steps = 0;
  for (;;) {
    steps++;
    long op = code[pc++];
    switch (op) {
    case PUSH: vm->stack[vm->sp++] = code[pc++]; break;
    case LOAD: vm->stack[vm->sp++] = vm->locals[vm->fp][code[pc++]]; break;
    case STORE: vm->locals[vm->fp][code[pc++]] = vm->stack[--vm->sp]; break;
    case DUP: vm->stack[vm->sp] = vm->stack[vm->sp - 1]; vm->sp++; break;
    case ADD: case SUB: case MUL: case MOD: case LT: {
      long b = vm->stack[--vm->sp], a = vm->stack[--vm->sp], r;
      switch (op) {
      case ADD: r = a + b; break;
      case SUB: r = a - b; break;
      case MUL: r = a * b; break;
      case MOD: r = a % b; break;
      default: r = a < b;
      }
      vm->stack[vm->sp++] = r;
      break;
    }
    case JZ: {
      long t = code[pc++];
      if (!vm->stack[--vm->sp]) pc = (int)t;
      break;
    }
    case JMP: pc = (int)code[pc]; break;
    case CALL: {
      int target = (int)code[pc++];
      vm->ret[++vm->fp] = pc;
      vm->locals[vm->fp][0] = vm->stack[--vm->sp];
      pc = target;
      break;
    }
    case RET: pc = vm->ret[vm->fp--]; break;
    case PRINT: print_long(vm->stack[--vm->sp]); break;
    case HALT: return steps;
    default: return -1;
    }
  }
}

int main(void) {
  int to_main = emit2(JMP, 0);
  /* fact(n): n < 2 ? 1 : n * fact(n - 1) */
  int fact = len;
  emit2(LOAD, 0);
  emit2(PUSH, 2);
  emit(LT);
  int jz = emit2(JZ, 0);
  emit2(PUSH, 1);
  emit(RET);
  code[jz] = len;
  emit2(LOAD, 0);
  emit2(LOAD, 0);
  emit2(PUSH, 1);
  emit(SUB);
  emit2(CALL, fact);
  emit(MUL);
  emit(RET);
  code[to_main] = len;
  emit2(PUSH, 10);
  emit2(CALL, fact);
  emit(PRINT);
  emit2(PUSH, 20);
  emit2(CALL, fact);
  emit(PRINT);
  /* a = 0, b = 1, i = 0; while (i < 40) { t = a + b; a = b; b = t; i++ } print a */
  emit2(PUSH, 0); emit2(STORE, 1);
  emit2(PUSH, 1); emit2(STORE, 2);
  emit2(PUSH, 0); emit2(STORE, 3);
  int loop = len;
  emit2(LOAD, 3); emit2(PUSH, 40); emit(LT);
  int exit = emit2(JZ, 0);
  emit2(LOAD, 1); emit2(LOAD, 2); emit(ADD);
  emit2(LOAD, 2); emit2(STORE, 1);
  emit2(STORE, 2);
  emit2(LOAD, 3); emit2(PUSH, 1); emit(ADD); emit2(STORE, 3);
  emit2(JMP, loop);
  code[exit] = len;
  emit2(LOAD, 1);
  emit(PRINT);
  /* gcd(1071, 462): while (b) { t = a % b; a = b; b = t } print a */
  emit2(PUSH, 1071); emit2(STORE, 4);
  emit2(PUSH, 462); emit2(STORE, 5);
  int gl = len;
  emit2(LOAD, 5);
  int gx = emit2(JZ, 0);
  emit2(LOAD, 4); emit2(LOAD, 5); emit(MOD);
  emit2(LOAD, 5); emit2(STORE, 4);
  emit2(STORE, 5);
  emit2(JMP, gl);
  code[gx] = len;
  emit2(LOAD, 4);
  emit(PRINT);
  emit(HALT);
  static struct vm vm;
  show("steps", run(&vm, 0));
  show("code length", len);
  return 0;
}
