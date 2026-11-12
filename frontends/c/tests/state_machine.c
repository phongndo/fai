/* A switch-heavy tokenizer and evaluator: a character-class state machine splits an
 * arithmetic expression into tokens, and a precedence-climbing parser evaluates it. */
#include "fai_test.h"

enum kind { NUM, PLUS, MINUS, STAR, SLASH, LPAREN, RPAREN, END, ERROR };
struct token { enum kind kind; long value; };

static struct token toks[64];
static int ntoks, pos;

static void tokenize(const char *s) {
  enum { START, IN_NUMBER } state = START;
  long v = 0;
  ntoks = 0;
  for (;; s++) {
    char c = *s;
    switch (state) {
    case IN_NUMBER:
      if (c >= '0' && c <= '9') {
        v = v * 10 + (c - '0');
        continue;
      }
      toks[ntoks++] = (struct token){NUM, v};
      state = START;
      /* fall through: c starts the next token */
    case START:
      switch (c) {
      case ' ': case '\t': break;
      case '+': toks[ntoks++] = (struct token){PLUS, 0}; break;
      case '-': toks[ntoks++] = (struct token){MINUS, 0}; break;
      case '*': toks[ntoks++] = (struct token){STAR, 0}; break;
      case '/': toks[ntoks++] = (struct token){SLASH, 0}; break;
      case '(': toks[ntoks++] = (struct token){LPAREN, 0}; break;
      case ')': toks[ntoks++] = (struct token){RPAREN, 0}; break;
      case 0: toks[ntoks++] = (struct token){END, 0}; return;
      case '0': case '1': case '2': case '3': case '4':
      case '5': case '6': case '7': case '8': case '9':
        v = c - '0';
        state = IN_NUMBER;
        break;
      default:
        toks[ntoks++] = (struct token){ERROR, c};
        break;
      }
    }
  }
}

static int prec(enum kind k) {
  switch (k) {
  case PLUS: case MINUS: return 1;
  case STAR: case SLASH: return 2;
  default: return 0;
  }
}

static long expr(int min);

static long primary(void) {
  struct token t = toks[pos++];
  switch (t.kind) {
  case NUM: return t.value;
  case MINUS: return -primary();
  case LPAREN: {
    long v = expr(1);
    pos++; /* ) */
    return v;
  }
  default: return 0;
  }
}

static long expr(int min) {
  long lhs = primary();
  for (;;) {
    enum kind op = toks[pos].kind;
    int p = prec(op);
    if (p < min) return lhs;
    pos++;
    long rhs = expr(p + 1);
    switch (op) {
    case PLUS: lhs += rhs; break;
    case MINUS: lhs -= rhs; break;
    case STAR: lhs *= rhs; break;
    case SLASH: lhs = rhs ? lhs / rhs : 0; break;
    default: break;
    }
  }
}

static long eval(const char *s) {
  tokenize(s);
  pos = 0;
  return expr(1);
}

int main(void) {
  const char *cases[] = {"1 + 2 * 3", "(1 + 2) * 3", "100 / 7 - 3", "-(4 - 10) * -2",
                         "2 * (3 + (4 - 1) * 5) / 3", "42", "7 - 2 - 1"};
  for (unsigned i = 0; i < sizeof cases / sizeof cases[0]; i++) {
    print_str(cases[i]);
    print_str(" = ");
    print_long(eval(cases[i]));
  }
  tokenize("12 $ 3");
  show("tokens", ntoks);
  show("error char", toks[1].kind == ERROR ? toks[1].value : -1);
  return 0;
}
