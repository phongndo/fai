// error: extern @f: read(args) is listed twice
extern func @f(ptr) effects[read(args), write(args), read(args)] assume
