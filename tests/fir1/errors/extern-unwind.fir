// error: extern @f: unwinding out of an external function is not supported yet
extern func @f() effects[unwind] assume
