// error: extern @f: struct<C>{i32, i32} is not a value type
extern func @f(struct<C>{i32, i32}) effects[] assume
