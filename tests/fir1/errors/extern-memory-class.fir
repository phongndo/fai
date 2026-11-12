// error: expected args, exposed, or globals but found 'heap'
extern func @f(ptr) effects[read(heap)] assume
