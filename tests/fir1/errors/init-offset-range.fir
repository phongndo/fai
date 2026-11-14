// An offset in an initializer must fit in a pointer.
// error: global @p: the offset 340282366920938463463374607431768211457 does not fit in a ptr
global @g: i8 = 7
global @p: ptr = offset(@g, 340282366920938463463374607431768211457)
