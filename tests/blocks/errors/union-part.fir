// Unions have no layout, so they are not parts of structs or arrays.
// error: union<i8> can't be part of struct<C>{union<i8>}
func @f(%s: struct<C>{union<i8>}) {
  func.ret
}
