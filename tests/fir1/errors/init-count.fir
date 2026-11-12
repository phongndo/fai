// One initializer per field.
// error: global @g: struct<C>{i32, i32} takes 2 initializers but got 1
global @g: struct<C>{i32, i32} = {1}
