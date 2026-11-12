// bytes give the whole object.
// error: global @g: 2 bytes can't initialize i32, which takes 4
global @g: i32 = bytes "0102"
