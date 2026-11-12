// bytes take lowercase hex digits, two per byte.
// error: 3:24: expected two lowercase hex digits per byte
global @g: i16 = bytes "0A0B"
