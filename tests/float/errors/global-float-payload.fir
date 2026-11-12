// error: the NaN payload doesn't fit f32
global @g: struct<C>{f32} = {nan(0x800000)}
