-- The string library: formatting, concatenation, patterns, and interning.
local n = tonumber(arg[1]) or 100000
local parts = {}
for i = 1, n do parts[#parts + 1] = string.format("%d:%x;", i, i * 7) end
local s = table.concat(parts)
local count, sum = 0, 0
for a, b in s:gmatch("(%d+):(%x+);") do count = count + 1 sum = sum + #a + #b end
local r = s:gsub("%d", "x")
local keys = {}
for i = 1, n do keys["k" .. (i % 1000)] = (keys["k" .. (i % 1000)] or 0) + 1 end
print(count, sum, #r, s:find("999:", 1, true))
