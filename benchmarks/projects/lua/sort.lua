-- table.sort with a Lua comparison function, and table insertion.
local n = tonumber(arg[1]) or 200000
local seed = 42
local function rand() seed = (seed * 1103515245 + 12345) % 2147483648 return seed end
local t = {}
for i = 1, n do t[i] = rand() end
table.sort(t, function(a, b) return a > b end)
local ok = true
for i = 2, n do if t[i - 1] < t[i] then ok = false end end
local h = {}
for i = 1, n do h[t[i] % 65536] = i end
local c = 0 for _ in pairs(h) do c = c + 1 end
print(ok, t[1], t[n], c)
