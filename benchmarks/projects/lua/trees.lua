-- Allocation and the garbage collector: build and walk binary trees.
local function make(d) if d == 0 then return {} end d = d - 1 return { make(d), make(d) } end
local function check(t) if t[1] then return 1 + check(t[1]) + check(t[2]) end return 1 end
local maxd = tonumber(arg[1]) or 14
local total = 0
for d = 4, maxd, 2 do
  local iters = 1 << (maxd - d + 4)
  for _ = 1, iters do total = total + check(make(d)) end
end
print(total)
