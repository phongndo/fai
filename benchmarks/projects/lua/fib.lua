-- Recursive calls: the call/return path of the VM.
local function fib(n) if n < 2 then return n end return fib(n - 1) + fib(n - 2) end
local n = tonumber(arg[1]) or 27
print(fib(n))
