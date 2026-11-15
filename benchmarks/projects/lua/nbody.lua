-- Floating-point arithmetic on table fields.
local sqrt = math.sqrt
local PI = math.pi local SOLAR = 4 * PI * PI local DAYS = 365.24
local function body(x, y, z, vx, vy, vz, m)
  return { x = x, y = y, z = z, vx = vx * DAYS, vy = vy * DAYS, vz = vz * DAYS, m = m * SOLAR }
end
local bodies = {
  body(0, 0, 0, 0, 0, 0, 1),
  body(4.84143144246472090e+00, -1.16032004402742839e+00, -1.03622044471123109e-01,
       1.66007664274403694e-03, 7.69901118419740425e-03, -6.90460016972063023e-05, 9.54791938424326609e-04),
  body(8.34336671824457987e+00, 4.12479856412430479e+00, -4.03523417114321381e-01,
       -2.76742510726862411e-03, 4.99852801234917238e-03, 2.30417297573763929e-05, 2.85885980666130812e-04),
  body(1.28943695621391310e+01, -1.51111514016986312e+01, -2.23307578892655734e-01,
       2.96460137564761618e-03, 2.37847173959480950e-03, -2.96589568540237556e-05, 4.36624404335156298e-05),
  body(1.53796971148509165e+01, -2.59193146099879641e+01, 1.79258772950371181e-01,
       2.68067772490389322e-03, 1.62824170038242295e-03, -9.51592254519715870e-05, 5.15138902046611451e-05),
}
local px, py, pz = 0, 0, 0
for _, b in ipairs(bodies) do px = px + b.vx * b.m py = py + b.vy * b.m pz = pz + b.vz * b.m end
bodies[1].vx, bodies[1].vy, bodies[1].vz = -px / SOLAR, -py / SOLAR, -pz / SOLAR
local function energy()
  local e = 0
  for i = 1, #bodies do
    local a = bodies[i]
    e = e + 0.5 * a.m * (a.vx * a.vx + a.vy * a.vy + a.vz * a.vz)
    for j = i + 1, #bodies do
      local b = bodies[j]
      local dx, dy, dz = a.x - b.x, a.y - b.y, a.z - b.z
      e = e - a.m * b.m / sqrt(dx * dx + dy * dy + dz * dz)
    end
  end
  return e
end
local function advance(dt)
  local n = #bodies
  for i = 1, n do
    local a = bodies[i]
    for j = i + 1, n do
      local b = bodies[j]
      local dx, dy, dz = a.x - b.x, a.y - b.y, a.z - b.z
      local d2 = dx * dx + dy * dy + dz * dz
      local mag = dt / (d2 * sqrt(d2))
      a.vx = a.vx - dx * b.m * mag a.vy = a.vy - dy * b.m * mag a.vz = a.vz - dz * b.m * mag
      b.vx = b.vx + dx * a.m * mag b.vy = b.vy + dy * a.m * mag b.vz = b.vz + dz * a.m * mag
    end
  end
  for i = 1, n do local b = bodies[i] b.x = b.x + dt * b.vx b.y = b.y + dt * b.vy b.z = b.z + dt * b.vz end
end
local n = tonumber(arg[1]) or 100000
print(string.format("%.9f", energy()))
for _ = 1, n do advance(0.01) end
print(string.format("%.9f", energy()))
