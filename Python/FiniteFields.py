from pyfinite import ffield

F = ffield.FField(4)
a = 2
b = 14
t = F.FindDegree(b)
c = F.Multiply(a, b)
d = F.Inverse(a)
print(c, d, t)

for i in range(1, 5):
    print(F.Inverse(i))

if c > d:
    print(c)
else:
    print(d)