"""Independent arithmetic checks for the A051903 solutions (Python 3 + sympy)."""
from sympy import factorint, n_order

# conjecture3: the witness
n = 9687963167864344937
f = factorint(n)
a = max(f.values())
print("n =", n, "=", " * ".join(f"{p}^{e}" if e > 1 else str(p) for p, e in sorted(f.items())))
print("odd:", n % 2 == 1, "| a(n) =", a, "| 2^n == 2^a(n) (mod n):", pow(2, n, n) == pow(2, a, n))
for p in sorted(f):
    q = p ** f[p]
    print(f"  ord_{q}(2) = {n_order(2, q)} divides n - 2: {(n - 2) % n_order(2, q) == 0}")

# conjecture2: no odd n <= 2*10^5 with a(n) > 1 and b^n == b^a(n) (mod n) for b = 2..59
hits = [N for N in range(9, 200001, 2)
        if max(factorint(N).values()) > 1
        and all(pow(b, N, N) == pow(b, max(factorint(N).values()), N) for b in range(2, 60))]
print("conjecture2 brute force, odd n <= 200000:", hits if hits else "no candidates")
