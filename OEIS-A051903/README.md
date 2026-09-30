# OEIS A051903: Ordowski's questions (**) and (***) answered, with Lean proofs

**Authors:** Ansh Mishra, Aryan Senthilkumar. **License:** MIT.

`a(n)` is the maximum exponent in the prime factorization of `n` ([A051903](https://oeis.org/A051903)).
On Dec 02 2019 Thomas Ordowski asked three questions in the OEIS entry. Google DeepMind's
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) formalises them as
`OeisA51903.conjecture1`, `conjecture2` and `conjecture3` in
[`FormalConjectures/OEIS/51903.lean`](https://github.com/google-deepmind/formal-conjectures/blob/e04cc601840dd7a37f89b821a67f3a9e3c38d9c3/FormalConjectures/OEIS/51903.lean),
all marked `research open`.

This folder answers **`conjecture2`** and **`conjecture3`**:

| Statement | Question | Answer |
|---|---|---|
| `conjecture2` | Is there an odd `n` with `a(n) > 1` and `b^n ≡ b^a(n) (mod n)` for all `b`? | **No** |
| `conjecture3` | Is there an odd `n` with `a(n) > 1` and `2^n ≡ 2^a(n) (mod n)`? | **Yes**, `n = 9687963167864344937` |

`conjecture1` is equivalent to Lehmer's totient problem and is not addressed here.

## Proofs

**`conjecture2` (no).**
1. Suppose `n` is odd and `E = a(n) ≥ 2`. Choose a prime `q` with `q^E ∥ n`. Then `q` is odd, so `q ≥ 3`, and `n ≥ q^E > E`.
2. Take `b = q + 1`. From `(q+1)^n ≡ (q+1)^E (mod q^E)`, and since `q + 1` is a unit mod `q^E`, we get `(q+1)^(n−E) ≡ 1 (mod q^E)`.
3. By the lifting-the-exponent lemma, `v_q((q+1)^(n−E) − 1) = 1 + v_q(n−E)`. Hence `E ≤ 1 + v_q(n−E)`, that is, `q^(E−1) ∣ n − E`.
4. Also `q^(E−1) ∣ n`, so `q^(E−1) ∣ E`. This is impossible, because `q^(E−1) ≥ 3^(E−1) > E` for `E ≥ 2`.

**`conjecture3` (yes).**

    n = 9687963167864344937 = 7 · 631 · 881 · 3511² · 201961

- `n` is odd and `a(n) = 2`.
- `2^n ≡ 2^2 (mod n)`, since `2^(n−2) ≡ 1` modulo each prime-power factor:
  - `ord_{3511²}(2) = 1755`;
  - `ord_7(2) = 3`, `ord_631(2) = 45`, `ord_881(2) = 55` and `ord_201961(2) = 55`;
  - every one of these orders divides `n − 2`.

How the witness was found. A square factor `q² ∣ n` forces `ord_{q²}(2) = ord_q(2)`, so `q` must be a Wieferich prime:
- `q = 1093` fails, because its order `364` is even, which would force `n` to be even;
- `q = 3511` has odd order `1755` and `3511 ≡ 1 (mod 1755)`.

A search over squarefree cofactors `m` with `m ≡ 2 (mod 1755)` and `ord_r(2) ∣ n − 2` for every prime `r ∣ m` gives `m = 7 · 631 · 881 · 201961`.

## Lean 4 verification

- `lean/DMSolutions/OEIS_A051903/Core.lean` imports Mathlib only and contains a verbatim copy of the repository's `a`.
  - `not_conj2`: the negative answer.
  - `conj3_witness`: the witness. The congruence is checked by a proved-correct square-and-multiply function evaluated with `decide +kernel`. The factorisation is proved from `Nat.primeFactorsList_unique`.
- `lean/DMSolutions/OEIS_A051903/Solution.lean` imports the **unmodified** repository file and proves
  ```lean
  theorem OeisA51903.conjecture2_solved :
      answer(False) ↔ ∃ n : ℕ, Odd n ∧ 1 < a n ∧ ∀ b : ℕ, b ^ n ≡ b ^ (a n) [MOD n]
  theorem OeisA51903.conjecture3_solved :
      answer(True) ↔ ∃ n : ℕ, Odd n ∧ 1 < a n ∧ 2 ^ n ≡ 2 ^ (a n) [MOD n]
  ```
  These use the repository's own definition `OeisA51903.a`, which equals the core copy by `rfl`.
- `lean/DMSolutions/OEIS_A051903/CheckAnswer.lean` shows that `answer(False)` is `False` and `answer(True)` is `True` (both by `rfl`). It also derives the plain statements from the two theorems, and prints the repository statements next to ours.

All theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`, `native_decide` or custom axiom.

To reproduce, you need Lean v4.33.1, a formal-conjectures checkout at commit `ab0addc45f699bdd0b7cc58efa5140a72f101a9e`, and `lake exe cache get` run in the checkout. The statement file is byte-identical at `e04cc601840dd7a37f89b821a67f3a9e3c38d9c3`, the latest main at the time of writing. Then run:

```bash
bash lean/check.sh /path/to/formal-conjectures
```

The script:
1. compiles `Core.lean`;
2. rebuilds the repository statement module with the repository's own `leanOptions`;
3. compiles `Solution.lean` and `CheckAnswer.lean`;
4. prints the axioms and runs a keyword scan.

Our run is in `logs/lean_check.log` (exit 0, 104 s).

## Independent arithmetic check

`scripts/verify_witness.py` (Python 3 with sympy) does the following:
- recomputes the factorisation, `a(n)`, the congruence and all multiplicative orders;
- runs a brute-force sanity check of `conjecture2` for odd `n ≤ 200000`.

Output: `logs/verify_witness.log`.

## Prior work

As of 2026-09-30 we found no earlier answer to either question:
- **OEIS entry:** A051903 still poses (**) and (***) as open. There are no replies.
- **Related OEIS data:** A173572, the odd `n` with `2^n ≡ 4 (mod n)`, has a b-file of 722 terms up to `9.98·10^13`. None is divisible by `3511²`.
- **Formal Conjectures:** both statements are `research open` at the latest main. No open or closed PR addresses them; the only hit for "51903" is a documentation cross-reference PR.
- **Other solution repositories:** no other public solution repository mentions A051903.
- **OEIS Open benchmark** (Adamczewski, arXiv:2608.11941): it contains only the Lehmer-equivalent question (`conjecture1`), unsolved there.
- **Web search:** nothing.

## Updating Formal Conjectures

The natural change to `FormalConjectures/OEIS/51903.lean` is:
- set `conjecture2` to `answer(False)` and `conjecture3` to `answer(True)`;
- change both to `@[category research solved, AMS 11, formal_proof using lean4 at "<link to Solution.lean>"]`.
