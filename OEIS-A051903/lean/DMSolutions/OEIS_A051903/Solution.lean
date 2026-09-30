import FormalConjectures.OEIS.«51903»
import DMSolutions.OEIS_A051903.Core

/-!
# Solutions of `OeisA51903.conjecture2` and `OeisA51903.conjecture3`

The statements are those of `FormalConjectures/OEIS/51903.lean` (unmodified), with the answer
filled in, stated with the repository's own definition `OeisA51903.a`.

* `conjecture2`: answer **False** (Thomas Ordowski's question (**) has a negative answer).
* `conjecture3`: answer **True**, witnessed by `n = 9687963167864344937 = 7 * 631 * 881 * 3511 ^ 2 * 201961`
  (Thomas Ordowski's question (***) has a positive answer).
-/

namespace OeisA51903

/-- The repository's `a` is definitionally the copy used in `A051903Core`. -/
theorem a_eq_core : a = A051903Core.a := rfl

/-- `OeisA51903.conjecture2` with the answer `False`. -/
theorem conjecture2_solved :
    answer(False) ↔ ∃ n : ℕ, Odd n ∧ 1 < a n ∧ ∀ b : ℕ, b ^ n ≡ b ^ (a n) [MOD n] := by
  rw [a_eq_core]
  exact ⟨False.elim, fun h => A051903Core.not_conj2 h⟩

/-- `OeisA51903.conjecture3` with the answer `True`. -/
theorem conjecture3_solved :
    answer(True) ↔ ∃ n : ℕ, Odd n ∧ 1 < a n ∧ 2 ^ n ≡ 2 ^ (a n) [MOD n] := by
  rw [a_eq_core]
  exact ⟨fun _ => A051903Core.conj3_witness, fun _ => trivial⟩

end OeisA51903

#print axioms OeisA51903.conjecture2_solved
#print axioms OeisA51903.conjecture3_solved
