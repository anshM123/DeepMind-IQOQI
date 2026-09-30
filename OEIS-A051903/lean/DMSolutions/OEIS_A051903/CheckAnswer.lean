import DMSolutions.OEIS_A051903.Solution

-- The filled-in answers elaborate to the propositions `False` and `True` themselves.
example : (answer(False) : Prop) = False := rfl
example : (answer(True) : Prop) = True := rfl
-- Hence conjecture2_solved really proves the negation of the repository's existence claim:
example : ¬ ∃ n : ℕ, Odd n ∧ 1 < OeisA51903.a n ∧ ∀ b : ℕ, b ^ n ≡ b ^ (OeisA51903.a n) [MOD n] :=
  fun h => OeisA51903.conjecture2_solved.mpr h
example : ∃ n : ℕ, Odd n ∧ 1 < OeisA51903.a n ∧ 2 ^ n ≡ 2 ^ (OeisA51903.a n) [MOD n] :=
  OeisA51903.conjecture3_solved.mp trivial
-- Repository statements (with their answer placeholder) and ours, printed for comparison:
#check @OeisA51903.conjecture2
#check @OeisA51903.conjecture2_solved
#check @OeisA51903.conjecture3
#check @OeisA51903.conjecture3_solved
