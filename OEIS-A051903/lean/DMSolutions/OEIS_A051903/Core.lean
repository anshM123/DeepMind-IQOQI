import Mathlib

/-!
# OEIS A051903: Ordowski's questions (**) and (***)

`a n` is the largest exponent in the prime factorisation of `n` (a verbatim copy of
`OeisA51903.a` from `FormalConjectures/OEIS/51903.lean`).

* `not_conj2`: there is no odd `n` with `a n > 1` and `b ^ n ≡ b ^ a(n) (mod n)` for all `b`.
  If `q ^ E ∥ n` with `E = a n ≥ 2`, then `b = q + 1` gives `(q + 1) ^ (n - E) ≡ 1 (mod q ^ E)`.
  Lifting the exponent gives `q ^ (E - 1) ∣ n - E`, and `q ^ (E - 1) ∣ n`, so `q ^ (E - 1) ∣ E`.
  That is impossible because `q ≥ 3`.
* `conj3_witness`: `n = 3511 ^ 2 * 7 * 631 * 881 * 201961 = 9687963167864344937` is odd,
  `a n = 2`, and `2 ^ n ≡ 2 ^ 2 (mod n)`. The modular power is evaluated by a verified
  square-and-multiply function.
-/

namespace A051903Core

/-- Verbatim copy of `OeisA51903.a`: maximum exponent in the prime factorization of `n`. -/
def a (n : ℕ) : ℕ :=
  (n.primeFactorsList.map (n.primeFactorsList.count ·)).foldr max 0

theorem foldr_max_eq_zero_or_mem : ∀ L : List ℕ, L.foldr max 0 = 0 ∨ L.foldr max 0 ∈ L
  | [] => Or.inl rfl
  | x :: L => by
    right
    rcases foldr_max_eq_zero_or_mem L with h | h
    · simp [List.foldr_cons, h]
    · rcases le_total x (L.foldr max 0) with hle | hle
      · rw [List.foldr_cons, max_eq_right hle]; exact List.mem_cons_of_mem _ h
      · rw [List.foldr_cons, max_eq_left hle]; exact List.mem_cons_self

/-- If `a n > 0`, the maximum is attained at a prime `q ∣ n`. -/
theorem exists_prime_eq (n : ℕ) (h : 0 < a n) :
    ∃ q, q.Prime ∧ q ∣ n ∧ n.factorization q = a n := by
  unfold a at h ⊢
  rcases foldr_max_eq_zero_or_mem (n.primeFactorsList.map (n.primeFactorsList.count ·)) with
    h0 | hmem
  · omega
  · obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hmem
    exact ⟨q, Nat.prime_of_mem_primeFactorsList hq, Nat.dvd_of_mem_primeFactorsList hq,
      by rw [← Nat.primeFactorsList_count_eq]; exact hqe⟩

theorem lt_three_pow (E : ℕ) (hE : 2 ≤ E) : E < 3 ^ (E - 1) := by
  induction E with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · omega
      · norm_num
    · have h := ih hk
      rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]
      omega

/-- Ordowski's question (**) has a negative answer. -/
theorem not_conj2 : ¬ ∃ n : ℕ, Odd n ∧ 1 < a n ∧ ∀ b : ℕ, b ^ n ≡ b ^ (a n) [MOD n] := by
  rintro ⟨n, hodd, hE, hall⟩
  obtain ⟨q, hq, hqn, hqE⟩ := exists_prime_eq n (by omega)
  set E := a n with hEdef
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact absurd hodd (by decide)
  have hqEdvd : q ^ E ∣ n := by
    have := Nat.ordProj_dvd n q
    rwa [hqE] at this
  have hqodd : Odd q := hodd.of_dvd_nat hqn
  have hq3 : 3 ≤ q := by
    have h2 := hq.two_le
    obtain ⟨k, hk⟩ := hqodd
    omega
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hqEle : q ^ E ≤ n := Nat.le_of_dvd hnpos hqEdvd
  have hE3 : E < 3 ^ (E - 1) := lt_three_pow E (by omega)
  have h3q : 3 ^ (E - 1) ≤ q ^ (E - 1) := Nat.pow_le_pow_left hq3 _
  have hqE1 : q ^ (E - 1) ≤ q ^ E := Nat.pow_le_pow_right (by omega) (by omega)
  have hEn : E < n := by omega
  have hmod : (q + 1) ^ n ≡ (q + 1) ^ E [MOD q ^ E] := (hall (q + 1)).of_dvd hqEdvd
  have hsplit : (q + 1) ^ n = (q + 1) ^ E * (q + 1) ^ (n - E) := by
    rw [← pow_add, Nat.add_sub_cancel' hEn.le]
  have hcop : Nat.gcd (q ^ E) ((q + 1) ^ E) = 1 := by
    have h1 : Nat.Coprime (q + 1) q := Nat.coprime_self_add_left.mpr (Nat.coprime_one_left q)
    exact Nat.Coprime.pow E E h1.symm
  have hcancel : (q + 1) ^ (n - E) ≡ 1 [MOD q ^ E] := by
    apply Nat.ModEq.cancel_left_of_coprime hcop
    rw [mul_one, ← hsplit]
    exact hmod
  have hone : 1 ≤ (q + 1) ^ (n - E) := Nat.one_le_pow _ _ (by omega)
  have hdvd : q ^ E ∣ (q + 1) ^ (n - E) - 1 := (Nat.modEq_iff_dvd' hone).mp hcancel.symm
  have : Fact q.Prime := ⟨hq⟩
  have hnE0 : n - E ≠ 0 := by omega
  have hnot : ¬ q ∣ q + 1 := by
    intro h
    have h1 : q ∣ 1 := (Nat.dvd_add_right (dvd_refl q)).mp h
    exact absurd (Nat.dvd_one.mp h1) (by omega)
  have hLTE := padicValNat.pow_sub_pow (x := q + 1) (y := 1) hqodd (by omega)
    (by simp) hnot hnE0
  simp only [one_pow, Nat.add_sub_cancel, padicValNat_self] at hLTE
  have hne0 : (q + 1) ^ (n - E) - 1 ≠ 0 := by
    have : 1 < (q + 1) ^ (n - E) := (one_lt_pow_iff hnE0).mpr (by omega)
    omega
  have hle1 : E ≤ padicValNat q ((q + 1) ^ (n - E) - 1) := (padicValNat_dvd_iff_le hne0).mp hdvd
  have hle2 : E - 1 ≤ padicValNat q (n - E) := by omega
  have hdvd2 : q ^ (E - 1) ∣ n - E := (Nat.pow_dvd_pow q hle2).trans pow_padicValNat_dvd
  have hdvd3 : q ^ (E - 1) ∣ n := (Nat.pow_dvd_pow q (Nat.sub_le E 1)).trans hqEdvd
  have hdvdE : q ^ (E - 1) ∣ E := by
    have h := Nat.dvd_sub hdvd3 hdvd2
    rwa [Nat.sub_sub_self hEn.le] at h
  have hle := Nat.le_of_dvd (by omega) hdvdE
  omega

/-! ## The witness for question (***) -/

/-- Square-and-multiply with fuel `k`: `pm b m k e = b ^ e % m` whenever `e < 2 ^ k`. -/
def pm (b m : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % m
  | k + 1, e => if e % 2 = 0 then (pm b m k (e / 2)) ^ 2 % m
                 else (pm b m k (e / 2)) ^ 2 * b % m

theorem pm_eq (b m : ℕ) : ∀ k e, e < 2 ^ k → pm b m k e = b ^ e % m
  | 0, e, he => by
    have : e = 0 := by simpa using he
    subst this; simp [pm]
  | k + 1, e, he => by
    have h2 : e / 2 < 2 ^ k := by rw [pow_succ] at he; omega
    have ih := pm_eq b m k (e / 2) h2
    have hmod : (b ^ (e / 2) % m) ^ 2 ≡ (b ^ (e / 2)) ^ 2 [MOD m] := (Nat.mod_modEq _ _).pow 2
    simp only [pm, ih]
    split_ifs with hpar
    · have he2 : b ^ e = (b ^ (e / 2)) ^ 2 := by
        rw [← pow_mul]; congr 1; omega
      rw [he2]; exact hmod
    · have he2 : b ^ e = (b ^ (e / 2)) ^ 2 * b := by
        rw [← pow_mul, ← pow_succ]; congr 1; omega
      rw [he2]; exact hmod.mul_right b

def N0 : ℕ := 9687963167864344937

theorem N0_factors : N0.primeFactorsList = [7, 631, 881, 3511, 3511, 201961] := by
  have hperm : [7, 631, 881, 3511, 3511, 201961].Perm N0.primeFactorsList :=
    Nat.primeFactorsList_unique (by norm_num [N0]) (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
  exact (hperm.eq_of_sortedLE (by decide) (Nat.primeFactorsList_sorted _)).symm

theorem a_N0 : a N0 = 2 := by
  unfold a
  rw [N0_factors]
  decide

theorem pow_N0 : 2 ^ N0 % N0 = 4 := by
  rw [← pm_eq 2 N0 64 N0 (by norm_num [N0])]
  decide +kernel

/-- Ordowski's question (***) has a positive answer. -/
theorem conj3_witness : ∃ n : ℕ, Odd n ∧ 1 < a n ∧ 2 ^ n ≡ 2 ^ (a n) [MOD n] := by
  refine ⟨N0, Nat.odd_iff.mpr (by norm_num [N0]), by rw [a_N0]; norm_num, ?_⟩
  rw [a_N0]
  show 2 ^ N0 % N0 = 2 ^ 2 % N0
  rw [pow_N0]
  norm_num [N0]

end A051903Core

#print axioms A051903Core.not_conj2
#print axioms A051903Core.conj3_witness
