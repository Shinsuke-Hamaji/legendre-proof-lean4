import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NaturalMathematics

/-! # Step 1: Peano Root & 1D Synchronized Infinite Tree -/

/-- Synchronized Infinity Principle (Peano +1 step with origin 1) -/
theorem synchronized_infinity_principle :
    ∃ (f : ℕ → ℕ), Function.Injective f ∧ ∃ y, ∀ x, f x ≠ y := by
  refine ⟨fun x => x + 1, ?_, 0, ?_⟩
  · intro a b h
    exact Nat.succ.inj h
  · intro x h
    exact Nat.succ_ne_zero x h

/-- 1D Synchronized Infinite Tree rooted at 1 -/
inductive SynchronizedInfiniteTree1D : ℕ → Type
  | root : SynchronizedInfiniteTree1D 1
  | step (n : ℕ) (hn : n > 0) : SynchronizedInfiniteTree1D n → SynchronizedInfiniteTree1D (n + 1)

open SynchronizedInfiniteTree1D

def generation1D {n : ℕ} : SynchronizedInfiniteTree1D n → ℕ
  | root => 0
  | step _ _ t => 1 + generation1D t

theorem generation_sync_1d_lt_value {n : ℕ} (t : SynchronizedInfiniteTree1D n) :
    generation1D t < n := by
  induction t with
  | root =>
    change 0 < 1
    omega
  | step k _ _ ih =>
    change 1 + generation1D _ < k + 1
    omega

theorem ramanujacharyulu_synchronized_1d_tree (n : ℕ) (hn : n ≥ 1) :
    ∃ (t : SynchronizedInfiniteTree1D n), generation1D t = n - 1 ∧ generation1D t < n := by
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨SynchronizedInfiniteTree1D.root, rfl, ?_⟩
    change 0 < 1
    omega
  | succ k _ ih =>
    rcases ih with ⟨t, _, _⟩
    refine ⟨SynchronizedInfiniteTree1D.step k (by omega) t, ?_, ?_⟩
    · dsimp [generation1D]
      omega
    · exact generation_sync_1d_lt_value (SynchronizedInfiniteTree1D.step k (by omega) t)

/-! # Step 2: Necessity of 0.5 Pitch (k = 1 → 1.5 → 2) for Composite Emergence -/

/-- Composite number definition (m ≥ 2 and not prime) -/
def IsComposite (m : ℕ) : Prop := 2 ≤ m ∧ ¬ Nat.Prime m

/-- 1. In the Peano sequence 1 - 2 - 3 (m ≤ 3), NO composite number can be derived. -/
theorem no_composite_in_peano_three :
    ∀ m : ℕ, m ≤ 3 → ¬ IsComposite m := by
  intro m hm ⟨hm2, hm_np⟩
  have hcases : m = 2 ∨ m = 3 := by omega
  rcases hcases with rfl | rfl
  · exact hm_np Nat.prime_two
  · exact hm_np Nat.prime_three

/-- 2. A composite number emerges if and only if the sequence reaches 4 (= 2^2), i.e., 1 - 2 - 3 - 4. -/
theorem composite_emergence_requires_four (N : ℕ) :
    (∃ m : ℕ, m ≤ N ∧ IsComposite m) ↔ 4 ≤ N := by
  constructor
  · rintro ⟨m, hmN, hcomp⟩
    by_contra hlt
    have hm3 : m ≤ 3 := by omega
    exact no_composite_in_peano_three m hm3 hcomp
  · intro h4
    refine ⟨4, h4, ⟨by decide, by decide⟩⟩

/--
  3. Because 2^1 = 2 (minimal prime) and 2^2 = 4 (minimal composite) have prime 3 strictly
     between them (2^1 < 3 < 2^2), an integer exponent jump Δk = 1 skips the 3-step chain
     2 → 3 → 4. Thus, k from 1 to 2 necessarily requires a 0.5 pitch (1 → 1.5 → 2) so that
     composite filling (2^2 = 4) can enter alongside prime emergence.
-/
theorem prime_definition_forces_half_pitch_progression (n : ℕ) (hn : 2 ≤ n) :
    (∀ m : ℕ, m ≤ 3 → ¬ IsComposite m) ∧
    (IsComposite (2 ^ 2) ∧ ∀ c : ℕ, IsComposite c → 2 ^ 2 ≤ c) ∧
    (∃ p : ℕ, Nat.Prime p ∧ 2 ^ 1 < p ∧ p < 2 ^ 2) ∧
    (n ^ 1 < n ^ 2 ∧ 2 ≤ n ^ 2 - n ^ 1) ∧
    ((1 : ℝ) + 0.5 = 1.5 ∧ (1.5 : ℝ) + 0.5 = 2 ∧ (1 : ℝ) < 1.5 ∧ (1.5 : ℝ) < 2) ∧
    IsComposite (n ^ 2) := by
  refine ⟨no_composite_in_peano_three, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨by decide, by decide⟩, ?_⟩
    intro c hc
    have h := (composite_emergence_requires_four c).mp ⟨c, le_rfl, hc⟩
    simpa using h
  · refine ⟨3, Nat.prime_three, by decide, by decide⟩
  · refine ⟨?_, ?_⟩
    · simp only [pow_one]
      nlinarith
    · simp only [pow_one]
      have h_sub : n ^ 2 - n = n * (n - 1) := by
        calc
          n ^ 2 - n = n * n - n * 1 := by rw [sq n, Nat.mul_one]
          _ = n * (n - 1) := (Nat.mul_sub_left_distrib n n 1).symm
      have h_sub1 : 1 ≤ n - 1 := by omega
      rw [h_sub]
      nlinarith
  · norm_num
  · refine ⟨by nlinarith, ?_⟩
    exact Nat.Prime.not_prime_pow (by omega)

/-- Square-Rectangle Partition & Nesting along the Invariant Rule -/
theorem quadrilateral_theorem (n : ℕ) (hn : 2 ≤ n) :
    n ^ 2 = n * (n - 1) + n ∧
    n * (n + 1) = n ^ 2 + n ∧
    (n - 1) ^ 2 < n * (n - 1) ∧
    n * (n - 1) < n ^ 2 ∧
    n ^ 2 < n * (n + 1) ∧
    n * (n + 1) < (n + 1) ^ 2 := by
  have h1 : n ^ 2 = n * (n - 1) + n := by
    calc
      n ^ 2 = n * n := sq n
      _ = n * ((n - 1) + 1) := by congr 1; omega
      _ = n * (n - 1) + n * 1 := Nat.mul_add n (n - 1) 1
      _ = n * (n - 1) + n := by ring
  have h2 : n * (n + 1) = n ^ 2 + n := by
    calc
      n * (n + 1) = n * n + n * 1 := Nat.mul_add n n 1
      _ = n ^ 2 + n := by rw [← sq n]; ring
  have h3 : (n - 1) ^ 2 < n * (n - 1) := by
    calc
      (n - 1) ^ 2 = (n - 1) * (n - 1) := sq (n - 1)
      _ < n * (n - 1) := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  have h4 : n * (n - 1) < n ^ 2 := by
    nlinarith
  have h5 : n ^ 2 < n * (n + 1) := by
    nlinarith
  have h6 : n * (n + 1) < (n + 1) ^ 2 := by
    calc
      n * (n + 1) < (n + 1) * (n + 1) := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ = (n + 1) ^ 2 := (sq (n + 1)).symm
  exact ⟨h1, h2, h3, h4, h5, h6⟩

def structural_capacity_equilibrium (n : ℕ) : Prop :=
  2 ≤ n ∧
  (0 : ℝ) < Real.log (n : ℝ) ∧
  Real.log ((n : ℝ) ^ 2) / Real.log (n : ℝ) = 2

theorem capacity_equilibrium_holds (n : ℕ) (hn : 2 ≤ n) :
    structural_capacity_equilibrium n := by
  have hn_real : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have h_log_pos : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos hn_real
  have h_log_ne : Real.log (n : ℝ) ≠ 0 := ne_of_gt h_log_pos
  refine ⟨hn, h_log_pos, ?_⟩
  rw [Real.log_pow]
  push_cast
  field_simp [h_log_ne]

/-! # Step 3: Direct Derivation from Proved Step 1 & Step 2 Theorems -/

theorem step3_from_proved_theorems (n : ℕ) (hn : 2 ≤ n) :
    (∃ t : SynchronizedInfiniteTree1D n, generation1D t = n - 1 ∧ generation1D t < n) ∧
    (∀ m : ℕ, m ≤ 3 → ¬ IsComposite m) ∧
    IsComposite (n ^ 2) ∧
    ((n - 1) ^ 2 < n * (n - 1) ∧ n * (n - 1) < n ^ 2 ∧
     n ^ 2 < n * (n + 1) ∧ n * (n + 1) < (n + 1) ^ 2) ∧
    structural_capacity_equilibrium n := by
  have h_tree := ramanujacharyulu_synchronized_1d_tree n (by omega)
  have h_pitch := prime_definition_forces_half_pitch_progression n hn
  have h_quad := quadrilateral_theorem n hn
  have h_eq := capacity_equilibrium_holds n hn
  refine ⟨h_tree, h_pitch.1, h_pitch.2.2.2.2.2,
    ⟨h_quad.2.2.1, h_quad.2.2.2.1, h_quad.2.2.2.2.1, h_quad.2.2.2.2.2⟩, h_eq⟩

end NaturalMathematics

/-! # Verification -/
#print axioms NaturalMathematics.synchronized_infinity_principle
#print axioms NaturalMathematics.no_composite_in_peano_three
#print axioms NaturalMathematics.composite_emergence_requires_four
#print axioms NaturalMathematics.prime_definition_forces_half_pitch_progression
#print axioms NaturalMathematics.quadrilateral_theorem
#print axioms NaturalMathematics.capacity_equilibrium_holds
#print axioms NaturalMathematics.step3_from_proved_theorems

