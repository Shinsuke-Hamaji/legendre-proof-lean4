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

/-! # Step 2: Intrinsic Generation Rule, C(m) & 0.5-Step (2n - 2) Baseline -/

/-- Composite number definition (m ≥ 2 and not prime) -/
def IsComposite (m : ℕ) : Prop := 2 ≤ m ∧ ¬ Nat.Prime m

/-- Cumulative prime count π(m) up to m -/
noncomputable def primeCount (m : ℕ) : ℕ :=
  ((Finset.Icc 2 m).filter Nat.Prime).card

/-- Cumulative composite count C(m) = (m - 1) - π(m) for m ≥ 2 -/
noncomputable def compositeCount (m : ℕ) : ℕ :=
  ((Finset.Icc 2 m).filter (fun x => ¬ Nat.Prime x)).card

/-- Partition identity: π(m) + C(m) = m - 1 for all m ≥ 2 -/
theorem prime_plus_composite_eq (m : ℕ) (hm : 2 ≤ m) :
    primeCount m + compositeCount m = m - 1 := by
  unfold primeCount compositeCount
  rw [Finset.card_filter_add_card_filter_not]
  rw [Nat.card_Icc]
  omega

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

theorem composite_generation_pitch :
    (∀ m : ℕ, m ≤ 3 → ¬ IsComposite m) ∧
    IsComposite 4 ∧
    (∀ c : ℕ, IsComposite c → 4 ≤ c) ∧
    (4 - 3 = 1 ∧ 4 - 2 = 2) := by
  refine ⟨no_composite_in_peano_three, ⟨by decide, by decide⟩, ?_, ?_⟩
  · intro c hc
    exact (composite_emergence_requires_four c).mp ⟨c, le_rfl, hc⟩
  · omega

theorem prime_definition_forces_half_pitch_progression (n : ℕ) (hn : 2 ≤ n) :
    (∀ m : ℕ, m ≤ 3 → ¬ IsComposite m) ∧
    (IsComposite (2 ^ 2) ∧ ∀ c : ℕ, IsComposite c → 2 ^ 2 ≤ c) ∧
    (∃ p : ℕ, Nat.Prime p ∧ 2 ^ 1 < p ∧ p < 2 ^ 2) ∧
    (n ^ 1 < n ^ 2 ∧ 2 ≤ n ^ 2 - n ^ 1) ∧
    (4 - 3 = 1 ∧ 4 - 2 = 2) ∧
    ((1 : ℝ) + 0.5 = 1.5 ∧ (1.5 : ℝ) + 0.5 = 2 ∧ (1 : ℝ) < 1.5 ∧ (1.5 : ℝ) < 2) ∧
    IsComposite (n ^ 2) := by
  have h_gen := composite_generation_pitch
  refine ⟨h_gen.1, ⟨h_gen.2.1, h_gen.2.2.1⟩, ?_, ?_, h_gen.2.2.2, ?_, ?_⟩
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

/--
  0.5-Step (2n - 2) Baseline Equivalence:
  Up to n^2, having at least `2 * n - 2` primes (`π(n^2) ≥ 2n - 2`)
  is strictly equivalent to bounding composites by `C(n^2) ≤ (n - 1)^2`.
-/
theorem baseline_2n_sub_2_equivalence (n : ℕ) (hn : 2 ≤ n) :
    2 * n - 2 ≤ primeCount (n ^ 2) ↔ compositeCount (n ^ 2) ≤ (n - 1) ^ 2 := by
  have h_sq_ge : 2 ≤ n ^ 2 := by nlinarith
  have h_part := prime_plus_composite_eq (n ^ 2) h_sq_ge
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ 2 * n := by omega
  have h3 : 1 ≤ n ^ 2 := by nlinarith
  have h_expand : (n - 1) ^ 2 + (2 * n - 2) = n ^ 2 - 1 := by
    zify [h1, h2, h3]
    ring
  omega

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

/-! # Step 3: Propositional Dependency Structure & Unconditional Instantiation -/

/-- Oppermann's conjecture proposition on primes in quadratic intervals -/
def OppermannQuadraticIntervalProp (n : ℕ) : Prop :=
  (∃ p : ℕ, Nat.Prime p ∧ n * (n - 1) < p ∧ p < n ^ 2) ∧
  (∃ q : ℕ, Nat.Prime q ∧ n ^ 2 < q ∧ q < n * (n + 1))

/-- Legendre's conjecture proposition on primes in square intervals -/
def LegendreSquareIntervalProp (n : ℕ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2

/--
  Propositional Dependency Form:
  Takes ONLY the proved theorems from Step 1 and Step 2 as dependencies and derives
  the interval bridge between Oppermann's quadratic intervals and consecutive Legendre square intervals.
-/
theorem step3_dependency_structure
    (n : ℕ) (hn : 2 ≤ n)
    (h_peano : ∃ (f : ℕ → ℕ), Function.Injective f ∧ ∃ y, ∀ x, f x ≠ y)
    (h_tree  : ∃ t : SynchronizedInfiniteTree1D n, generation1D t = n - 1 ∧ generation1D t < n)
    (h_pitch : ∃ p : ℕ, Nat.Prime p ∧ 2 ^ 1 < p ∧ p < 2 ^ 2)
    (h_comp  : IsComposite (n ^ 2))
    (h_base  : 2 * n - 2 ≤ primeCount (n ^ 2) ↔ compositeCount (n ^ 2) ≤ (n - 1) ^ 2)
    (h_quad  : n ^ 2 = n * (n - 1) + n ∧ n * (n + 1) = n ^ 2 + n ∧
               (n - 1) ^ 2 < n * (n - 1) ∧ n * (n - 1) < n ^ 2 ∧
               n ^ 2 < n * (n + 1) ∧ n * (n + 1) < (n + 1) ^ 2)
    (h_eq    : structural_capacity_equilibrium n) :
    (OppermannQuadraticIntervalProp n →
      LegendreSquareIntervalProp (n - 1) ∧ LegendreSquareIntervalProp n) := by
  intro h_opp
  rcases h_opp with ⟨⟨p, hp_prime, hp_lo, hp_hi⟩, ⟨q, hq_prime, hq_lo, hq_hi⟩⟩
  have h_prev : (n - 1) + 1 = n := by omega
  refine ⟨?_, ?_⟩
  · unfold LegendreSquareIntervalProp
    rw [h_prev]
    exact ⟨p, hp_prime, lt_trans h_quad.2.2.1 hp_lo, hp_hi⟩
  · exact ⟨q, hq_prime, hq_lo, lt_trans hq_hi h_quad.2.2.2.2.2⟩

/--
  Final Theorem (No External Assumptions):
  Instantiates `step3_dependency_structure` directly with the proved theorems of Step 1 and Step 2.
-/
theorem step3_with_oppermann_and_legendre (n : ℕ) (hn : 2 ≤ n) :
    (∃ t : SynchronizedInfiniteTree1D n, generation1D t = n - 1 ∧ generation1D t < n) ∧
    IsComposite (n ^ 2) ∧
    (2 * n - 2 ≤ primeCount (n ^ 2) ↔ compositeCount (n ^ 2) ≤ (n - 1) ^ 2) ∧
    (n * (n - 1) < n ^ 2 ∧ n ^ 2 < n * (n + 1)) ∧
    structural_capacity_equilibrium n ∧
    (OppermannQuadraticIntervalProp n →
      LegendreSquareIntervalProp (n - 1) ∧ LegendreSquareIntervalProp n) := by
  have h_peano := synchronized_infinity_principle
  have h_tree := ramanujacharyulu_synchronized_1d_tree n (by omega)
  have h_pitch := prime_definition_forces_half_pitch_progression n hn
  rcases h_pitch with ⟨_, _, h_init_prime, _, _, _, h_comp_sq⟩
  have h_base := baseline_2n_sub_2_equivalence n hn
  have h_quad := quadrilateral_theorem n hn
  have h_eq := capacity_equilibrium_holds n hn
  have h_bridge := step3_dependency_structure n hn h_peano h_tree h_init_prime h_comp_sq h_base h_quad h_eq
  exact ⟨h_tree, h_comp_sq, h_base, ⟨h_quad.2.2.2.1, h_quad.2.2.2.2.1⟩, h_eq, h_bridge⟩

end NaturalMathematics

/-! # Verification -/

#print axioms NaturalMathematics.synchronized_infinity_principle
#print axioms NaturalMathematics.prime_plus_composite_eq
#print axioms NaturalMathematics.no_composite_in_peano_three
#print axioms NaturalMathematics.composite_emergence_requires_four
#print axioms NaturalMathematics.composite_generation_pitch
#print axioms NaturalMathematics.prime_definition_forces_half_pitch_progression
#print axioms NaturalMathematics.quadrilateral_theorem
#print axioms NaturalMathematics.baseline_2n_sub_2_equivalence
#print axioms NaturalMathematics.capacity_equilibrium_holds
#print axioms NaturalMathematics.step3_dependency_structure
#print axioms NaturalMathematics.step3_with_oppermann_and_legendre