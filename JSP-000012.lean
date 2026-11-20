import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NaturalMathematics

/-! # Step 1: Synchronized Infinity & 1D Tree -/

/-- Synchronized Infinity Principle -/
theorem synchronized_infinity_principle :
    ∃ (f : ℕ → ℕ), Function.Injective f ∧ ∃ y, ∀ x, f x ≠ y := by
  refine ⟨fun x => x + 1, ?_, 0, ?_⟩
  · intro a b h
    exact Nat.succ.inj h
  · intro x h
    exact Nat.succ_ne_zero x h

/-- 1D Synchronized Infinite Tree -/
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

/-! # Step 2: Square Geometry, Prime Separation (1 vs 2), & 0.5-Pitch Composite Emergence -/

/-- Square-Rectangle Partition & Nesting -/
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

/-- Composite number definition (m ≥ 2 and not prime) -/
def IsComposite (m : ℕ) : Prop := 2 ≤ m ∧ ¬ Nat.Prime m

/--
  Separation of 1 and 2 via prime definition, absence of composites in m ≤ 2,
  minimal composite emergence at 2^2 = 4 (0.5 square pitch from 1-2 to 1-2-3-4),
  and composite existence at n^2 for n ≥ 2.
-/
theorem composite_emergence_half_step_inevitability (n : ℕ) (hn : 2 ≤ n) :
    (¬ Nat.Prime 1 ∧ Nat.Prime 2) ∧
    (∀ m : ℕ, m ≤ 2 → ¬ IsComposite m) ∧
    (IsComposite (2 ^ 2) ∧ ∀ c : ℕ, IsComposite c → 2 ^ 2 ≤ c) ∧
    IsComposite (n ^ 2) := by
  refine ⟨⟨Nat.not_prime_one, Nat.prime_two⟩, ?_, ?_, ?_⟩
  · intro m _ ⟨hm2, hnp⟩
    have hm_eq : m = 2 := by omega
    subst hm_eq
    exact hnp Nat.prime_two
  · refine ⟨⟨by norm_num, by decide⟩, ?_⟩
    intro c ⟨_, hcnp⟩
    by_contra hlt
    have hcases : c = 2 ∨ c = 3 := by omega
    rcases hcases with rfl | rfl
    · exact hcnp Nat.prime_two
    · exact hcnp Nat.prime_three
  · refine ⟨by nlinarith, ?_⟩
    exact Nat.Prime.not_prime_pow (by omega)

/-- Invariant square pitch log_n(n^2) = 2 -/
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

/-! # Step 3: Synchronized-Tree-Dependent Propositional Bridge (Oppermann & Legendre) -/

def oppermann_left_energy_slots (n : ℕ) : Finset ℕ :=
  (Finset.range (n ^ 2 + 1)).filter (fun p => Nat.Prime p ∧ n * (n - 1) < p ∧ p < n ^ 2)

def oppermann_right_energy_slots (n : ℕ) : Finset ℕ :=
  (Finset.range (n * (n + 1) + 1)).filter (fun q => Nat.Prime q ∧ n ^ 2 < q ∧ q < n * (n + 1))

def OppermannConjectureStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n → SynchronizedInfiniteTree1D n →
    (∃ p : ℕ, Nat.Prime p ∧ n * (n - 1) < p ∧ p < n ^ 2) ∧
    (∃ q : ℕ, Nat.Prime q ∧ n ^ 2 < q ∧ q < n * (n + 1))

def ShiftedLegendreConjectureStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n → SynchronizedInfiniteTree1D n →
    ∃ p : ℕ, Nat.Prime p ∧ (n - 1) ^ 2 < p ∧ p < n ^ 2

theorem oppermann_slots_nonempty_of_conjecture
    (h_opp : OppermannConjectureStatement) (n : ℕ) (hn : 2 ≤ n) :
    1 ≤ (oppermann_left_energy_slots n).card ∧ 1 ≤ (oppermann_right_energy_slots n).card := by
  obtain ⟨t_sync, _, h_gen_lt⟩ := ramanujacharyulu_synchronized_1d_tree n (by omega)
  have _h_bound : generation1D t_sync < n := h_gen_lt
  obtain ⟨⟨p, hp_prime, hp_lo, hp_hi⟩, ⟨q, hq_prime, hq_lo, hq_hi⟩⟩ := h_opp n hn t_sync
  constructor
  · rw [Nat.succ_le_iff, Finset.card_pos, Finset.nonempty_def]
    dsimp [oppermann_left_energy_slots]
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨p, by nlinarith, hp_prime, hp_lo, hp_hi⟩
  · rw [Nat.succ_le_iff, Finset.card_pos, Finset.nonempty_def]
    dsimp [oppermann_right_energy_slots]
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨q, by nlinarith, hq_prime, hq_lo, hq_hi⟩

theorem prove_shifted_legendre_of_oppermann
    (h_opp : OppermannConjectureStatement) :
    ShiftedLegendreConjectureStatement := by
  intro n hn t_sync
  obtain ⟨t_gen, _, h_gen_lt⟩ := ramanujacharyulu_synchronized_1d_tree n (by omega)
  have _h_bound : generation1D t_gen < n := h_gen_lt
  obtain ⟨⟨p, hp_prime, hp_lo, hp_hi⟩, _⟩ := h_opp n hn t_sync
  obtain ⟨_, _, h_nest, _, _, _⟩ := quadrilateral_theorem n hn
  exact ⟨p, hp_prime, lt_trans h_nest hp_lo, hp_hi⟩

end NaturalMathematics

/-! # Verification -/
#print axioms NaturalMathematics.synchronized_infinity_principle
#print axioms NaturalMathematics.quadrilateral_theorem
#print axioms NaturalMathematics.composite_emergence_half_step_inevitability
#print axioms NaturalMathematics.capacity_equilibrium_holds
#print axioms NaturalMathematics.oppermann_slots_nonempty_of_conjecture
#print axioms NaturalMathematics.prove_shifted_legendre_of_oppermann
