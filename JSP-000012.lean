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

/-! # Step 2: Pitch Determined by Prime Definition & Mutual Catch-Up (1 → 1.5 → 2) -/

/-- Composite number definition (m ≥ 2 and not prime) -/
def IsComposite (m : ℕ) : Prop := 2 ≤ m ∧ ¬ Nat.Prime m

/--
  Half-integer generative pitch index `k` representing `n = k / 2`:
  - `k = 2` (`n = 1.0`): Natural unit `1` (root)
  - `k = 3` (`n = 1.5`): Prime `2` emerges from prime definition, yet prime pitch alone
    cannot keep pace with the full progression by itself.
  - `k = 4` (`n = 2.0`): Prime `3` and minimal composite `4 = 2^2` emerge together,
    where composite filling steps in to cover what one side alone cannot catch up with.
-/
def PitchAnchorValue (k : ℕ) : ℕ :=
  if k = 2 then 1
  else if k = 3 then 2
  else if k = 4 then 4
  else (k / 2) ^ 2

@[simp] lemma pitchAnchorValue_two : PitchAnchorValue 2 = 1 := by
  simp [PitchAnchorValue]

@[simp] lemma pitchAnchorValue_three : PitchAnchorValue 3 = 2 := by
  simp [PitchAnchorValue]

@[simp] lemma pitchAnchorValue_four : PitchAnchorValue 4 = 4 := by
  simp [PitchAnchorValue]

/--
  At the initial prime-2 pitch (`k = 3`, `n = 1.5`), one side alone cannot catch up with
  the generative rhythm: composites have not yet emerged (`m ≤ 2`), and only once `k = 4`
  (`n = 2.0`) is reached does composite filling (`4 = 2^2`) join alongside prime `3`,
  continuing under the same invariant rule for all `n ≥ 2`.
-/
theorem prime_definition_determines_pitch_and_composite_filling (n : ℕ) (hn : 2 ≤ n) :
    (¬ Nat.Prime (PitchAnchorValue 2) ∧ Nat.Prime (PitchAnchorValue 3)) ∧
    (∀ m : ℕ, m ≤ PitchAnchorValue 3 → ¬ IsComposite m) ∧
    (∃ c : ℕ, PitchAnchorValue 3 < c ∧ c ≤ PitchAnchorValue 4 ∧ IsComposite c) ∧
    (Nat.Prime 3 ∧ IsComposite (PitchAnchorValue 4) ∧
      ∀ c : ℕ, IsComposite c → PitchAnchorValue 4 ≤ c) ∧
    IsComposite (n ^ 2) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp [Nat.not_prime_one]
  · simp [Nat.prime_two]
  · intro m hm ⟨_, hnp⟩
    simp at hm
    have hm_eq : m = 2 := by omega
    subst hm_eq
    exact hnp Nat.prime_two
  · refine ⟨4, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · decide
    · decide
  · refine ⟨Nat.prime_three, ⟨by decide, by decide⟩, ?_⟩
    intro c ⟨_, hcnp⟩
    by_contra hlt
    simp at hlt
    have hcases : c = 2 ∨ c = 3 := by omega
    rcases hcases with rfl | rfl
    · exact hcnp Nat.prime_two
    · exact hcnp Nat.prime_three
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

/-- Invariant square scaling exponent log_n(n^2) = 2 across the pitch progression -/
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
#print axioms NaturalMathematics.prime_definition_determines_pitch_and_composite_filling
#print axioms NaturalMathematics.quadrilateral_theorem
#print axioms NaturalMathematics.capacity_equilibrium_holds
#print axioms NaturalMathematics.oppermann_slots_nonempty_of_conjecture
#print axioms NaturalMathematics.prove_shifted_legendre_of_oppermann
