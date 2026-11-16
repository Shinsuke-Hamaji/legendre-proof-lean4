import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

def ShiftedLegendreConjectureStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ p : ℕ, Nat.Prime p ∧ (n - 1) ^ 2 < p ∧ p < n ^ 2

#print ShiftedLegendreConjectureStatement

def shifted_legendre_energy_slots (n : ℕ) : Finset ℕ :=
  (Finset.range (n ^ 2 + 1)).filter (fun p => Nat.Prime p ∧ (n - 1) ^ 2 < p ∧ p < n ^ 2)

#print shifted_legendre_energy_slots

def structural_capacity_equilibrium (n : ℕ) : Prop :=
  2 ≤ n ∧ (0 : ℝ) < Real.log (n : ℝ)

#print structural_capacity_equilibrium

theorem shifted_legendre_internal_floor (n : ℕ) (_hn : 2 ≤ n)
    (_h_capacity_eq : structural_capacity_equilibrium n)
    (h_density : ∃ p, Nat.Prime p ∧ (n - 1) ^ 2 < p ∧ p < n ^ 2) :
    1 ≤ (shifted_legendre_energy_slots n).card := by
  rw [Nat.succ_le_iff, Finset.card_pos, Finset.nonempty_def]
  dsimp [shifted_legendre_energy_slots]
  simp only [Finset.mem_filter, Finset.mem_range]
  obtain ⟨p, hp_prime, hp_lo, hp_hi⟩ := h_density
  exact ⟨p, by omega, hp_prime, hp_lo, hp_hi⟩

#print shifted_legendre_internal_floor

theorem shifted_legendre_conditioned_main 
    (h_capacity_eq : ∀ n, 2 ≤ n → structural_capacity_equilibrium n)
    (h_structural_density : ∀ m, 2 ≤ m → ∃ p, Nat.Prime p ∧ (m - 1) ^ 2 < p ∧ p < m ^ 2) :
    ShiftedLegendreConjectureStatement := by
  intro n hn
  have _heq := h_capacity_eq n hn
  exact h_structural_density n hn

#print shifted_legendre_conditioned_main

def OppermannConjectureStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∃ p : ℕ, Nat.Prime p ∧ n * (n - 1) < p ∧ p < n ^ 2) ∧
    (∃ q : ℕ, Nat.Prime q ∧ n ^ 2 < q ∧ q < n * (n + 1))

#print OppermannConjectureStatement

def oppermann_left_energy_slots (n : ℕ) : Finset ℕ :=
  (Finset.range (n ^ 2 + 1)).filter (fun p => Nat.Prime p ∧ n * (n - 1) < p ∧ p < n ^ 2)

#print oppermann_left_energy_slots

def oppermann_right_energy_slots (n : ℕ) : Finset ℕ :=
  (Finset.range (n * (n + 1) + 1)).filter (fun q => Nat.Prime q ∧ n ^ 2 < q ∧ q < n * (n + 1))

#print oppermann_right_energy_slots

theorem oppermann_half_step_internal_floor (n : ℕ) (_hn : 2 ≤ n)
    (_h_capacity_eq : structural_capacity_equilibrium n)
    (h_half_step_sync :
      (∃ p, Nat.Prime p ∧ n * (n - 1) < p ∧ p < n ^ 2) ∧
      (∃ q, Nat.Prime q ∧ n ^ 2 < q ∧ q < n * (n + 1))) :
    1 ≤ (oppermann_left_energy_slots n).card ∧ 1 ≤ (oppermann_right_energy_slots n).card := by
  obtain ⟨⟨p, hp_prime, hp_lo, hp_hi⟩, ⟨q, hq_prime, hq_lo, hq_hi⟩⟩ := h_half_step_sync
  constructor
  · rw [Nat.succ_le_iff, Finset.card_pos, Finset.nonempty_def]
    dsimp [oppermann_left_energy_slots]
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨p, by omega, hp_prime, hp_lo, hp_hi⟩
  · rw [Nat.succ_le_iff, Finset.card_pos, Finset.nonempty_def]
    dsimp [oppermann_right_energy_slots]
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨q, by omega, hq_prime, hq_lo, hq_hi⟩

#print oppermann_half_step_internal_floor

theorem oppermann_conditioned_main
    (h_capacity_eq : ∀ n, 2 ≤ n → structural_capacity_equilibrium n)
    (h_half_step_density : ∀ m, 2 ≤ m →
      (∃ p, Nat.Prime p ∧ m * (m - 1) < p ∧ p < m ^ 2) ∧
      (∃ q, Nat.Prime q ∧ m ^ 2 < q ∧ q < m * (m + 1))) :
    OppermannConjectureStatement := by
  intro n hn
  have _heq := h_capacity_eq n hn
  exact h_half_step_density n hn

#print oppermann_conditioned_main

theorem shifted_legendre_of_oppermann
    (h_opp : OppermannConjectureStatement) :
    ShiftedLegendreConjectureStatement := by
  intro n hn
  obtain ⟨⟨p, hp_prime, hp_lo, hp_hi⟩, _⟩ := h_opp n hn
  refine ⟨p, hp_prime, ?_, hp_hi⟩
  have h_sub : (n - 1) ^ 2 ≤ n * (n - 1) := by
    calc
      (n - 1) ^ 2 = (n - 1) * (n - 1) := sq (n - 1)
      _ ≤ n * (n - 1) := Nat.mul_le_mul_right (n - 1) (Nat.sub_le n 1)
  exact lt_of_le_of_lt h_sub hp_lo

#print shifted_legendre_of_oppermann

#print axioms oppermann_conditioned_main
#print axioms shifted_legendre_of_oppermann
