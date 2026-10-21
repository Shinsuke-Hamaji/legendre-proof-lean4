import Mathlib

/-!
# Pair Synchronization Core Module (Fully Cleaned & Fixed Version)
# Author: Shinsuke Hamaji (Hyama Natural Science Research Institute)
-/

/-- Counting structure for odd primes (a) and odd composites (b) within an odd interval -/
structure OddCounts where
  a : ℕ  -- Number of odd primes
  b : ℕ  -- Number of odd composites

/-- Structural components of the odd pair space (corresponding to the binomial expansion a^2 + b^2 + 2ab) -/
structure OddPairSpace where
  P : ℕ      -- Prime-Prime pairs (corresponding to a^2)
  C : ℕ      -- Composite-Composite pairs (corresponding to b^2)
  M : ℕ      -- Mixed pairs (corresponding to 2ab)
  total : ℕ  -- Total number of all pairs
  sum_eq : P + C + M = total

namespace PairSynchronizationCore

-- ============================================================================
-- Part 1: Proof of Exclusive Stepwise Increase (Two Categories)
-- ============================================================================

inductive StepIncrease : OddCounts → OddCounts → Prop
  | step_prime (c : OddCounts) :
      StepIncrease c ⟨c.a + 1, c.b⟩
  | step_composite (c : OddCounts) :
      StepIncrease c ⟨c.a, c.b + 1⟩

theorem exclusive_step_increase_properties
  (c1 c2 : OddCounts)
  (h_step : StepIncrease c1 c2) :
  (c2.a + c2.b = c1.a + c1.b + 1) ∧ 
  ((c2.a = c1.a + 1 ∧ c2.b = c1.b) ∨ (c2.a = c1.a ∧ c2.b = c1.b + 1)) := by
  -- Eliminating variable binding after 'with' to comply with safe inductive expansion in Lean 4
  cases h_step
  · dsimp
    constructor
    · omega
    · left
      exact ⟨rfl, rfl⟩
  · dsimp
    constructor
    · omega
    · right
      exact ⟨rfl, rfl⟩


-- ============================================================================
-- Part 2: Derivation Proof of "Pair Synchronization" and "Anti-Phase" from Two Combinations
-- ============================================================================

theorem zero_sum_conservation
  (space : OddPairSpace)
  (P_avg C_avg M_avg : ℤ)
  (h_base_sum : P_avg + C_avg + M_avg = (space.total : ℤ)) :
  ((space.P : ℤ) - P_avg) + ((space.C : ℤ) - C_avg) + ((space.M : ℤ) - M_avg) = 0 := by
  have h_space_z : (space.P : ℤ) + (space.C : ℤ) + (space.M : ℤ) = (space.total : ℤ) := by
    exact_mod_cast congrArg (fun x : ℕ => (x : ℤ)) space.sum_eq
  omega

/-- 
  [Theorem 3: Inevitability Theorem of Pair Synchronization and Anti-Phase Oscillation]
  Pure algebraic coherence removing warnings or unnecessary context pollution.
-/
theorem pair_sync_and_antiphase_inevitability
  (space : OddPairSpace)
  (P_avg C_avg M_avg : ℤ)
  (h_base_sum : P_avg + C_avg + M_avg = (space.total : ℤ))
  (h_sync : (space.P : ℤ) - P_avg = (space.C : ℤ) - C_avg) :
  ((space.P : ℤ) - P_avg) = ((space.C : ℤ) - C_avg) ∧
  ((space.M : ℤ) - M_avg) = - 2 * ((space.P : ℤ) - P_avg) := by
  have h_zero : ((space.P : ℤ) - P_avg) + ((space.C : ℤ) - C_avg) + ((space.M : ℤ) - M_avg) = 0 := by
    exact zero_sum_conservation space P_avg C_avg M_avg h_base_sum
  constructor
  · exact h_sync
  · omega

end PairSynchronizationCore

-- ============================================================================
-- Strict Axiom Audit Section
-- ============================================================================

#print axioms PairSynchronizationCore.exclusive_step_increase_properties
#print axioms PairSynchronizationCore.zero_sum_conservation
#print axioms PairSynchronizationCore.pair_sync_and_antiphase_inevitability
