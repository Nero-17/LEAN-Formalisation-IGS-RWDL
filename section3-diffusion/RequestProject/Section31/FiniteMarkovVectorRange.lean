import RequestProject.Section31.FiniteMarkovCommonColumnContraction
import Mathlib.Topology.Order.MonotoneConvergence

/-! Actual finite minimum/maximum ranges for stochastic matrix iterates.
These supply bounded monotone envelopes and the Doeblin width contraction;
no asymptotic statement is assumed. Candidate source. -/

namespace EIGS
open scoped BigOperators
noncomputable section
variable {State : Type*} [Fintype State] [DecidableEq State] [Nonempty State]

def finiteVectorMinimum (function : State → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty function

def finiteVectorMaximum (function : State → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty function

def finiteVectorWidth (function : State → ℝ) : ℝ :=
  finiteVectorMaximum function - finiteVectorMinimum function

theorem finiteVector_range_bounds (function : State → ℝ) (state : State) :
    finiteVectorMinimum function ≤ function state ∧ function state ≤ finiteVectorMaximum function :=
  ⟨Finset.inf'_le _ (Finset.mem_univ state), Finset.le_sup' _ (Finset.mem_univ state)⟩

theorem finiteVector_width_nonnegative (function : State → ℝ) : 0 ≤ finiteVectorWidth function := by
  have bounds := finiteVector_range_bounds function (Classical.arbitrary State)
  exact sub_nonneg.mpr (bounds.1.trans bounds.2)

theorem finiteMarkov_range_bounds (kernel : Matrix State State ℝ)
    (nonnegative : ∀ first second, 0 ≤ kernel first second)
    (rowSum : ∀ first, ∑ second, kernel first second = 1)
    (function : State → ℝ) (first : State) :
    finiteVectorMinimum function ≤ kernel.mulVec function first ∧
      kernel.mulVec function first ≤ finiteVectorMaximum function := by
  have comparison := finiteMarkov_common_column_bounds kernel nonnegative rowSum
    (Classical.arbitrary State) 0 (fun first => nonnegative first _) function
    (finiteVectorMinimum function) (finiteVectorMaximum function)
    (finiteVector_range_bounds function) first
  simpa using comparison

theorem finiteMarkov_envelope_bounds (kernel : Matrix State State ℝ)
    (nonnegative : ∀ first second, 0 ≤ kernel first second)
    (rowSum : ∀ first, ∑ second, kernel first second = 1)
    (function : State → ℝ) :
    finiteVectorMinimum function ≤ finiteVectorMinimum (kernel.mulVec function) ∧
      finiteVectorMaximum (kernel.mulVec function) ≤ finiteVectorMaximum function := by
  constructor
  · apply Finset.le_inf'
    intro state _
    exact (finiteMarkov_range_bounds kernel nonnegative rowSum function state).1
  · apply Finset.sup'_le
    intro state _
    exact (finiteMarkov_range_bounds kernel nonnegative rowSum function state).2

theorem finiteMarkov_width_contraction (kernel : Matrix State State ℝ)
    (nonnegative : ∀ first second, 0 ≤ kernel first second)
    (rowSum : ∀ first, ∑ second, kernel first second = 1)
    (anchor : State) (commonMass : ℝ)
    (commonColumn : ∀ first, commonMass ≤ kernel first anchor)
    (function : State → ℝ) :
    finiteVectorWidth (kernel.mulVec function) ≤ (1 - commonMass) * finiteVectorWidth function := by
  obtain ⟨first, _, firstValue⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (kernel.mulVec function)
  obtain ⟨second, _, secondValue⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (kernel.mulVec function)
  have comparison := finiteMarkov_common_column_difference kernel nonnegative rowSum
    anchor commonMass commonColumn function (finiteVectorMinimum function)
    (finiteVectorMaximum function) (finiteVector_range_bounds function) first second
  simpa only [finiteVectorWidth, finiteVectorMaximum, finiteVectorMinimum,
    firstValue, secondValue] using comparison

theorem finiteMarkov_power_envelopes (kernel : Matrix State State ℝ)
    (nonnegative : ∀ first second, 0 ≤ kernel first second)
    (rowSum : ∀ first, ∑ second, kernel first second = 1)
    (function : State → ℝ) :
    Monotone (fun power : ℕ => finiteVectorMinimum ((kernel ^ power).mulVec function)) ∧
      Antitone (fun power : ℕ => finiteVectorMaximum ((kernel ^ power).mulVec function)) := by
  constructor
  · apply monotone_nat_of_le_succ
    intro power
    have comparison := (finiteMarkov_envelope_bounds kernel nonnegative rowSum
      ((kernel ^ power).mulVec function)).1
    simpa only [pow_succ', Matrix.mulVec_mulVec] using comparison
  · apply antitone_nat_of_succ_le
    intro power
    have comparison := (finiteMarkov_envelope_bounds kernel nonnegative rowSum
      ((kernel ^ power).mulVec function)).2
    simpa only [pow_succ', Matrix.mulVec_mulVec] using comparison

end
end EIGS

#print axioms EIGS.finiteVector_range_bounds
#print axioms EIGS.finiteMarkov_envelope_bounds
#print axioms EIGS.finiteMarkov_width_contraction
#print axioms EIGS.finiteMarkov_power_envelopes
