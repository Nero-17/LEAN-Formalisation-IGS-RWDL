import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Tactic

/-! Elementary finite Doeblin comparison. Removing a common positive
column mass leaves nonnegative rows of mass 1-delta, which contracts the
range of every real function. No matrix-power convergence is assumed.
Candidate source. -/

namespace EIGS
open scoped BigOperators
noncomputable section
variable {State : Type*} [Fintype State] [DecidableEq State]

theorem finiteMarkov_common_column_bounds (kernel : Matrix State State ℝ)
    (nonnegative : ∀ first second, 0 ≤ kernel first second)
    (rowSum : ∀ first, ∑ second, kernel first second = 1)
    (anchor : State) (commonMass : ℝ)
    (commonColumn : ∀ first, commonMass ≤ kernel first anchor)
    (function : State → ℝ) (lower upper : ℝ)
    (bounds : ∀ state, lower ≤ function state ∧ function state ≤ upper)
    (first : State) :
    (1 - commonMass) * lower ≤ kernel.mulVec function first - commonMass * function anchor ∧
    kernel.mulVec function first - commonMass * function anchor ≤ (1 - commonMass) * upper := by
  have residualNonnegative (second : State) :
      0 ≤ kernel first second - (if second = anchor then commonMass else 0) := by
    by_cases same : second = anchor
    · subst second
      simpa using sub_nonneg.mpr (commonColumn first)
    · simpa [same] using nonnegative first second
  have residualSum :
      (∑ second, (kernel first second - if second = anchor then commonMass else 0)) =
        1 - commonMass := by
    rw [Finset.sum_sub_distrib, rowSum]
    simp
  have residualValue :
      (∑ second, (kernel first second - if second = anchor then commonMass else 0) * function second) =
        kernel.mulVec function first - commonMass * function anchor := by
    simp only [sub_mul, Finset.sum_sub_distrib, Matrix.mulVec, dotProduct, ite_mul, zero_mul]
    simp
  constructor
  · calc
      (1 - commonMass) * lower =
          (∑ second, (kernel first second - if second = anchor then commonMass else 0)) * lower := by
            rw [residualSum]
      _ = ∑ second, (kernel first second - if second = anchor then commonMass else 0) * lower :=
        Finset.sum_mul _ _ _
      _ ≤ ∑ second, (kernel first second - if second = anchor then commonMass else 0) * function second :=
        Finset.sum_le_sum (fun second _ => mul_le_mul_of_nonneg_left
          (bounds second).1 (residualNonnegative second))
      _ = kernel.mulVec function first - commonMass * function anchor := residualValue
  · calc
      kernel.mulVec function first - commonMass * function anchor =
          ∑ second, (kernel first second - if second = anchor then commonMass else 0) * function second :=
            residualValue.symm
      _ ≤ ∑ second, (kernel first second - if second = anchor then commonMass else 0) * upper :=
        Finset.sum_le_sum (fun second _ => mul_le_mul_of_nonneg_left
          (bounds second).2 (residualNonnegative second))
      _ = (∑ second, (kernel first second - if second = anchor then commonMass else 0)) * upper :=
        (Finset.sum_mul _ _ _).symm
      _ = (1 - commonMass) * upper := by rw [residualSum]

theorem finiteMarkov_common_column_difference (kernel : Matrix State State ℝ)
    (nonnegative : ∀ first second, 0 ≤ kernel first second)
    (rowSum : ∀ first, ∑ second, kernel first second = 1)
    (anchor : State) (commonMass : ℝ)
    (commonColumn : ∀ first, commonMass ≤ kernel first anchor)
    (function : State → ℝ) (lower upper : ℝ)
    (bounds : ∀ state, lower ≤ function state ∧ function state ≤ upper)
    (first second : State) :
    kernel.mulVec function first - kernel.mulVec function second ≤
      (1 - commonMass) * (upper - lower) := by
  have firstBound := finiteMarkov_common_column_bounds kernel nonnegative rowSum
    anchor commonMass commonColumn function lower upper bounds first
  have secondBound := finiteMarkov_common_column_bounds kernel nonnegative rowSum
    anchor commonMass commonColumn function lower upper bounds second
  nlinarith

theorem finite_positive_matrix_common_column [Nonempty State]
    (kernel : Matrix State State ℝ) (positive : ∀ first second, 0 < kernel first second) :
    ∃ anchor commonMass, 0 < commonMass ∧ commonMass < 1 ∧
      ∀ first, commonMass ≤ kernel first anchor := by
  classical
  let anchor : State := Classical.arbitrary State
  let columnValues : Finset ℝ := Finset.univ.image (fun first => kernel first anchor)
  have columnNonempty : columnValues.Nonempty := Finset.univ_nonempty.image _
  let smallest := columnValues.min' columnNonempty
  have smallestPositive : 0 < smallest := by
    obtain ⟨first, _, valueEquality⟩ := Finset.mem_image.mp
      (Finset.min'_mem columnValues columnNonempty)
    exact valueEquality ▸ positive first anchor
  refine ⟨anchor, min (1 / 2) smallest, lt_min (by norm_num) smallestPositive,
    (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  intro first
  exact (min_le_right _ _).trans
    (Finset.min'_le columnValues _ (Finset.mem_image_of_mem _ (Finset.mem_univ first)))

end
end EIGS

#print axioms EIGS.finiteMarkov_common_column_bounds
#print axioms EIGS.finiteMarkov_common_column_difference
#print axioms EIGS.finite_positive_matrix_common_column
