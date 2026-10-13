import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

/-! Finite expansions of an affine resolvent equation, with an explicit
remainder. These are algebraic estimates to be instantiated with the actual
finite Markov operator; no stochastic representation is assumed here. -/

namespace IGS.Sec31

open scoped BigOperators

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem continuousLinearMap_norm_pow_le (operator : Space →L[ℝ] Space) (count : ℕ) :
    ‖operator ^ count‖ ≤ ‖operator‖ ^ count := by
  cases count with
  | zero =>
    change ‖ContinuousLinearMap.id ℝ Space‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  | succ count => exact norm_pow_le' operator (Nat.succ_pos count)

theorem affine_fixedPoint_finite_expansion
    (operator : Space →L[ℝ] Space) (forcing solution : Space)
    (fixedPoint : solution = forcing + operator solution) (count : ℕ) :
    solution = (∑ index ∈ Finset.range count, (operator ^ index) forcing) +
      (operator ^ count) solution := by
  induction count with
  | zero => simp
  | succ count induction =>
    have remainder : (operator ^ count) solution =
        (operator ^ count) forcing + (operator ^ (count + 1)) solution := by
      simpa only [map_add, pow_succ, ContinuousLinearMap.mul_apply] using
        congrArg (fun value => (operator ^ count) value) fixedPoint
    calc
      solution = (∑ index ∈ Finset.range count, (operator ^ index) forcing) +
          (operator ^ count) solution := induction
      _ = (∑ index ∈ Finset.range (count + 1), (operator ^ index) forcing) +
          (operator ^ (count + 1)) solution := by
        rw [remainder, Finset.sum_range_succ]
        abel

theorem affine_fixedPoint_finite_expansion_error
    (operator : Space →L[ℝ] Space) (forcing solution : Space)
    (fixedPoint : solution = forcing + operator solution)
    (ratio : ℝ) (ratioNonnegative : 0 ≤ ratio) (contraction : ‖operator‖ ≤ ratio)
    (count : ℕ) :
    ‖solution - ∑ index ∈ Finset.range count, (operator ^ index) forcing‖ ≤
      ratio ^ count * ‖solution‖ := by
  have remainder : solution - ∑ index ∈ Finset.range count, (operator ^ index) forcing =
      (operator ^ count) solution := by
    have expansion := affine_fixedPoint_finite_expansion operator forcing solution fixedPoint count
    exact (sub_eq_iff_eq_add).mpr (by simpa only [add_comm] using expansion)
  rw [remainder]
  calc
    ‖(operator ^ count) solution‖ ≤ ‖operator ^ count‖ * ‖solution‖ :=
      (operator ^ count).le_opNorm solution
    _ ≤ ‖operator‖ ^ count * ‖solution‖ :=
      mul_le_mul_of_nonneg_right (continuousLinearMap_norm_pow_le operator count) (norm_nonneg solution)
    _ ≤ ratio ^ count * ‖solution‖ := by gcongr

end IGS.Sec31

#print axioms IGS.Sec31.affine_fixedPoint_finite_expansion
#print axioms IGS.Sec31.affine_fixedPoint_finite_expansion_error
#print axioms IGS.Sec31.continuousLinearMap_norm_pow_le
