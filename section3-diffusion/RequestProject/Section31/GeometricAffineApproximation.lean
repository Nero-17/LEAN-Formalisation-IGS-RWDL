import RequestProject.Section31.AffineContractionTruncation
import Mathlib.Algebra.Ring.GeomSum

/-! A short-time estimate for a contractive transition controls an affine
resolvent through an explicit geometric remainder. Native applications must
fill the transition contraction, equation, bounds and short-time estimate. -/

namespace IGS.Sec31

open scoped BigOperators

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem geometric_affine_fixedPoint_error
    (transition : Space →L[ℝ] Space) (contraction : ‖transition‖ ≤ 1)
    (ratio : ℝ) (ratioNonnegative : 0 ≤ ratio) (ratioAtMostOne : ratio ≤ 1)
    (forcing solution : Space)
    (fixedPoint : solution = (1 - ratio) • forcing + ratio • transition solution)
    (bound error : ℝ) (boundNonnegative : 0 ≤ bound) (errorNonnegative : 0 ≤ error)
    (forcingBound : ‖forcing‖ ≤ bound) (solutionBound : ‖solution‖ ≤ bound)
    (count : ℕ)
    (shortTime : ∀ index < count, ‖(transition ^ index) forcing - forcing‖ ≤ error) :
    ‖solution - forcing‖ ≤ error + 2 * ratio ^ count * bound := by
  have expansion := affine_fixedPoint_finite_expansion (ratio • transition)
    ((1 - ratio) • forcing) solution fixedPoint count
  simp_rw [smul_pow, ContinuousLinearMap.smul_apply, map_smul, smul_smul] at expansion
  have weightSum : (∑ index ∈ Finset.range count, ratio ^ index * (1 - ratio)) =
      1 - ratio ^ count := by
    rw [← Finset.sum_mul, geom_sum_mul_neg]
  have constantExpansion :
      (∑ index ∈ Finset.range count, (ratio ^ index * (1 - ratio)) • forcing) +
        ratio ^ count • forcing = forcing := by
    rw [← Finset.sum_smul, weightSum, ← add_smul]
    simp
  have difference : solution - forcing =
      (∑ index ∈ Finset.range count,
        (ratio ^ index * (1 - ratio)) • ((transition ^ index) forcing - forcing)) +
          ratio ^ count • ((transition ^ count) solution - forcing) := by
    calc
      solution - forcing =
          ((∑ index ∈ Finset.range count,
            (ratio ^ index * (1 - ratio)) • (transition ^ index) forcing) +
              ratio ^ count • (transition ^ count) solution) -
          ((∑ index ∈ Finset.range count, (ratio ^ index * (1 - ratio)) • forcing) +
            ratio ^ count • forcing) := congrArg₂ (fun first second => first - second)
              expansion constantExpansion.symm
      _ = _ := by
        simp_rw [smul_sub, Finset.sum_sub_distrib]
        abel
  have powerBound : ‖transition ^ count‖ ≤ 1 := by
    calc
      ‖transition ^ count‖ ≤ ‖transition‖ ^ count := continuousLinearMap_norm_pow_le transition count
      _ ≤ 1 ^ count := by gcongr
      _ = 1 := one_pow count
  have tailBound : ‖(transition ^ count) solution - forcing‖ ≤ 2 * bound := by
    have iteratedBound : ‖(transition ^ count) solution‖ ≤ bound := by
      calc
        ‖(transition ^ count) solution‖ ≤ ‖transition ^ count‖ * ‖solution‖ :=
          (transition ^ count).le_opNorm solution
        _ ≤ 1 * ‖solution‖ := mul_le_mul_of_nonneg_right powerBound (norm_nonneg _)
        _ ≤ bound := by simpa using solutionBound
    exact (norm_sub_le _ _).trans (by linarith)
  have finiteBound :
      ‖∑ index ∈ Finset.range count,
        (ratio ^ index * (1 - ratio)) • ((transition ^ index) forcing - forcing)‖ ≤
          (1 - ratio ^ count) * error := by
    calc
      _ ≤ ∑ index ∈ Finset.range count,
          ‖(ratio ^ index * (1 - ratio)) • ((transition ^ index) forcing - forcing)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ index ∈ Finset.range count, (ratio ^ index * (1 - ratio)) * error := by
        apply Finset.sum_le_sum
        intro index membership
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (pow_nonneg ratioNonnegative _) (sub_nonneg.mpr ratioAtMostOne))]
        exact mul_le_mul_of_nonneg_left (shortTime index (Finset.mem_range.mp membership))
          (mul_nonneg (pow_nonneg ratioNonnegative _) (sub_nonneg.mpr ratioAtMostOne))
      _ = (1 - ratio ^ count) * error := by rw [← Finset.sum_mul, weightSum]
  rw [difference]
  calc
    _ ≤ (1 - ratio ^ count) * error + ratio ^ count * (2 * bound) := by
      apply (norm_add_le _ _).trans
      apply add_le_add finiteBound
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ratioNonnegative count)]
      exact mul_le_mul_of_nonneg_left tailBound (pow_nonneg ratioNonnegative count)
    _ ≤ error + 2 * ratio ^ count * bound := by
      nlinarith [mul_nonneg (pow_nonneg ratioNonnegative count) errorNonnegative]

end IGS.Sec31

#print axioms IGS.Sec31.geometric_affine_fixedPoint_error
