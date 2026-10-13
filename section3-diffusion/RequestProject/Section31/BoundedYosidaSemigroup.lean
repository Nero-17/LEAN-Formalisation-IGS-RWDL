import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity

/-! Bounded Yosida exponentials from a contraction resolvent.  All exponentials
below are the actual Banach-algebra power series.  No semigroup generation or
spectral theorem is assumed. -/

namespace IGS.Sec31.BoundedYosida

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

noncomputable local instance : NormedAlgebra ℚ (H →L[ℝ] H) :=
  NormedAlgebra.restrictScalars ℚ ℝ (H →L[ℝ] H)

/-- The bounded Yosida operator associated with the step resolvent. -/
noncomputable def generator (resolvent : H →L[ℝ] H) (step : ℝ) : H →L[ℝ] H :=
  step⁻¹ • (1 - resolvent)

/-- The genuine bounded-operator exponential of minus the Yosida operator. -/
noncomputable def semigroup (resolvent : H →L[ℝ] H) (step time : ℝ) : H →L[ℝ] H :=
  NormedSpace.exp ((-time) • generator resolvent step)

theorem norm_exp_smul_le (resolvent : H →L[ℝ] H)
    (contraction : ‖resolvent‖ ≤ 1) (time : ℝ) (timeNonnegative : 0 ≤ time) :
    ‖NormedSpace.exp (time • resolvent)‖ ≤ Real.exp time := by
  have powerBound : ∀ index : ℕ, ‖(time • resolvent) ^ index‖ ≤ time ^ index := by
    intro index
    induction index with
    | zero =>
        simpa only [pow_zero] using (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := H))
    | succ index inductionBound =>
        calc
          ‖(time • resolvent) ^ (index + 1)‖ ≤
              ‖(time • resolvent) ^ index‖ * ‖time • resolvent‖ := by
            rw [pow_succ]
            exact norm_mul_le _ _
          _ ≤ time ^ index * time := by
            apply mul_le_mul inductionBound
            · simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg timeNonnegative,
                mul_one] using mul_le_mul_of_nonneg_left contraction timeNonnegative
            · exact norm_nonneg _
            · exact pow_nonneg timeNonnegative _
          _ = time ^ (index + 1) := (pow_succ _ _).symm
  have scalarSum : HasSum (fun index : ℕ =>
      ((index.factorial : ℝ)⁻¹) * time ^ index) (Real.exp time) := by
    simpa only [smul_eq_mul, Real.exp_eq_exp_ℝ] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) time)
  apply (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (time • resolvent)).norm_le_of_bounded
    scalarSum
  intro index
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ (index.factorial : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left (powerBound index) (by positivity)

theorem exp_smul_identity (time : ℝ) :
    NormedSpace.exp (time • (1 : H →L[ℝ] H)) =
      Real.exp time • (1 : H →L[ℝ] H) := by
  simpa only [Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] using
    (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := H →L[ℝ] H) time).symm

theorem semigroup_eq_scalar_mul_exp (resolvent : H →L[ℝ] H) (step time : ℝ) :
    semigroup resolvent step time =
      Real.exp (-(time / step)) • NormedSpace.exp ((time / step) • resolvent) := by
  have exponentIdentity : (-time) • generator resolvent step =
      (-(time / step)) • (1 : H →L[ℝ] H) + (time / step) • resolvent := by
    simp only [generator, smul_sub, smul_smul, div_eq_mul_inv, neg_mul, neg_smul]
    module
  have commuting : Commute ((-(time / step)) • (1 : H →L[ℝ] H))
      ((time / step) • resolvent) :=
    ((Commute.one_left resolvent).smul_left _).smul_right _
  rw [semigroup, exponentIdentity, NormedSpace.exp_add_of_commute commuting,
    exp_smul_identity, smul_mul_assoc, one_mul]

theorem semigroup_norm_le_one (resolvent : H →L[ℝ] H)
    (contraction : ‖resolvent‖ ≤ 1) (step : ℝ) (stepPositive : 0 < step)
    (time : ℝ) (timeNonnegative : 0 ≤ time) :
    ‖semigroup resolvent step time‖ ≤ 1 := by
  rw [semigroup_eq_scalar_mul_exp, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-(time / step)) * ‖NormedSpace.exp ((time / step) • resolvent)‖ ≤
        Real.exp (-(time / step)) * Real.exp (time / step) :=
      mul_le_mul_of_nonneg_left
        (norm_exp_smul_le resolvent contraction _ (div_nonneg timeNonnegative stepPositive.le))
        (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

@[simp] theorem semigroup_zero (resolvent : H →L[ℝ] H) (step : ℝ) :
    semigroup resolvent step 0 = 1 := by
  simp [semigroup, NormedSpace.exp_zero]

theorem semigroup_add (resolvent : H →L[ℝ] H) (step firstTime secondTime : ℝ) :
    semigroup resolvent step (firstTime + secondTime) =
      semigroup resolvent step firstTime * semigroup resolvent step secondTime := by
  have commuting : Commute ((-firstTime) • generator resolvent step)
      ((-secondTime) • generator resolvent step) :=
    ((Commute.refl (generator resolvent step)).smul_left _).smul_right _
  simpa only [semigroup, neg_add, add_smul] using
    NormedSpace.exp_add_of_commute commuting

theorem semigroup_continuous (resolvent : H →L[ℝ] H) (step : ℝ) :
    Continuous (semigroup resolvent step) := by
  exact NormedSpace.exp_continuous.comp (continuous_neg.smul continuous_const)

theorem semigroup_apply_norm_le (resolvent : H →L[ℝ] H)
    (contraction : ‖resolvent‖ ≤ 1) (step : ℝ) (stepPositive : 0 < step)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (values : H) :
    ‖semigroup resolvent step time values‖ ≤ ‖values‖ := by
  calc
    ‖semigroup resolvent step time values‖ ≤
        ‖semigroup resolvent step time‖ * ‖values‖ :=
      (semigroup resolvent step time).le_opNorm values
    _ ≤ 1 * ‖values‖ := mul_le_mul_of_nonneg_right
      (semigroup_norm_le_one resolvent contraction step stepPositive time timeNonnegative)
      (norm_nonneg values)
    _ = ‖values‖ := one_mul _

#print axioms norm_exp_smul_le
#print axioms semigroup_eq_scalar_mul_exp
#print axioms semigroup_norm_le_one
#print axioms semigroup_add
#print axioms semigroup_continuous
#print axioms semigroup_apply_norm_le

end IGS.Sec31.BoundedYosida
