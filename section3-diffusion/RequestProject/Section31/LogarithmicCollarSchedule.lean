import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Independently proved logarithmic collar schedules. These are scalar and
measure-theoretic leaves, not a heat-kernel lower estimate. Candidate source;
no compilation is claimed. -/

namespace EIGS
open Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

theorem logarithmic_ceiling_geometric_le (ratio width : ℝ)
    (ratioPositive : 0 < ratio) (ratioBelowOne : ratio < 1) (index : ℕ) :
    ratio ^ Nat.ceil (width * Real.log (index + 2 : ℝ)) ≤
      (index + 2 : ℝ) ^ (width * Real.log ratio) := by
  have basePositive : 0 < (index + 2 : ℝ) := by positivity
  calc
    _ = ratio ^ (Nat.ceil (width * Real.log (index + 2 : ℝ)) : ℝ) :=
      (Real.rpow_natCast ratio _).symm
    _ ≤ ratio ^ (width * Real.log (index + 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge ratioPositive ratioBelowOne.le (Nat.le_ceil _)
    _ = (index + 2 : ℝ) ^ (width * Real.log ratio) := by
      rw [Real.rpow_def_of_pos ratioPositive, Real.rpow_def_of_pos basePositive]
      congr 1
      ring

theorem summable_logarithmic_ceiling_geometric (ratio width : ℝ)
    (ratioPositive : 0 < ratio) (ratioBelowOne : ratio < 1)
    (widthLarge : 1 / Real.log ratio⁻¹ < width) :
    Summable (fun index : ℕ => ratio ^ Nat.ceil (width * Real.log (index + 2 : ℝ))) := by
  have inverseGreater : 1 < ratio⁻¹ := (one_lt_inv₀ ratioPositive).mpr ratioBelowOne
  have logarithmPositive : 0 < Real.log ratio⁻¹ := Real.log_pos inverseGreater
  have exponentBelow : width * Real.log ratio < -1 := by
    have inequality := (div_lt_iff₀ logarithmPositive).mp widthLarge
    rw [Real.log_inv] at inequality
    nlinarith
  have powers : Summable (fun index : ℕ => (index + 2 : ℝ) ^ (width * Real.log ratio)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (summable_nat_add_iff 2).mpr (Real.summable_nat_rpow.mpr exponentBelow)
  exact Summable.of_nonneg_of_le (fun index => pow_nonneg ratioPositive.le _) 
    (logarithmic_ceiling_geometric_le ratio width ratioPositive ratioBelowOne) powers

theorem logarithmic_ceiling_degree_cost_le (degreeRate width : ℝ)
    (degreeGreaterThanOne : 1 < degreeRate) (widthNonnegative : 0 ≤ width) (index : ℕ) :
    degreeRate ^ Nat.ceil (width * Real.log (index + 2 : ℝ)) ≤
      degreeRate * (index + 2 : ℝ) ^ (width * Real.log degreeRate) := by
  have degreePositive := zero_lt_one.trans degreeGreaterThanOne
  have basePositive : 0 < (index + 2 : ℝ) := by positivity
  have argumentNonnegative : 0 ≤ width * Real.log (index + 2 : ℝ) :=
    mul_nonneg widthNonnegative (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) index; linarith))
  calc
    _ = degreeRate ^ (Nat.ceil (width * Real.log (index + 2 : ℝ)) : ℝ) :=
      (Real.rpow_natCast degreeRate _).symm
    _ ≤ degreeRate ^ (width * Real.log (index + 2 : ℝ) + 1) :=
      Real.rpow_le_rpow_of_exponent_le degreeGreaterThanOne.le (Nat.ceil_lt_add_one argumentNonnegative).le
    _ = degreeRate * (index + 2 : ℝ) ^ (width * Real.log degreeRate) := by
      have identity : degreeRate ^ (width * Real.log (index + 2 : ℝ)) =
          (index + 2 : ℝ) ^ (width * Real.log degreeRate) := by
        rw [Real.rpow_def_of_pos degreePositive, Real.rpow_def_of_pos basePositive]
        congr 1
        ring
      rw [Real.rpow_add degreePositive, Real.rpow_one, identity, mul_comm]

theorem ae_eventually_avoid_logarithmic_collar {Point : Type*} [MeasurableSpace Point]
    (law : Measure Point) (collar : ℕ → Set Point) (coefficient ratio width : ℝ)
    (coefficientNonnegative : 0 ≤ coefficient)
    (ratioPositive : 0 < ratio) (ratioBelowOne : ratio < 1)
    (widthLarge : 1 / Real.log ratio⁻¹ < width)
    (probabilityBound : ∀ index, law (collar index) ≤ ENNReal.ofReal
      (coefficient * ratio ^ Nat.ceil (width * Real.log (index + 2 : ℝ)))) :
    ∀ᵐ point ∂law, ∀ᶠ index in atTop, point ∉ collar index := by
  apply ae_eventually_notMem
  apply ne_top_of_le_ne_top
    ((summable_logarithmic_ceiling_geometric ratio width ratioPositive ratioBelowOne widthLarge).mul_left
      coefficient).tsum_ofReal_ne_top
  exact ENNReal.tsum_le_tsum probabilityBound

theorem degree_logarithmic_collar_exponent (massRate degreeRate : ℝ)
    (degreeGreaterThanOne : 1 < degreeRate) (degreeMass : degreeRate < massRate) :
    Real.log degreeRate / (Real.log massRate - Real.log degreeRate) =
      1 / (Real.log massRate / Real.log degreeRate - 1) := by
  have degreeLogPositive := Real.log_pos degreeGreaterThanOne
  have differencePositive : 0 < Real.log massRate - Real.log degreeRate :=
    sub_pos.mpr (Real.log_lt_log (zero_lt_one.trans degreeGreaterThanOne) degreeMass)
  field_simp [degreeLogPositive.ne', differencePositive.ne']
  <;> ring

theorem eventually_logarithmic_ceiling_le_index (width : ℝ) :
    ∀ᶠ index : ℕ in atTop, Nat.ceil (width * Real.log (index + 2 : ℝ)) ≤ index := by
  have shiftedTendsto : Tendsto (fun index : ℕ => (index + 2 : ℝ)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro threshold
    filter_upwards [(tendsto_natCast_atTop_atTop :
      Tendsto (fun index : ℕ => (index : ℝ)) atTop atTop).eventually (eventually_ge_atTop threshold)] with index after
    linarith
  have quotientTendsto : Tendsto (fun index : ℕ => Real.log (index + 2 : ℝ) / index) atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_neg_cancel_right] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp shiftedTendsto
  have multiplied : Tendsto (fun index : ℕ => width * (Real.log (index + 2 : ℝ) / index))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using quotientTendsto.const_mul width
  filter_upwards [multiplied.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (0 : ℕ)] with index small indexPositive
  apply Nat.ceil_le.mpr
  have castPositive : 0 < (index : ℝ) := Nat.cast_pos.mpr indexPositive
  have inequality : width * Real.log (index + 2 : ℝ) / index < 1 := by
    simpa only [mul_zero, mul_div_assoc] using small
  exact ((div_lt_one castPositive).mp inequality).le

end
end EIGS

#print axioms EIGS.logarithmic_ceiling_geometric_le
#print axioms EIGS.summable_logarithmic_ceiling_geometric
#print axioms EIGS.logarithmic_ceiling_degree_cost_le
#print axioms EIGS.ae_eventually_avoid_logarithmic_collar
#print axioms EIGS.degree_logarithmic_collar_exponent
#print axioms EIGS.eventually_logarithmic_ceiling_le_index
