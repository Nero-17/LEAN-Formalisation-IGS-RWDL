import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Algebra for combining a harmonic point lower bound with the actual
projection tail. This separates the cancellation of mass from its analytic use. -/

namespace IGS.Sec31

theorem point_square_le_of_projection_bounds
    (value functionNorm projectionNorm energy coefficient tail : ℝ)
    (coefficientPositive : 0 < coefficient)
    (projectionNonnegative : 0 ≤ projectionNorm)
    (normNonnegative : 0 ≤ functionNorm)
    (energyNonnegative : 0 ≤ energy) (tailNonnegative : 0 ≤ tail)
    (pointBound : coefficient * value ^ 2 ≤ projectionNorm ^ 2)
    (projectionBound : projectionNorm ≤ functionNorm + tail * Real.sqrt energy) :
    value ^ 2 ≤ (2 / coefficient) * functionNorm ^ 2 +
      (2 * tail ^ 2 / coefficient) * energy := by
  have squaredBound := pow_le_pow_left₀ projectionNonnegative projectionBound 2
  have rootSquared := Real.sq_sqrt energyNonnegative
  have crossBound := sq_nonneg (functionNorm - tail * Real.sqrt energy)
  have upperBound : coefficient * value ^ 2 ≤ 2 * functionNorm ^ 2 + 2 * tail ^ 2 * energy := by
    nlinarith [sq_nonneg projectionNorm]
  have dividedBound : value ^ 2 ≤ (2 * functionNorm ^ 2 + 2 * tail ^ 2 * energy) / coefficient :=
    (le_div_iff₀ coefficientPositive).2 (by nlinarith [upperBound])
  convert dividedBound using 1 <;> ring

theorem projection_point_energy_coefficient
    (massRate resistanceRate constant pointConstant incidence : ℝ)
    (massPositive : 0 < massRate) (resistancePositive : 0 < resistanceRate)
    (pointConstantPositive : 0 < pointConstant) (incidencePositive : 0 < incidence)
    (level : ℕ) :
    2 * (constant * (Real.sqrt (massRate * resistanceRate))⁻¹ ^ level) ^ 2 /
      (pointConstant / massRate ^ level * incidence) =
      (2 * constant ^ 2 / pointConstant) * (1 / (incidence * resistanceRate ^ level)) := by
  have rootPower : ((Real.sqrt (massRate * resistanceRate))⁻¹ ^ level) ^ 2 =
      (massRate ^ level * resistanceRate ^ level)⁻¹ := by
    calc
      _ = ((Real.sqrt (massRate * resistanceRate))⁻¹ ^ 2) ^ level := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm level 2]
      _ = _ := by
        rw [inv_pow, Real.sq_sqrt (mul_pos massPositive resistancePositive).le, inv_pow, mul_pow]
  rw [mul_pow, rootPower]
  field_simp [ne_of_gt massPositive, ne_of_gt resistancePositive,
    ne_of_gt pointConstantPositive, ne_of_gt incidencePositive]
  <;> ring

end IGS.Sec31

#print axioms IGS.Sec31.point_square_le_of_projection_bounds
#print axioms IGS.Sec31.projection_point_energy_coefficient
