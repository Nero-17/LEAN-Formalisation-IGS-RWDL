import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Consume geometric lower ball masses at every small radius, with the
fixed spatial factor absorbed explicitly into the coefficient. -/

namespace IGS.Sec31
noncomputable section

theorem geometric_ball_mass_lower_all_radii
    (volume : ℝ → ℝ) (volumeMonotone : Monotone volume)
    (rate massRate exponent coefficient radiusFactor : ℝ)
    (rateGreaterThanOne : 1 < rate) (massPositive : 0 < massRate)
    (exponentNonnegative : 0 ≤ exponent) (growthIdentity : massRate = rate ^ exponent)
    (coefficientPositive : 0 < coefficient) (radiusFactorPositive : 0 < radiusFactor)
    (geometricLower : ∀ level : ℕ,
      coefficient / massRate ^ level ≤ volume (radiusFactor * rate⁻¹ ^ level)) :
    ∀ radius : ℝ, 0 < radius → radius ≤ radiusFactor →
      (coefficient / (massRate * radiusFactor ^ exponent)) * radius ^ exponent ≤ volume radius := by
  intro radius radiusPositive radiusSmall
  have ratePositive : 0 < rate := zero_lt_one.trans rateGreaterThanOne
  have ratioLarge : 1 ≤ radiusFactor / radius :=
    (le_div_iff₀ radiusPositive).mpr (by simpa only [one_mul] using radiusSmall)
  obtain ⟨level, powerLower, powerUpper⟩ := exists_nat_pow_near ratioLarge rateGreaterThanOne
  have innerRadius : radiusFactor * rate⁻¹ ^ (level + 1) < radius := by
    rw [inv_pow, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (pow_pos ratePositive (level + 1))).mpr
    simpa only [mul_comm] using (div_lt_iff₀ radiusPositive).mp powerUpper
  have outerRadius : radius ≤ radiusFactor * rate⁻¹ ^ level := by
    rw [inv_pow, ← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos ratePositive level)).mpr
    simpa only [mul_comm] using (le_div_iff₀ radiusPositive).mp powerLower
  have normalizedRadius : radius / radiusFactor ≤ rate⁻¹ ^ level :=
    (div_le_iff₀ radiusFactorPositive).mpr (by simpa only [mul_comm] using outerRadius)
  have powers : (rate⁻¹ ^ level) ^ exponent = (massRate ^ level)⁻¹ := by
    rw [inv_pow, Real.inv_rpow (pow_nonneg ratePositive.le level)]
    congr 1
    rw [growthIdentity, ← Real.rpow_mul_natCast ratePositive.le,
      mul_comm exponent, Real.rpow_natCast_mul ratePositive.le]
  have powerBound : (radius / radiusFactor) ^ exponent ≤ (massRate ^ level)⁻¹ := by
    rw [← powers]
    exact Real.rpow_le_rpow (div_nonneg radiusPositive.le radiusFactorPositive.le)
      normalizedRadius exponentNonnegative
  have multiplied := mul_le_mul_of_nonneg_left powerBound
    (div_pos coefficientPositive massPositive).le
  have profileIdentity :
      (coefficient / (massRate * radiusFactor ^ exponent)) * radius ^ exponent =
        (coefficient / massRate) * (radius / radiusFactor) ^ exponent := by
    rw [Real.div_rpow radiusPositive.le radiusFactorPositive.le]
    field_simp
  have geometricIdentity :
      (coefficient / massRate) * (massRate ^ level)⁻¹ = coefficient / massRate ^ (level + 1) := by
    rw [pow_succ]
    field_simp
  rw [profileIdentity]
  exact multiplied.trans (by
    rw [geometricIdentity]
    exact (geometricLower (level + 1)).trans (volumeMonotone innerRadius.le))

end
end IGS.Sec31

#print axioms IGS.Sec31.geometric_ball_mass_lower_all_radii
