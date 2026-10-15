import RequestProject.Section31.IndependentWordBlocks
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The disjoint-word search ends at a polynomial times 2^width.
Consequently the retained-terminal degree gain 2^width dominates every
strictly sublinear power of that endpoint level. This is a deterministic
part of the logarithmic volume-fluctuation argument, not its geometry. -/

namespace EIGS
open Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 3000000

theorem renewal_word_endpoint_bounds (width : ℕ)
    (trial : Fin (renewalPhaseTrialCount width)) :
    width ≤ (trial.val + 1) * width ∧
      (trial.val + 1) * width ≤ (width + 1) ^ 3 * 2 ^ width := by
  constructor
  · exact le_mul_of_one_le_left (Nat.zero_le _) (by omega)
  · have trialBound : trial.val + 1 ≤ renewalPhaseTrialCount width := trial.isLt
    have upper := Nat.mul_le_mul_right width trialBound
    have widthBound := Nat.mul_le_mul_right ((width + 1) ^ 2 * 2 ^ width)
      (Nat.le_succ width)
    calc
      (trial.val + 1) * width ≤ renewalPhaseTrialCount width * width := upper
      _ = width * ((width + 1) ^ 2 * 2 ^ width) := by
        unfold renewalPhaseTrialCount
        ring
      _ ≤ (width + 1) * ((width + 1) ^ 2 * 2 ^ width) := widthBound
      _ = _ := by ring

theorem eventually_renewal_endpoint_power_cost (epsilon : ℝ)
    (epsilonPositive : 0 < epsilon) (epsilonBelowOne : epsilon < 1) :
    ∀ᶠ width : ℕ in atTop, ∀ endpoint : ℕ,
      endpoint ≤ (width + 1) ^ 3 * 2 ^ width →
      (endpoint : ℝ) ^ (1 - epsilon) ≤ (2 : ℝ) ^ width := by
  have ratioPositive : (0 : ℝ) < 2 ^ (-epsilon) := by positivity
  have ratioBelowOne : (2 : ℝ) ^ (-epsilon) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos epsilonPositive)
  have shifted := (tendsto_pow_const_mul_const_pow_of_lt_one 3
    ratioPositive.le ratioBelowOne).comp (tendsto_add_atTop_nat 1)
  have decays : Tendsto
      (fun width : ℕ => (width + 1 : ℝ) ^ 3 * ((2 : ℝ) ^ (-epsilon)) ^ width)
      atTop (𝓝 0) := by
    have multiplied := shifted.mul_const (((2 : ℝ) ^ (-epsilon))⁻¹)
    convert multiplied using 1
    · funext width
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp
    · simp
  have eventuallySmall := decays.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventuallySmall] with width small
  intro endpoint endpointUpper
  have upperReal : (endpoint : ℝ) ≤ (width + 1 : ℝ) ^ 3 * (2 : ℝ) ^ width := by
    exact_mod_cast endpointUpper
  have polynomialAboveOne : (1 : ℝ) ≤ (width + 1 : ℝ) ^ 3 :=
    one_le_pow₀ (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le width)))
  have exponentNonnegative : 0 ≤ 1 - epsilon := by linarith
  have polynomialPower : ((width + 1 : ℝ) ^ 3) ^ (1 - epsilon) ≤
      (width + 1 : ℝ) ^ 3 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      polynomialAboveOne (show 1 - epsilon ≤ 1 by linarith)
  have geometricIdentity :
      ((2 : ℝ) ^ (-epsilon)) ^ width * (2 : ℝ) ^ width =
        ((2 : ℝ) ^ width) ^ (1 - epsilon) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-epsilon)),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_natCast (2 : ℝ) width,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  calc
    (endpoint : ℝ) ^ (1 - epsilon) ≤
        ((width + 1 : ℝ) ^ 3 * (2 : ℝ) ^ width) ^ (1 - epsilon) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) upperReal exponentNonnegative
    _ = ((width + 1 : ℝ) ^ 3) ^ (1 - epsilon) *
        ((2 : ℝ) ^ width) ^ (1 - epsilon) :=
      Real.mul_rpow (by positivity) (by positivity)
    _ ≤ (width + 1 : ℝ) ^ 3 * ((2 : ℝ) ^ width) ^ (1 - epsilon) :=
      mul_le_mul_of_nonneg_right polynomialPower (by positivity)
    _ = ((width + 1 : ℝ) ^ 3 * ((2 : ℝ) ^ (-epsilon)) ^ width) *
        (2 : ℝ) ^ width := by rw [mul_assoc, geometricIdentity]
    _ ≤ (2 : ℝ) ^ width := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right small.le
        (show 0 ≤ (2 : ℝ) ^ width by positivity)

end
end EIGS

#print axioms EIGS.renewal_word_endpoint_bounds
#print axioms EIGS.eventually_renewal_endpoint_power_cost
