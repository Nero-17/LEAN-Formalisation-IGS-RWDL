import RequestProject.Section31.ExponentialHoldingTimePaths
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace IGS.Sec31.PoissonClock
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

private theorem unitExponential_weighted_id :
    (fun value : ℝ => (exponentialPDF 1 value).toReal * value) =
      (Set.Ioi (0 : ℝ)).indicator (fun value => Real.exp (-value) * value) := by
  funext value
  by_cases positive : 0 < value
  · simp [exponentialPDF_eq, positive.le, ENNReal.toReal_ofReal,
      (Real.exp_pos _).le, Set.indicator, positive]
  · by_cases zero : value = 0
    · subst value
      simp
    · have negative : value < 0 := lt_of_le_of_ne (le_of_not_gt positive) zero
      simp [exponentialPDF_of_neg negative, Set.indicator, positive]

theorem unitExponential_integrable_id : Integrable (fun value : ℝ => value) (expMeasure 1) := by
  change Integrable (fun value : ℝ => value) (volume.withDensity (exponentialPDF 1))
  rw [integrable_withDensity_iff_integrable_smul' (f := exponentialPDF 1)
    ((measurable_exponentialPDFReal 1).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun value => by exact ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul, unitExponential_weighted_id]
  have gamma : IntegrableOn (fun value : ℝ => Real.exp (-value) * value) (Set.Ioi 0) := by
    convert Real.GammaIntegral_convergent (s := 2) (by norm_num) using 1 <;> norm_num
  exact gamma.integrable_indicator measurableSet_Ioi

theorem unitExponential_integral_id : ∫ value : ℝ, value ∂expMeasure 1 = 1 := by
  change (∫ value : ℝ, value ∂volume.withDensity (exponentialPDF 1)) = 1
  rw [integral_withDensity_eq_integral_toReal_smul (f := exponentialPDF 1)
    ((measurable_exponentialPDFReal 1).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun value => by exact ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul, unitExponential_weighted_id]
  rw [integral_indicator measurableSet_Ioi]
  have gamma := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 1)
    (by norm_num) (by norm_num)
  norm_num at gamma
  simpa [mul_comm] using gamma

/-- The actual independent exponential sequence has mean-one cumulative clock.
This is the clock law required for de-Poissonisation, stronger than nonexplosion. -/
theorem exponentialHoldingTimeLaw_clock_average :
    ∀ᵐ holdingTimes ∂exponentialHoldingTimeLaw,
      Tendsto (fun count => cumulativeHoldingTime holdingTimes count / (count : ℝ)) atTop (𝓝 1) := by
  have integrable : Integrable (fun holdingTimes : ℕ → ℝ => holdingTimes 0)
      exponentialHoldingTimeLaw := by
    have mapped : Integrable (fun value : ℝ => value)
        (exponentialHoldingTimeLaw.map (fun holdingTimes => holdingTimes 0)) := by
      rw [exponentialHoldingTimeLaw_eval]
      exact unitExponential_integrable_id
    exact mapped.comp_aemeasurable (measurable_pi_apply 0).aemeasurable
  have identical : ∀ index, IdentDistrib (fun holdingTimes : ℕ → ℝ => holdingTimes index)
      (fun holdingTimes : ℕ → ℝ => holdingTimes 0)
      exponentialHoldingTimeLaw exponentialHoldingTimeLaw := by
    intro index
    exact ⟨(measurable_pi_apply index).aemeasurable, (measurable_pi_apply 0).aemeasurable,
      by rw [exponentialHoldingTimeLaw_eval, exponentialHoldingTimeLaw_eval]⟩
  have averages := strong_law_ae (fun index (holdingTimes : ℕ → ℝ) => holdingTimes index)
    integrable (fun _ _ distinct => exponentialHoldingTimeLaw_independent.indepFun distinct) identical
  have mean : (∫ holdingTimes : ℕ → ℝ, holdingTimes 0 ∂exponentialHoldingTimeLaw) = 1 := by
    calc
      _ = ∫ value : ℝ, value ∂exponentialHoldingTimeLaw.map (fun holdingTimes => holdingTimes 0) :=
        (integral_map (measurable_pi_apply 0).aemeasurable
          (show AEStronglyMeasurable (fun value : ℝ => value) _ from measurable_id.aestronglyMeasurable)).symm
      _ = 1 := by rw [exponentialHoldingTimeLaw_eval, unitExponential_integral_id]
  rw [mean] at averages
  simpa only [smul_eq_mul, cumulativeHoldingTime, div_eq_mul_inv, mul_comm] using averages

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.unitExponential_integrable_id
#print axioms IGS.Sec31.PoissonClock.unitExponential_integral_id
#print axioms IGS.Sec31.PoissonClock.exponentialHoldingTimeLaw_clock_average

