import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace IGS.Sec31.PoissonClock
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

instance unitExponential_probability : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure zero_lt_one

/-- Independent rate-one exponential holding times. -/
def exponentialHoldingTimeLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => expMeasure 1)

instance exponentialHoldingTimeLaw_probability : IsProbabilityMeasure exponentialHoldingTimeLaw := by
  unfold exponentialHoldingTimeLaw
  infer_instance

theorem exponentialHoldingTimeLaw_eval (index : ℕ) :
    exponentialHoldingTimeLaw.map (fun holdingTimes => holdingTimes index) = expMeasure 1 :=
  Measure.infinitePi_map_eval _ index

theorem exponentialHoldingTimeLaw_independent :
    iIndepFun (fun index (holdingTimes : ℕ → ℝ) => holdingTimes index) exponentialHoldingTimeLaw :=
  iIndepFun_infinitePi (X := fun _ value => value) (fun _ => measurable_id)

theorem exponentialHoldingTimeLaw_positive :
    ∀ᵐ holdingTimes ∂exponentialHoldingTimeLaw, ∀ index, 0 < holdingTimes index := by
  have exponentialPositive : ∀ᵐ value ∂expMeasure 1, 0 < value := by
    rw [ae_iff]
    have measureZero : expMeasure 1 (Set.Iic 0) = 0 := by
      rw [← ofReal_cdf, cdf_expMeasure_eq zero_lt_one]
      norm_num
    simpa only [Set.Iic, not_lt] using measureZero
  rw [ae_all_iff]
  intro index
  have mapped : ∀ᵐ value ∂exponentialHoldingTimeLaw.map (fun holdingTimes => holdingTimes index),
      0 < value := by
    rw [exponentialHoldingTimeLaw_eval]
    exact exponentialPositive
  exact ae_of_ae_map (measurable_pi_apply index).aemeasurable mapped

private def longHoldingIndicator : ℝ → ℝ := (Set.Ioi (1 : ℝ)).indicator (fun _ => 1)

private theorem longHoldingIndicator_measurable : Measurable longHoldingIndicator :=
  measurable_const.indicator measurableSet_Ioi

private theorem longHoldingIndicator_integral :
    ∫ holdingTimes, longHoldingIndicator (holdingTimes 0) ∂exponentialHoldingTimeLaw = Real.exp (-1) := by
  rw [← integral_map (measurable_pi_apply 0).aemeasurable
    longHoldingIndicator_measurable.stronglyMeasurable.aestronglyMeasurable,
    exponentialHoldingTimeLaw_eval]
  change (∫ value, (Set.Ioi (1 : ℝ)).indicator (fun _ => (1 : ℝ)) value ∂expMeasure 1) = _
  rw [integral_indicator_const 1 measurableSet_Ioi, smul_eq_mul, mul_one, ← Set.compl_Iic,
    measureReal_compl measurableSet_Iic, probReal_univ, ← cdf_eq_real,
    cdf_expMeasure_eq zero_lt_one]
  norm_num

/-- The cumulative holding times diverge almost surely. This supplies
nonexplosion without assuming any stochastic process existence theorem. -/
theorem exponentialHoldingTimeLaw_nonexplosion :
    ∀ᵐ holdingTimes ∂exponentialHoldingTimeLaw,
      Tendsto (fun count => ∑ index ∈ Finset.range count, holdingTimes index) atTop atTop := by
  have independent : iIndepFun
      (fun index (holdingTimes : ℕ → ℝ) => longHoldingIndicator (holdingTimes index))
      exponentialHoldingTimeLaw :=
    iIndepFun_infinitePi (X := fun _ => longHoldingIndicator) (fun _ => longHoldingIndicator_measurable)
  have identical : ∀ index, IdentDistrib
      (fun holdingTimes : ℕ → ℝ => longHoldingIndicator (holdingTimes index))
      (fun holdingTimes : ℕ → ℝ => longHoldingIndicator (holdingTimes 0))
      exponentialHoldingTimeLaw exponentialHoldingTimeLaw := by
    intro index
    have coordinates : IdentDistrib (fun holdingTimes : ℕ → ℝ => holdingTimes index)
        (fun holdingTimes : ℕ → ℝ => holdingTimes 0)
        exponentialHoldingTimeLaw exponentialHoldingTimeLaw :=
      ⟨(measurable_pi_apply index).aemeasurable, (measurable_pi_apply 0).aemeasurable,
        by rw [exponentialHoldingTimeLaw_eval, exponentialHoldingTimeLaw_eval]⟩
    exact coordinates.comp longHoldingIndicator_measurable
  have integrable : Integrable (fun holdingTimes : ℕ → ℝ => longHoldingIndicator (holdingTimes 0))
      exponentialHoldingTimeLaw := by
    change Integrable (((fun holdingTimes : ℕ → ℝ => holdingTimes 0) ⁻¹' Set.Ioi (1 : ℝ)).indicator
      (fun _ => (1 : ℝ))) exponentialHoldingTimeLaw
    exact (integrable_const 1).indicator (measurableSet_Ioi.preimage (measurable_pi_apply 0))
  have averages := strong_law_ae
    (fun index (holdingTimes : ℕ → ℝ) => longHoldingIndicator (holdingTimes index))
    integrable (fun _ _ distinct => independent.indepFun distinct) identical
  rw [longHoldingIndicator_integral] at averages
  filter_upwards [averages, exponentialHoldingTimeLaw_positive] with holdingTimes convergence positive
  have indicatorDivergence : Tendsto
      (fun count => ∑ index ∈ Finset.range count, longHoldingIndicator (holdingTimes index)) atTop atTop := by
    have multiplied := tendsto_natCast_atTop_atTop.atTop_mul_pos (Real.exp_pos (-1)) convergence
    apply multiplied.congr'
    filter_upwards [eventually_ne_atTop 0] with count countNonzero
    simp only [smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr countNonzero), one_mul]
  apply tendsto_atTop_mono _ indicatorDivergence
  intro count
  apply Finset.sum_le_sum
  intro index _
  change (Set.Ioi (1 : ℝ)).indicator (fun _ => (1 : ℝ)) (holdingTimes index) ≤ holdingTimes index
  by_cases long : 1 < holdingTimes index
  · simpa [Set.indicator, long] using long.le
  · simpa [Set.indicator, long] using (positive index).le

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.exponentialHoldingTimeLaw_independent
#print axioms IGS.Sec31.PoissonClock.exponentialHoldingTimeLaw_positive
#print axioms IGS.Sec31.PoissonClock.exponentialHoldingTimeLaw_nonexplosion

