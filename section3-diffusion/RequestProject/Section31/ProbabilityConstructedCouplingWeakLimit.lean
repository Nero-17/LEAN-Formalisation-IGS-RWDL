import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Weak limits are preserved by explicit varying-sample couplings whose
distance vanishes in probability. The proof uses bounded Lipschitz tests
and the actual sample measures; it does not use a Skorokhod representation,
separability, completeness, or a Polish assertion. -/

namespace IGS.Sec31
noncomputable section
open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction
set_option maxHeartbeats 5000000

theorem probability_maps_same_limit_of_constructed_coupling
    {Space : Type*} [PseudoMetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    {Sample : ℕ → Type*} [∀ index, MeasurableSpace (Sample index)]
    (samples : ∀ index, ProbabilityMeasure (Sample index))
    (source target : ∀ index, Sample index → Space)
    (sourceMeasurable : ∀ index, AEMeasurable (source index) (samples index : Measure _))
    (targetMeasurable : ∀ index, AEMeasurable (target index) (samples index : Measure _))
    (coupling : ∀ radius error : ℝ, 0 < radius → 0 < error → ∀ᶠ index in atTop,
      ∃ bad : Set (Sample index), MeasurableSet bad ∧ (samples index : Measure _).real bad ≤ error ∧
        ∀ᵐ sample ∂(samples index : Measure _), sample ∉ bad →
          dist (target index sample) (source index sample) ≤ radius)
    (limit : ProbabilityMeasure Space)
    (sourceConverges : Tendsto
      (fun index => ProbabilityMeasure.map (samples index) (sourceMeasurable index)) atTop (𝓝 limit)) :
    Tendsto (fun index => ProbabilityMeasure.map (samples index) (targetMeasurable index)) atTop (𝓝 limit) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro test bounded lipschitz
  obtain ⟨constant, lipschitzBound⟩ := lipschitz
  let boundedTest : Space →ᵇ ℝ :=
    { toFun := test
      continuous_toFun := lipschitzBound.continuous
      map_bounded' := bounded }
  have sourceIntegrable (index : ℕ) :
      Integrable (fun sample => test (source index sample)) (samples index : Measure _) :=
    Integrable.of_bound
      (lipschitzBound.continuous.measurable.aestronglyMeasurable.comp_aemeasurable (sourceMeasurable index))
      ‖boundedTest‖ (ae_of_all _ fun sample => boundedTest.norm_coe_le_norm _)
  have targetIntegrable (index : ℕ) :
      Integrable (fun sample => test (target index sample)) (samples index : Measure _) :=
    Integrable.of_bound
      (lipschitzBound.continuous.measurable.aestronglyMeasurable.comp_aemeasurable (targetMeasurable index))
      ‖boundedTest‖ (ae_of_all _ fun sample => boundedTest.norm_coe_le_norm _)
  have integralDifference (index : ℕ) (radius : ℝ) (radiusNonnegative : 0 ≤ radius)
      (bad : Set (Sample index)) (badMeasurable : MeasurableSet bad)
      (close : ∀ᵐ sample ∂(samples index : Measure _), sample ∉ bad →
        dist (target index sample) (source index sample) ≤ radius) :
      ‖(∫ point, test point ∂(ProbabilityMeasure.map (samples index) (targetMeasurable index) : Measure Space)) -
          (∫ point, test point ∂(ProbabilityMeasure.map (samples index) (sourceMeasurable index) : Measure Space))‖ ≤
        (constant : ℝ) * radius + 2 * ‖boundedTest‖ * (samples index : Measure _).real bad := by
    change ‖(∫ point, test point ∂(samples index : Measure _).map (target index)) -
      (∫ point, test point ∂(samples index : Measure _).map (source index))‖ ≤ _
    rw [integral_map (targetMeasurable index) lipschitzBound.continuous.measurable.aestronglyMeasurable,
      integral_map (sourceMeasurable index) lipschitzBound.continuous.measurable.aestronglyMeasurable,
      ← integral_sub (targetIntegrable index) (sourceIntegrable index),
      ← integral_add_compl badMeasurable ((targetIntegrable index).sub (sourceIntegrable index))]
    have badBound : ‖∫ sample in bad, test (target index sample) - test (source index sample)
        ∂(samples index : Measure _)‖ ≤ 2 * ‖boundedTest‖ * (samples index : Measure _).real bad := by
      apply norm_setIntegral_le_of_norm_le_const_ae' (measure_lt_top _ _)
      exact ae_of_all _ fun sample _ =>
        (norm_sub_le _ _).trans (by
          have first := boundedTest.norm_coe_le_norm (target index sample)
          have second := boundedTest.norm_coe_le_norm (source index sample)
          change ‖test (target index sample)‖ ≤ ‖boundedTest‖ at first
          change ‖test (source index sample)‖ ≤ ‖boundedTest‖ at second
          linarith)
    have goodBound : ‖∫ sample in badᶜ, test (target index sample) - test (source index sample)
        ∂(samples index : Measure _)‖ ≤ (constant : ℝ) * radius := by
      have bound : ‖∫ sample in badᶜ, test (target index sample) - test (source index sample)
          ∂(samples index : Measure _)‖ ≤ (constant : ℝ) * radius * (samples index : Measure _).real badᶜ := by
        apply norm_setIntegral_le_of_norm_le_const_ae' (measure_lt_top _ _)
        filter_upwards [close] with sample close
        intro outside
        rw [← dist_eq_norm]
        exact (lipschitzBound.dist_le_mul _ _).trans
          (mul_le_mul_of_nonneg_left (close outside) constant.property)
      exact bound.trans (by
        have massBound : (samples index : Measure _).real badᶜ ≤ 1 := measureReal_le_one
        exact (mul_le_mul_of_nonneg_left massBound (mul_nonneg constant.property radiusNonnegative)).trans_eq (mul_one _))
    exact (norm_add_le _ _).trans (by linarith)
  have differencesZero : Tendsto (fun index =>
      (∫ point, test point ∂(ProbabilityMeasure.map (samples index) (targetMeasurable index) : Measure Space)) -
        (∫ point, test point ∂(ProbabilityMeasure.map (samples index) (sourceMeasurable index) : Measure Space)))
      atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro error errorPositive
    let coefficient : ℝ := (constant : ℝ) + 2 * ‖boundedTest‖ + 1
    have coefficientPositive : 0 < coefficient := by dsimp [coefficient]; positivity
    let radius : ℝ := error / (2 * coefficient)
    have radiusPositive : 0 < radius := by dsimp [radius]; positivity
    filter_upwards [coupling radius radius radiusPositive radiusPositive] with index witness
    obtain ⟨bad, badMeasurable, badBound, close⟩ := witness
    have bound := integralDifference index radius radiusPositive.le bad badMeasurable close
    have estimate : (constant : ℝ) * radius + 2 * ‖boundedTest‖ * (samples index : Measure _).real bad ≤
        coefficient * radius := by
      have multiplied := mul_le_mul_of_nonneg_left badBound (by positivity : 0 ≤ 2 * ‖boundedTest‖)
      dsimp [coefficient]
      nlinarith
    have equality : coefficient * radius = error / 2 := by
      dsimp [radius]
      field_simp [ne_of_gt coefficientPositive] <;> ring
    have small := (bound.trans estimate).trans_lt (equality.trans_lt (half_lt_self errorPositive))
    simpa only [dist_zero_right] using small
  have sourceIntegrals := tendsto_iff_forall_lipschitz_integral_tendsto.mp sourceConverges
    test bounded ⟨constant, lipschitzBound⟩
  simpa only [zero_add, sub_add_cancel] using differencesZero.add sourceIntegrals

end
end IGS.Sec31

#print axioms IGS.Sec31.probability_maps_same_limit_of_constructed_coupling
