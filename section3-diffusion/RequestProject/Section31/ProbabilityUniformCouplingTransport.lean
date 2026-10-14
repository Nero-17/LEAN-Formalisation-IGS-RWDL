import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Uniformly close images of the same probability samples have the same
weak limit. The sample spaces may vary with the index. Bounded Lipschitz
tests suffice on a pseudometric target; separability, Polishness and an
external coupling theorem are not assumptions. -/

namespace IGS.Sec31
noncomputable section
open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

theorem probability_maps_same_limit_of_uniform_displacement
    {Space : Type*} [PseudoMetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    {Sample : ℕ → Type*} [∀ n, MeasurableSpace (Sample n)]
    (samples : ∀ n, ProbabilityMeasure (Sample n))
    (first second : ∀ n, Sample n → Space)
    (firstMeasurable : ∀ n, Measurable (first n)) (secondMeasurable : ∀ n, Measurable (second n))
    (radii : ℕ → ℝ) (radiiNonnegative : ∀ n, 0 ≤ radii n) (radiiZero : Tendsto radii atTop (𝓝 0))
    (close : ∀ n sample, dist (first n sample) (second n sample) ≤ radii n)
    (limit : ProbabilityMeasure Space)
    (secondConverges : Tendsto (fun n => (samples n).map (secondMeasurable n).aemeasurable) atTop (𝓝 limit)) :
    Tendsto (fun n => (samples n).map (firstMeasurable n).aemeasurable) atTop (𝓝 limit) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro test bounded lipschitz
  obtain ⟨constant, lipschitzBound⟩ := lipschitz
  let boundedTest : Space →ᵇ ℝ :=
    { toFun := test
      continuous_toFun := lipschitzBound.continuous
      map_bounded' := bounded }
  have firstIntegrable (n : ℕ) : Integrable (fun sample => test (first n sample)) (samples n : Measure (Sample n)) :=
    Integrable.of_bound (lipschitzBound.continuous.measurable.comp (firstMeasurable n)).aestronglyMeasurable
      ‖boundedTest‖ (ae_of_all _ fun sample => boundedTest.norm_coe_le_norm _)
  have secondIntegrable (n : ℕ) : Integrable (fun sample => test (second n sample)) (samples n : Measure (Sample n)) :=
    Integrable.of_bound (lipschitzBound.continuous.measurable.comp (secondMeasurable n)).aestronglyMeasurable
      ‖boundedTest‖ (ae_of_all _ fun sample => boundedTest.norm_coe_le_norm _)
  have integralDifference (n : ℕ) :
      dist (∫ point, test point ∂((samples n).map (firstMeasurable n).aemeasurable : Measure Space))
        (∫ point, test point ∂((samples n).map (secondMeasurable n).aemeasurable : Measure Space)) ≤
          (constant : ℝ) * radii n := by
    rw [Real.dist_eq, ← Real.norm_eq_abs]
    change ‖(∫ point, test point ∂(samples n : Measure (Sample n)).map (first n)) -
      (∫ point, test point ∂(samples n : Measure (Sample n)).map (second n))‖ ≤ _
    rw [integral_map (firstMeasurable n).aemeasurable lipschitzBound.continuous.measurable.aestronglyMeasurable,
      integral_map (secondMeasurable n).aemeasurable lipschitzBound.continuous.measurable.aestronglyMeasurable,
      ← integral_sub (firstIntegrable n) (secondIntegrable n)]
    have pointwise : ∀ᵐ sample ∂(samples n : Measure (Sample n)),
        ‖test (first n sample) - test (second n sample)‖ ≤ (constant : ℝ) * radii n :=
      ae_of_all _ fun sample => by
        rw [← dist_eq_norm]
        exact (lipschitzBound.dist_le_mul _ _).trans
          (mul_le_mul_of_nonneg_left (close n sample) constant.property)
    simpa using norm_integral_le_of_norm_le_const pointwise
  have differencesZero : Tendsto (fun n =>
      (∫ point, test point ∂((samples n).map (firstMeasurable n).aemeasurable : Measure Space)) -
        (∫ point, test point ∂((samples n).map (secondMeasurable n).aemeasurable : Measure Space))) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have distanceZero := squeeze_zero (fun n => dist_nonneg) integralDifference
      (by simpa only [mul_zero] using radiiZero.const_mul (constant : ℝ))
    simpa only [Real.norm_eq_abs, Real.dist_eq] using distanceZero
  have secondIntegrals := tendsto_iff_forall_lipschitz_integral_tendsto.mp secondConverges
    test bounded ⟨constant, lipschitzBound⟩
  simpa only [zero_add, sub_add_cancel] using differencesZero.add secondIntegrals

end
end IGS.Sec31

#print axioms IGS.Sec31.probability_maps_same_limit_of_uniform_displacement
