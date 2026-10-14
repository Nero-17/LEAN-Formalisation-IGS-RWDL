import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! The tail-integral formula includes infinite exit times. The Fatou
step controls the whole expectation, rather than integrating a Markov
bound proportional to the reciprocal of time. -/

namespace IGS.Sec31
open MeasureTheory Filter Set
open scoped ENNReal
noncomputable section

theorem ennreal_eq_lintegral_positive_tail (value : ℝ≥0∞) :
    value = ∫⁻ time in Ioi (0 : ℝ),
      if ENNReal.ofReal time < value then (1 : ℝ≥0∞) else 0 := by
  by_cases infinite : value = ∞
  · subst value
    simp
  · have equality :
        (∫⁻ time in Ioi (0 : ℝ), if ENNReal.ofReal time < value then (1 : ℝ≥0∞) else 0) =
          ∫⁻ time in Ioi (0 : ℝ), (Iio value.toReal).indicator (fun _ => (1 : ℝ≥0∞)) time := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with time positive
      simp only [Set.indicator_apply, Set.mem_Iio]
      simp only [ENNReal.ofReal_lt_iff_lt_toReal positive.le infinite]
    rw [equality, lintegral_indicator measurableSet_Iio, lintegral_const, one_mul,
      Measure.restrict_apply_univ,
      Measure.restrict_apply measurableSet_Iio]
    have intersection : Iio value.toReal ∩ Ioi (0 : ℝ) = Ioo 0 value.toReal := by
      ext time
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_Ioo]
      exact and_comm
    rw [intersection, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal infinite]

theorem lintegral_exit_eq_positive_tail {Path : Type*} [MeasurableSpace Path]
    (law : Measure Path) [SFinite law] (exit : Path → ℝ≥0∞) (exitMeasurable : Measurable exit) :
    (∫⁻ path, exit path ∂law) =
      ∫⁻ time in Ioi (0 : ℝ), law {path | ENNReal.ofReal time < exit path} := by
  have indicatorMeasurable : Measurable (fun point : Path × ℝ =>
      if ENNReal.ofReal point.2 < exit point.1 then (1 : ℝ≥0∞) else 0) := by
    exact Measurable.ite
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd)
        (exitMeasurable.comp measurable_fst)) measurable_const measurable_const
  calc
    (∫⁻ path, exit path ∂law) =
        ∫⁻ path, (∫⁻ time in Ioi (0 : ℝ),
          if ENNReal.ofReal time < exit path then (1 : ℝ≥0∞) else 0) ∂law :=
      lintegral_congr fun path => ennreal_eq_lintegral_positive_tail (exit path)
    _ = ∫⁻ time in Ioi (0 : ℝ), ∫⁻ path,
          if ENNReal.ofReal time < exit path then (1 : ℝ≥0∞) else 0 ∂law :=
      lintegral_lintegral_swap indicatorMeasurable.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro time
      have measurableEvent : MeasurableSet {path | ENNReal.ofReal time < exit path} :=
        measurableSet_lt measurable_const exitMeasurable
      simpa only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply] using
        (lintegral_indicator_one (μ := law) measurableEvent)

theorem positive_tail_mean_upper_of_liminf {Path : Type*} [MeasurableSpace Path]
    (law : Measure Path) [SFinite law] (exit : Path → ℝ≥0∞) (exitMeasurable : Measurable exit)
    (finiteTails : ℕ → ℝ → ℝ≥0∞)
    (finiteTailsMeasurable : ∀ level, Measurable (finiteTails level))
    (tailComparison : ∀ time, 0 < time →
      law {path | ENNReal.ofReal time < exit path} ≤ liminf (fun level => finiteTails level time) atTop)
    (upper : ℝ≥0∞)
    (finiteMeanUpper : ∀ level, (∫⁻ time in Ioi (0 : ℝ), finiteTails level time) ≤ upper) :
    (∫⁻ path, exit path ∂law) ≤ upper := by
  rw [lintegral_exit_eq_positive_tail law exit exitMeasurable]
  calc
    (∫⁻ time in Ioi (0 : ℝ), law {path | ENNReal.ofReal time < exit path}) ≤
        ∫⁻ time in Ioi (0 : ℝ), liminf (fun level => finiteTails level time) atTop := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with time positive
      exact tailComparison time positive
    _ ≤ liminf (fun level => ∫⁻ time in Ioi (0 : ℝ), finiteTails level time) atTop :=
      lintegral_liminf_le finiteTailsMeasurable
    _ ≤ upper := liminf_le_of_frequently_le' (Filter.Frequently.of_forall finiteMeanUpper)

end
end IGS.Sec31

#print axioms IGS.Sec31.ennreal_eq_lintegral_positive_tail
#print axioms IGS.Sec31.lintegral_exit_eq_positive_tail
#print axioms IGS.Sec31.positive_tail_mean_upper_of_liminf
