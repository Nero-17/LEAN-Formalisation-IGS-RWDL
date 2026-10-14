import RequestProject.Section31.GammaExponentialMeasureConvolution
import RequestProject.Section31.ExponentialHoldingZeroCountProbability

/-! Probability of a time lying between a gamma arrival and the next
unit-exponential arrival. The density computation is supplied internally. -/

namespace IGS.Sec31
open ProbabilityTheory MeasureTheory Real Set
open scoped ENNReal NNReal Classical MeasureTheory
noncomputable section

 theorem gamma_exponential_interval_event_probability (count : ℕ) (time : ℝ) :
    (gammaMeasure ((count : ℝ) + 1) 1).prod (expMeasure 1)
      {pair : ℝ × ℝ | pair.1 ≤ time ∧ time < pair.1 + pair.2} =
        gammaPDF (((count + 1 : ℕ) : ℝ) + 1) 1 time := by
  letI : IsProbabilityMeasure (gammaMeasure ((count : ℝ) + 1) 1) :=
    isProbabilityMeasure_gammaMeasure (by positivity) zero_lt_one
  have regionMeasurable : MeasurableSet
      {pair : ℝ × ℝ | pair.1 ≤ time ∧ time < pair.1 + pair.2} :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_lt measurable_const (measurable_fst.add measurable_snd))
  have sectionProbability (first : ℝ) :
      expMeasure 1 {second : ℝ | first ≤ time ∧ time < first + second} = exponentialPDF 1 (time - first) := by
    by_cases beforeTime : first ≤ time
    · have sectionEquality : {second : ℝ | first ≤ time ∧ time < first + second} = Set.Ioi (time - first) := by
        ext second
        simp only [Set.mem_setOf_eq, beforeTime, true_and, Set.mem_Ioi]
        constructor <;> intro inequality <;> linarith
      rw [sectionEquality, PoissonClock.unit_exponential_tail_probability _ (sub_nonneg.mpr beforeTime),
        exponentialPDF_of_nonneg (sub_nonneg.mpr beforeTime)]
      simp only [one_mul]
    · have sectionEquality : {second : ℝ | first ≤ time ∧ time < first + second} = ∅ := by
        ext second
        simp only [Set.mem_setOf_eq, beforeTime, false_and, Set.mem_empty_iff_false]
      rw [sectionEquality, measure_empty, exponentialPDF_of_neg (sub_neg.mpr (lt_of_not_ge beforeTime))]
  rw [Measure.prod_apply regionMeasurable]
  change (∫⁻ first : ℝ, expMeasure 1 {second : ℝ | first ≤ time ∧ time < first + second}
    ∂gammaMeasure ((count : ℝ) + 1) 1) = _
  simp_rw [sectionProbability]
  have gammaMeasurable : Measurable (gammaPDF ((count : ℝ) + 1) 1) :=
    (measurable_gammaPDFReal ((count : ℝ) + 1) 1).ennreal_ofReal
  have tailMeasurable : Measurable (fun first : ℝ => exponentialPDF 1 (time - first)) :=
    (measurable_exponentialPDFReal 1).ennreal_ofReal.comp (measurable_const.sub measurable_id)
  rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul volume gammaMeasurable tailMeasurable]
  have reordered :
      (∫⁻ first : ℝ, gammaPDF ((count : ℝ) + 1) 1 first * exponentialPDF 1 (time - first)) =
        MeasureTheory.lconvolution (gammaPDF ((count : ℝ) + 1) 1) (exponentialPDF 1) volume time := by
    rw [MeasureTheory.lconvolution_def]
    apply lintegral_congr
    intro first
    congr 2
    ring
  change (∫⁻ first : ℝ, gammaPDF ((count : ℝ) + 1) 1 first * exponentialPDF 1 (time - first)) = _
  rw [reordered, gamma_natural_exponential_lconvolution]

end
end IGS.Sec31

#print axioms IGS.Sec31.gamma_exponential_interval_event_probability
