import RequestProject.Section31.ExponentialResidualSequenceLaw

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 2200000

theorem exponential_residual_sequence_event_probability
    (elapsed : ℝ) (elapsedNonnegative : 0 ≤ elapsed)
    (future : Set (ℕ → ℝ)) (futureMeasurable : MeasurableSet future) :
    ((expMeasure 1).prod exponentialHoldingTimeLaw)
        {pair | elapsed < pair.1 ∧ prependHoldingTime (pair.1 - elapsed) pair.2 ∈ future} =
      ENNReal.ofReal (Real.exp (-elapsed)) * exponentialHoldingTimeLaw future := by
  have residualMeasurable : Measurable
      (fun pair : ℝ × (ℕ → ℝ) => prependHoldingTime (pair.1 - elapsed) pair.2) :=
    prependHoldingTime_measurable.comp
      ((measurable_fst.sub measurable_const).prodMk measurable_snd)
  have identity := congrArg (fun law : Measure (ℕ → ℝ) => law future)
    (exponential_residual_sequence_measure elapsed elapsedNonnegative)
  dsimp only at identity
  rw [Measure.map_apply residualMeasurable futureMeasurable,
    Measure.restrict_apply (futureMeasurable.preimage residualMeasurable),
    Measure.smul_apply] at identity
  have eventEquality :
      {pair : ℝ × (ℕ → ℝ) | elapsed < pair.1 ∧
        prependHoldingTime (pair.1 - elapsed) pair.2 ∈ future} =
      (fun pair : ℝ × (ℕ → ℝ) => prependHoldingTime (pair.1 - elapsed) pair.2) ⁻¹' future ∩
        (Ioi elapsed ×ˢ univ) := by
    ext pair
    simp only [mem_setOf_eq, mem_inter_iff, mem_preimage, mem_prod, mem_Ioi,
      mem_univ, true_and, and_true, and_comm]
  rw [eventEquality]
  exact identity

/-- A measurable arrival and arbitrary finite history only change the
survival weight. The entire regenerated future keeps its original law. -/
theorem exponential_survival_regeneration_factorization
    {Prefix : Type*} [MeasurableSpace Prefix]
    (prefixLaw : Measure Prefix) [SFinite prefixLaw]
    (arrival : Prefix → ℝ) (arrivalMeasurable : Measurable arrival) (time : ℝ)
    (history : Set Prefix) (historyMeasurable : MeasurableSet history)
    (future : Set (ℕ → ℝ)) (futureMeasurable : MeasurableSet future) :
    (prefixLaw.prod ((expMeasure 1).prod exponentialHoldingTimeLaw))
        {sample | arrival sample.1 ≤ time ∧ sample.1 ∈ history ∧
          time - arrival sample.1 < sample.2.1 ∧
          prependHoldingTime (sample.2.1 - (time - arrival sample.1)) sample.2.2 ∈ future} =
      (prefixLaw.prod ((expMeasure 1).prod exponentialHoldingTimeLaw))
          {sample | arrival sample.1 ≤ time ∧ sample.1 ∈ history ∧
            time - arrival sample.1 < sample.2.1} * exponentialHoldingTimeLaw future := by
  have baseMeasurable : MeasurableSet
      {sample : Prefix × (ℝ × (ℕ → ℝ)) | arrival sample.1 ≤ time ∧
        sample.1 ∈ history ∧ time - arrival sample.1 < sample.2.1} :=
    (measurableSet_le (arrivalMeasurable.comp measurable_fst) measurable_const).inter
      ((historyMeasurable.preimage measurable_fst).inter
        (measurableSet_lt (measurable_const.sub (arrivalMeasurable.comp measurable_fst))
          (measurable_fst.comp measurable_snd)))
  have residualMeasurable : Measurable
      (fun sample : Prefix × (ℝ × (ℕ → ℝ)) =>
        prependHoldingTime (sample.2.1 - (time - arrival sample.1)) sample.2.2) :=
    prependHoldingTime_measurable.comp
      (((measurable_fst.comp measurable_snd).sub
        (measurable_const.sub (arrivalMeasurable.comp measurable_fst))).prodMk
          (measurable_snd.comp measurable_snd))
  have fullMeasurable : MeasurableSet
      {sample : Prefix × (ℝ × (ℕ → ℝ)) | arrival sample.1 ≤ time ∧ sample.1 ∈ history ∧
        time - arrival sample.1 < sample.2.1 ∧
        prependHoldingTime (sample.2.1 - (time - arrival sample.1)) sample.2.2 ∈ future} := by
    convert baseMeasurable.inter (futureMeasurable.preimage residualMeasurable) using 1
    ext sample
    simp only [mem_inter_iff, mem_setOf_eq, mem_preimage, and_assoc]
  rw [Measure.prod_apply fullMeasurable, Measure.prod_apply baseMeasurable,
    ← lintegral_mul_const' _ _ (measure_ne_top exponentialHoldingTimeLaw future)]
  apply lintegral_congr
  intro historyPoint
  by_cases admitted : arrival historyPoint ≤ time ∧ historyPoint ∈ history
  · have elapsedNonnegative : 0 ≤ time - arrival historyPoint := sub_nonneg.mpr admitted.1
    have futureSection :
        {pair : ℝ × (ℕ → ℝ) | arrival historyPoint ≤ time ∧ historyPoint ∈ history ∧
          time - arrival historyPoint < pair.1 ∧
          prependHoldingTime (pair.1 - (time - arrival historyPoint)) pair.2 ∈ future} =
        {pair | time - arrival historyPoint < pair.1 ∧
          prependHoldingTime (pair.1 - (time - arrival historyPoint)) pair.2 ∈ future} := by
      ext pair
      simp only [mem_setOf_eq, admitted.1, admitted.2, true_and]
    have baseSection :
        {pair : ℝ × (ℕ → ℝ) | arrival historyPoint ≤ time ∧ historyPoint ∈ history ∧
          time - arrival historyPoint < pair.1} = Ioi (time - arrival historyPoint) ×ˢ univ := by
      ext pair
      simp only [mem_setOf_eq, admitted.1, admitted.2, true_and, mem_prod,
        mem_Ioi, mem_univ, and_true]
    change ((expMeasure 1).prod exponentialHoldingTimeLaw)
      {pair | arrival historyPoint ≤ time ∧ historyPoint ∈ history ∧ time - arrival historyPoint < pair.1 ∧
        prependHoldingTime (pair.1 - (time - arrival historyPoint)) pair.2 ∈ future} =
      ((expMeasure 1).prod exponentialHoldingTimeLaw)
        {pair | arrival historyPoint ≤ time ∧ historyPoint ∈ history ∧
          time - arrival historyPoint < pair.1} * exponentialHoldingTimeLaw future
    rw [futureSection, exponential_residual_sequence_event_probability _ elapsedNonnegative future futureMeasurable,
      baseSection, Measure.prod_prod, measure_univ, mul_one,
      unit_exponential_tail_probability _ elapsedNonnegative]
  · have rejected : ¬ (arrival historyPoint ≤ time ∧ historyPoint ∈ history) := admitted
    have fullEmpty :
        {pair : ℝ × (ℕ → ℝ) | arrival historyPoint ≤ time ∧ historyPoint ∈ history ∧
          time - arrival historyPoint < pair.1 ∧
          prependHoldingTime (pair.1 - (time - arrival historyPoint)) pair.2 ∈ future} = ∅ := by
      ext pair
      simp only [mem_setOf_eq, mem_empty_iff_false]
      tauto
    have baseEmpty :
        {pair : ℝ × (ℕ → ℝ) | arrival historyPoint ≤ time ∧ historyPoint ∈ history ∧
          time - arrival historyPoint < pair.1} = ∅ := by
      ext pair
      simp only [mem_setOf_eq, mem_empty_iff_false]
      tauto
    change ((expMeasure 1).prod exponentialHoldingTimeLaw)
      {pair | arrival historyPoint ≤ time ∧ historyPoint ∈ history ∧ time - arrival historyPoint < pair.1 ∧
        prependHoldingTime (pair.1 - (time - arrival historyPoint)) pair.2 ∈ future} =
      ((expMeasure 1).prod exponentialHoldingTimeLaw)
        {pair | arrival historyPoint ≤ time ∧ historyPoint ∈ history ∧
          time - arrival historyPoint < pair.1} * exponentialHoldingTimeLaw future
    rw [fullEmpty, baseEmpty, measure_empty, zero_mul]

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.exponential_residual_sequence_event_probability
#print axioms IGS.Sec31.PoissonClock.exponential_survival_regeneration_factorization
