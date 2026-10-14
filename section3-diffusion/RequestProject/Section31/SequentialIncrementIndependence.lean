import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory
noncomputable section
set_option maxHeartbeats 1800000

theorem sequential_independence_prefix_product
    {Sample Value : Type*} [MeasurableSpace Sample] [MeasurableSpace Value]
    (law : Measure Sample) [IsProbabilityMeasure law]
    (randomValues : ℕ → Sample → Value)
    (sequential : ∀ count, IndepFun (fun sample =>
      fun index : Fin count => randomValues index.val sample) (randomValues count) law)
    (events : ℕ → Set Value) (eventsMeasurable : ∀ index, MeasurableSet (events index))
    (count : ℕ) :
    law {sample | ∀ index : Fin count, randomValues index.val sample ∈ events index.val} =
      ∏ index : Fin count, law (randomValues index.val ⁻¹' events index.val) := by
  classical
  induction count with
  | zero => simp
  | succ count inductionHypothesis =>
    have prefixMeasurable : MeasurableSet
        {values : Fin count → Value | ∀ index, values index ∈ events index.val} := by
      convert MeasurableSet.iInter (fun index : Fin count =>
        (eventsMeasurable index.val).preimage (measurable_pi_apply index)) using 1
      ext values
      simp
    have eventEquality :
        {sample | ∀ index : Fin (count + 1), randomValues index.val sample ∈ events index.val} =
        (fun sample => fun index : Fin count => randomValues index.val sample) ⁻¹'
          {values | ∀ index, values index ∈ events index.val} ∩
          randomValues count ⁻¹' events count := by
      ext sample
      constructor
      · intro all
        exact ⟨fun index => all index.castSucc, all (Fin.last count)⟩
      · rintro ⟨past, current⟩ index
        by_cases before : index.val < count
        · exact past ⟨index.val, before⟩
        · have last : index.val = count := by omega
          simpa only [last] using current
    rw [eventEquality,
      (sequential count).measure_inter_preimage_eq_mul _ _ prefixMeasurable
        (eventsMeasurable count)]
    change law {sample | ∀ index : Fin count,
      randomValues index.val sample ∈ events index.val} * _ = _
    rw [inductionHypothesis, Fin.prod_univ_castSucc]
    rfl

theorem iIndepFun_of_sequential_prefix_independence
    {Sample Value : Type*} [MeasurableSpace Sample] [MeasurableSpace Value]
    (law : Measure Sample) [IsProbabilityMeasure law]
    (randomValues : ℕ → Sample → Value)
    (sequential : ∀ count, IndepFun (fun sample =>
      fun index : Fin count => randomValues index.val sample) (randomValues count) law) :
    iIndepFun randomValues law := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro indices events eventsMeasurable
  let count := indices.sup id + 1
  let selectedEvents : ℕ → Set Value := fun index =>
    if index ∈ indices then events index else Set.univ
  have selectedMeasurable : ∀ index, MeasurableSet (selectedEvents index) := by
    intro index
    by_cases member : index ∈ indices
    · simpa only [selectedEvents, if_pos member] using eventsMeasurable index member
    · simp only [selectedEvents, if_neg member]
      exact MeasurableSet.univ
  have before : ∀ index ∈ indices, index < count := by
    intro index member
    have bounded : index ≤ indices.sup id := Finset.le_sup (f := id) member
    dsimp [count]
    omega
  have eventEquality :
      (⋂ index ∈ indices, randomValues index ⁻¹' events index) =
      {sample | ∀ index : Fin count,
        randomValues index.val sample ∈ selectedEvents index.val} := by
    ext sample
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · intro all index
      dsimp [selectedEvents]
      split_ifs with member
      · exact all index.val member
      · exact Set.mem_univ _
    · intro all index member
      have selected := all ⟨index, before index member⟩
      simpa only [selectedEvents, if_pos member] using selected
  rw [eventEquality,
    sequential_independence_prefix_product law randomValues sequential
      selectedEvents selectedMeasurable count]
  rw [← Finset.prod_range (fun index => law (randomValues index ⁻¹' selectedEvents index))]
  have contained : indices ⊆ Finset.range count := by
    intro index member
    exact Finset.mem_range.mpr (before index member)
  calc
    (∏ index ∈ Finset.range count, law (randomValues index ⁻¹' selectedEvents index)) =
        ∏ index ∈ indices, law (randomValues index ⁻¹' selectedEvents index) := by
      symm
      apply Finset.prod_subset contained
      intro index _ absent
      simp only [selectedEvents, if_neg absent, Set.preimage_univ, measure_univ]
    _ = ∏ index ∈ indices, law (randomValues index ⁻¹' events index) := by
      apply Finset.prod_congr rfl
      intro index member
      simp only [selectedEvents, if_pos member]

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.sequential_independence_prefix_product
#print axioms IGS.Sec31.PoissonClock.iIndepFun_of_sequential_prefix_independence
