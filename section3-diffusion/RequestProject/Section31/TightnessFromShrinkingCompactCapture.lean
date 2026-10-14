import RequestProject.Section31.ShrinkingCompactCapture
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Topology.MetricSpace.Thickening

namespace IGS.Sec31.DiscreteMarkov
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
set_option maxHeartbeats 4000000

theorem isTight_of_real_compact_capture {Space : Type*} [MetricSpace Space]
    [MeasurableSpace Space] [BorelSpace Space] (laws : ℕ → ProbabilityMeasure Space)
    (capture : ∀ error : ℝ, 0 < error → ∃ compactSet : Set Space, IsCompact compactSet ∧
      ∀ index, (laws index : Measure Space).real compactSetᶜ ≤ error) :
    IsTightMeasureSet (Set.range (fun index => (laws index : Measure Space))) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro error errorPositive
  by_cases infinite : error = ∞
  · refine ⟨∅, isCompact_empty, ?_⟩
    intro law membership
    rw [infinite]
    exact le_top
  · obtain ⟨compactSet, compact, bound⟩ := capture error.toReal
      (ENNReal.toReal_pos errorPositive.ne' infinite)
    refine ⟨compactSet, compact, ?_⟩
    rintro _ ⟨index, rfl⟩
    calc
      (laws index : Measure Space) compactSetᶜ =
          ENNReal.ofReal ((laws index : Measure Space).real compactSetᶜ) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal error.toReal := ENNReal.ofReal_le_ofReal (bound index)
      _ = error := ENNReal.ofReal_toReal infinite

theorem isTight_of_singleton_tight_and_shrinking_compact_capture
    {Space : Type*} [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (laws : ℕ → ProbabilityMeasure Space)
    (eachTight : ∀ index, IsTightMeasureSet {(laws index : Measure Space)})
    (nearCapture : ∀ error : ℝ, 0 < error →
      ∃ limitSet : Set Space, IsCompact limitSet ∧ limitSet.Nonempty ∧
        ∃ errors : ℕ → ℝ, (∀ index, 0 ≤ errors index) ∧ Tendsto errors atTop (𝓝 0) ∧
          ∃ threshold : ℕ, ∀ index ≥ threshold,
            (laws index : Measure Space).real (cthickening (errors index) limitSet)ᶜ ≤ error) :
    IsTightMeasureSet (Set.range (fun index => (laws index : Measure Space))) := by
  classical
  apply isTight_of_real_compact_capture laws
  intro error errorPositive
  obtain ⟨limitSet, limitCompact, limitNonempty, errors, errorsNonnegative, errorsVanish,
      threshold, nearBound⟩ := nearCapture (error / 2) (by positivity)
  have individual : ∀ index, ∃ capture : Set Space, IsCompact capture ∧
      (laws index : Measure Space).real captureᶜ ≤ error / 2 := by
    intro index
    obtain ⟨capture, compact, bound⟩ :=
      (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp (eachTight index))
        (ENNReal.ofReal (error / 2)) (ENNReal.ofReal_pos.mpr (by positivity))
    refine ⟨capture, compact, ?_⟩
    have result := ENNReal.toReal_mono ENNReal.ofReal_ne_top (bound _ (by simp))
    simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity : 0 ≤ error / 2)] using result
  choose captures captureCompact captureBound using individual
  let trimmed := fun index => captures index ∩ cthickening (errors index) limitSet
  have trimmedCompact (index : ℕ) : IsCompact (trimmed index) :=
    (captureCompact index).inter_right isClosed_cthickening
  have trimmedNear : ∀ index, ∀ point ∈ trimmed index,
      ∃ limitPoint ∈ limitSet, dist point limitPoint ≤ errors index := by
    intro index point membership
    obtain ⟨limitPoint, inLimit, distanceEquality⟩ := limitCompact.exists_infEDist_eq_edist limitNonempty point
    refine ⟨limitPoint, inLimit, ?_⟩
    have bound := membership.2
    rw [mem_cthickening_iff, distanceEquality, edist_dist] at bound
    exact (ENNReal.ofReal_le_ofReal_iff (errorsNonnegative index)).mp bound
  have unionCompact := shrinking_compact_capture_union_isCompact limitSet limitCompact trimmed trimmedCompact
    errors errorsNonnegative errorsVanish trimmedNear
  refine ⟨(limitSet ∪ ⋃ index, trimmed index) ∪ accumulate captures threshold,
    unionCompact.union (isCompact_accumulate captureCompact threshold), ?_⟩
  intro index
  by_cases after : threshold ≤ index
  · have inclusion : ((limitSet ∪ ⋃ index, trimmed index) ∪ accumulate captures threshold)ᶜ ⊆
        (trimmed index)ᶜ := compl_subset_compl.mpr (by
      intro point inTrimmed
      exact Or.inl (Or.inr (mem_iUnion.mpr ⟨index, inTrimmed⟩)))
    have unionBound := measureReal_union_le (μ := (laws index : Measure Space))
      (captures index)ᶜ (cthickening (errors index) limitSet)ᶜ
    have small := add_le_add (captureBound index) (nearBound index after)
    calc
      (laws index : Measure Space).real _ ≤ (laws index : Measure Space).real (trimmed index)ᶜ :=
        measureReal_mono inclusion
      _ ≤ (laws index : Measure Space).real (captures index)ᶜ +
          (laws index : Measure Space).real (cthickening (errors index) limitSet)ᶜ := by
        simpa only [trimmed, compl_inter] using unionBound
      _ ≤ error := by linarith
  · have inclusion : ((limitSet ∪ ⋃ index, trimmed index) ∪ accumulate captures threshold)ᶜ ⊆
        (captures index)ᶜ := compl_subset_compl.mpr (by
      intro point inCapture
      exact Or.inr (mem_biUnion (Nat.le_of_lt (Nat.lt_of_not_ge after)) inCapture))
    exact (measureReal_mono inclusion).trans ((captureBound index).trans (by linarith))

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.isTight_of_real_compact_capture
#print axioms IGS.Sec31.DiscreteMarkov.isTight_of_singleton_tight_and_shrinking_compact_capture
