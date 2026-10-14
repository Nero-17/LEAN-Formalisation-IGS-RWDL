import RequestProject.Section31.TightnessFromShrinkingCompactCapture
import RequestProject.Section31.VanishingRadiusDiagonal

namespace IGS.Sec31.DiscreteMarkov
noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology
set_option maxHeartbeats 5000000

theorem isTight_of_constructed_couplings
    {Space : Type*} [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (Outcome : ℕ → Type*) [∀ index, MeasurableSpace (Outcome index)]
    (joint : ∀ index, Measure (Outcome index)) [∀ index, IsProbabilityMeasure (joint index)]
    (source target : ∀ index, Outcome index → Space)
    (sourceMeasurable : ∀ index, AEMeasurable (source index) (joint index))
    (targetMeasurable : ∀ index, AEMeasurable (target index) (joint index))
    (sourceLaws targetLaws : ℕ → ProbabilityMeasure Space)
    (sourceMarginal : ∀ index, (joint index).map (source index) = (sourceLaws index : Measure Space))
    (targetMarginal : ∀ index, (joint index).map (target index) = (targetLaws index : Measure Space))
    (sourceTight : IsTightMeasureSet (Set.range (fun index => (sourceLaws index : Measure Space))))
    (eachTargetTight : ∀ index, IsTightMeasureSet {(targetLaws index : Measure Space)})
    (coupling : ∀ radius error : ℝ, 0 < radius → 0 < error → ∀ᶠ index in atTop,
      ∃ bad : Set (Outcome index), (joint index).real bad ≤ error ∧
        ∀ᵐ sample ∂joint index, sample ∉ bad → dist (target index sample) (source index sample) ≤ radius) :
    IsTightMeasureSet (Set.range (fun index => (targetLaws index : Measure Space))) := by
  classical
  apply isTight_of_singleton_tight_and_shrinking_compact_capture targetLaws eachTargetTight
  intro error errorPositive
  let allowance : ℝ := min (error / 2) (1 / 2)
  have allowancePositive : 0 < allowance := lt_min (by positivity) (by norm_num)
  obtain ⟨limitSet, limitCompact, sourceBound⟩ :=
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp sourceTight)
      (ENNReal.ofReal allowance) (ENNReal.ofReal_pos.mpr allowancePositive)
  have sourceRealBound (index : ℕ) : (sourceLaws index : Measure Space).real limitSetᶜ ≤ allowance := by
    have bound := sourceBound _ (Set.mem_range_self index)
    have realBound := ENNReal.toReal_mono ENNReal.ofReal_ne_top bound
    simpa only [measureReal_def, ENNReal.toReal_ofReal allowancePositive.le] using realBound
  have limitNonempty : limitSet.Nonempty := by
    by_contra empty
    have equality : limitSet = ∅ := Set.not_nonempty_iff_eq_empty.mp empty
    have impossible := sourceRealBound 0
    rw [equality, compl_empty, measureReal_univ_eq_one] at impossible
    have small : allowance ≤ (1 / 2 : ℝ) := min_le_right _ _
    linarith
  obtain ⟨errors, errorsPositive, errorsVanish, threshold, good⟩ :=
    exists_vanishing_positive_radii_of_eventual
      (fun index radius => ∃ bad : Set (Outcome index), (joint index).real bad ≤ error / 2 ∧
        ∀ᵐ sample ∂joint index, sample ∉ bad → dist (target index sample) (source index sample) ≤ radius)
      (fun radius radiusPositive => coupling radius (error / 2) radiusPositive (by positivity))
  refine ⟨limitSet, limitCompact, limitNonempty, errors, fun index => (errorsPositive index).le,
    errorsVanish, threshold, ?_⟩
  intro index afterThreshold
  obtain ⟨bad, badBound, outsideClose⟩ := good index afterThreshold
  have inclusion : ∀ᵐ sample ∂joint index,
      sample ∈ (target index) ⁻¹' (cthickening (errors index) limitSet)ᶜ →
        sample ∈ (source index) ⁻¹' limitSetᶜ ∪ bad := by
    filter_upwards [outsideClose] with sample close
    intro outside
    by_cases inBad : sample ∈ bad
    · exact Or.inr inBad
    · left
      change source index sample ∉ limitSet
      intro inLimit
      exact outside (mem_cthickening_of_dist_le _ _ _ _ inLimit (close inBad))
  have bound := ENNReal.toReal_mono (measure_ne_top (joint index) _) (measure_mono_ae inclusion)
  change (joint index).real ((target index) ⁻¹' (cthickening (errors index) limitSet)ᶜ) ≤
    (joint index).real ((source index) ⁻¹' limitSetᶜ ∪ bad) at bound
  have unionBound := measureReal_union_le (μ := joint index) ((source index) ⁻¹' limitSetᶜ) bad
  have sourceEquality : (joint index).real ((source index) ⁻¹' limitSetᶜ) =
      (sourceLaws index : Measure Space).real limitSetᶜ := by
    rw [← sourceMarginal index]
    change ((joint index) ((source index) ⁻¹' limitSetᶜ)).toReal =
      ((joint index).map (source index) limitSetᶜ).toReal
    exact congrArg ENNReal.toReal
      (Measure.map_apply_of_aemeasurable (sourceMeasurable index) limitCompact.isClosed.measurableSet.compl).symm
  have targetEquality : (joint index).real ((target index) ⁻¹' (cthickening (errors index) limitSet)ᶜ) =
      (targetLaws index : Measure Space).real (cthickening (errors index) limitSet)ᶜ := by
    rw [← targetMarginal index]
    change ((joint index) ((target index) ⁻¹' (cthickening (errors index) limitSet)ᶜ)).toReal =
      ((joint index).map (target index) (cthickening (errors index) limitSet)ᶜ).toReal
    exact congrArg ENNReal.toReal
      (Measure.map_apply_of_aemeasurable (targetMeasurable index) isClosed_cthickening.measurableSet.compl).symm
  rw [sourceEquality] at unionBound
  rw [targetEquality] at bound
  exact bound.trans (unionBound.trans (by
    have allowanceSmall : allowance ≤ error / 2 := min_le_left _ _
    linarith [sourceRealBound index]))

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.isTight_of_constructed_couplings
