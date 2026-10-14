import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Order.Archimedean.Basic

/-! A measurable version of the eventual pointwise heat lower bound.
For fixed positive coefficient and threshold its good set is an arbitrary
intersection of spatially closed sets. Countable Archimedean quantization
therefore permits address-law AE transfer for all real times, with no
rational-time approximation or time-continuity premise.
Candidate source: no compilation is claimed. -/

namespace IGS.Sec31
open MeasureTheory
open scoped Topology
noncomputable section

theorem isClosed_local_lower_goodset
    {Space : Type*} [TopologicalSpace Space]
    (kernel : ℝ → Space → ℝ) (kernelContinuous : ∀ time, 0 < time → Continuous (kernel time))
    (weight : ℝ → ℝ) (coefficient threshold : ℝ) :
    IsClosed {point : Space | ∀ time : ℝ, 0 < time → time ≤ threshold →
      coefficient * weight time ≤ kernel time point} := by
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro time
  apply isClosed_iInter
  intro timePositive
  apply isClosed_iInter
  intro timeSmall
  exact isClosed_le continuous_const (kernelContinuous time timePositive)

theorem measurableSet_quantized_local_lower
    {Space : Type*} [TopologicalSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (kernel : ℝ → Space → ℝ) (kernelContinuous : ∀ time, 0 < time → Continuous (kernel time))
    (weight : ℝ → ℝ) (threshold : ℕ → ℝ) :
    MeasurableSet {point : Space | ∃ coefficientIndex thresholdIndex : ℕ,
      ∀ time : ℝ, 0 < time → time ≤ threshold thresholdIndex →
      (1 / ((coefficientIndex : ℝ) + 1)) * weight time ≤ kernel time point} := by
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro coefficientIndex
  apply MeasurableSet.iUnion
  intro thresholdIndex
  exact (isClosed_local_lower_goodset kernel kernelContinuous weight
    (1 / ((coefficientIndex : ℝ) + 1)) (threshold thresholdIndex)).measurableSet

theorem local_lower_archimedean_quantization
    {Space : Type*} (kernel : ℝ → Space → ℝ) (weight : ℝ → ℝ)
    (clip : ℝ) (weightNonnegative : ∀ time, 0 < time → time ≤ clip → 0 ≤ weight time)
    (point : Space) (coefficient threshold : ℝ)
    (coefficientPositive : 0 < coefficient) (thresholdPositive : 0 < threshold)
    (lower : ∀ time, 0 < time → time < threshold → coefficient * weight time ≤ kernel time point) :
    ∃ coefficientIndex thresholdIndex : ℕ, ∀ time : ℝ, 0 < time →
      time ≤ min clip (1 / ((thresholdIndex : ℝ) + 1)) →
      (1 / ((coefficientIndex : ℝ) + 1)) * weight time ≤ kernel time point := by
  obtain ⟨coefficientIndex, coefficientBound⟩ := exists_nat_one_div_lt coefficientPositive
  obtain ⟨thresholdIndex, thresholdBound⟩ := exists_nat_one_div_lt thresholdPositive
  refine ⟨coefficientIndex, thresholdIndex, ?_⟩
  intro time timePositive timeSmall
  exact (mul_le_mul_of_nonneg_right coefficientBound.le
    (weightNonnegative time timePositive (timeSmall.trans (min_le_left _ _)))).trans
    (lower time timePositive ((timeSmall.trans (min_le_right _ _)).trans_lt thresholdBound))

theorem ae_quantized_local_lower_map
    {Address Space : Type*} [MeasurableSpace Address]
    [TopologicalSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (law : Measure Address) (limit : Address → Space) (limitMeasurable : Measurable limit)
    (kernel : ℝ → Space → ℝ) (kernelContinuous : ∀ time, 0 < time → Continuous (kernel time))
    (weight : ℝ → ℝ) (threshold : ℕ → ℝ)
    (addressLower : ∀ᵐ address ∂law, ∃ coefficientIndex thresholdIndex : ℕ,
      ∀ time : ℝ, 0 < time → time ≤ threshold thresholdIndex →
      (1 / ((coefficientIndex : ℝ) + 1)) * weight time ≤ kernel time (limit address)) :
    ∀ᵐ point ∂law.map limit, ∃ coefficientIndex thresholdIndex : ℕ,
      ∀ time : ℝ, 0 < time → time ≤ threshold thresholdIndex →
      (1 / ((coefficientIndex : ℝ) + 1)) * weight time ≤ kernel time point :=
  (ae_map_iff limitMeasurable.aemeasurable
    (measurableSet_quantized_local_lower kernel kernelContinuous weight threshold)).mpr addressLower

end
end IGS.Sec31

#print axioms IGS.Sec31.isClosed_local_lower_goodset
#print axioms IGS.Sec31.measurableSet_quantized_local_lower
#print axioms IGS.Sec31.local_lower_archimedean_quantization
#print axioms IGS.Sec31.ae_quantized_local_lower_map
