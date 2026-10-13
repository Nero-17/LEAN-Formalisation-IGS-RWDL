import Mathlib.Probability.Kernel.Invariance

/-! A countable family of invariant kernels has a common stable measurable
full-measure subset of any prescribed measurable full-measure set.
The construction repeatedly removes points that can enter an earlier bad set,
then intersects the countably many refinements. No topology, completeness of
the measure, finite total mass or time-regularity assumption is required. -/

namespace IGS.Sec31.CountableMarkov

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {X Index : Type*} [MeasurableSpace X] [Countable Index]

def stableRefinement (kernels : Index → Kernel X X) (initialGood : Set X) : ℕ → Set X
  | 0 => initialGood
  | index + 1 => stableRefinement kernels initialGood index ∩
      ⋂ kernelIndex, {point | kernels kernelIndex point (stableRefinement kernels initialGood index)ᶜ = 0}

theorem stableRefinement_measurable (kernels : Index → Kernel X X)
    (initialGood : Set X) (initialMeasurable : MeasurableSet initialGood)
    (index : ℕ) : MeasurableSet (stableRefinement kernels initialGood index) := by
  induction index with
  | zero => exact initialMeasurable
  | succ index measurable =>
    change MeasurableSet (stableRefinement kernels initialGood index ∩
      ⋂ kernelIndex, {point | kernels kernelIndex point (stableRefinement kernels initialGood index)ᶜ = 0})
    exact measurable.inter (MeasurableSet.iInter fun kernelIndex =>
      measurableSet_eq_fun ((kernels kernelIndex).measurable_coe measurable.compl) measurable_const)

theorem stableRefinement_full (measure : Measure X) (kernels : Index → Kernel X X)
    (invariant : ∀ kernelIndex, (kernels kernelIndex).Invariant measure)
    (initialGood : Set X) (initialNull : measure initialGoodᶜ = 0)
    (index : ℕ) : ∀ᵐ point ∂measure, point ∈ stableRefinement kernels initialGood index := by
  induction index with
  | zero => exact ae_iff.mpr initialNull
  | succ index full =>
    have avoidsPrevious : ∀ kernelIndex, ∀ᵐ point ∂measure,
        kernels kernelIndex point (stableRefinement kernels initialGood index)ᶜ = 0 := by
      intro kernelIndex
      have fullComposed : ∀ᵐ point ∂(kernels kernelIndex ∘ₘ measure),
          point ∈ stableRefinement kernels initialGood index := by
        simpa only [(invariant kernelIndex).def] using full
      have transferred := Measure.ae_ae_of_ae_comp fullComposed
      filter_upwards [transferred] with point pointFull
      exact ae_iff.mp pointFull
    filter_upwards [full, ae_all_iff.mpr avoidsPrevious] with point previous allKernels
    exact ⟨previous, Set.mem_iInter.mpr allKernels⟩

theorem exists_invariant_stable_full_set (measure : Measure X) (kernels : Index → Kernel X X)
    (invariant : ∀ kernelIndex, (kernels kernelIndex).Invariant measure)
    (initialGood : Set X) (initialMeasurable : MeasurableSet initialGood)
    (initialNull : measure initialGoodᶜ = 0) :
    ∃ good : Set X, MeasurableSet good ∧ good ⊆ initialGood ∧ measure goodᶜ = 0 ∧
      ∀ point ∈ good, ∀ kernelIndex, kernels kernelIndex point goodᶜ = 0 := by
  let good : Set X := ⋂ index : ℕ, stableRefinement kernels initialGood index
  have goodMeasurable : MeasurableSet good :=
    MeasurableSet.iInter (stableRefinement_measurable kernels initialGood initialMeasurable)
  have goodSubset : good ⊆ initialGood := by
    intro point membership
    exact Set.mem_iInter.mp membership 0
  have goodFull : ∀ᵐ point ∂measure, point ∈ good := by
    have allLayers := ae_all_iff.mpr (stableRefinement_full measure kernels invariant initialGood initialNull)
    simpa only [good, Set.mem_iInter] using allLayers
  refine ⟨good, goodMeasurable, goodSubset, ae_iff.mp goodFull, ?_⟩
  intro point membership kernelIndex
  have avoidsAllLayers : ∀ index : ℕ,
      kernels kernelIndex point (stableRefinement kernels initialGood index)ᶜ = 0 := by
    intro index
    have nextLayer := Set.mem_iInter.mp membership (index + 1)
    exact Set.mem_iInter.mp nextLayer.2 kernelIndex
  simpa only [good, Set.compl_iInter] using measure_iUnion_null avoidsAllLayers

end IGS.Sec31.CountableMarkov

#print axioms IGS.Sec31.CountableMarkov.stableRefinement_measurable
#print axioms IGS.Sec31.CountableMarkov.stableRefinement_full
#print axioms IGS.Sec31.CountableMarkov.exists_invariant_stable_full_set
