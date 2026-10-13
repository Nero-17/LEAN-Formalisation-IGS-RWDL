import RequestProject.Section31.CountableMarkovKernelEquality

/-! The zero-time kernel and measurable common sets for countable AE laws.
These statements do not assert a common set for uncountably many times. -/

namespace IGS.Sec31.CountableMarkov

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X]

theorem ae_kernel_eq_id_of_identity_representation
    (measure : Measure X) [IsFiniteMeasure measure]
    (kernel : Kernel X X) [IsMarkovKernel kernel]
    (tests : Submodule ℚ C(X, ℝ)) [Countable tests]
    (dense : Dense (tests : Set C(X, ℝ)))
    (representation : ∀ values : C(X, ℝ), ∀ᵐ point ∂measure,
      (∫ location, values location ∂kernel point) =
        ContinuousMap.toLp 2 measure ℝ values point) :
    ∀ᵐ point ∂measure, kernel point = Kernel.id point := by
  apply ae_kernel_eq_of_countable_continuous_tests measure kernel Kernel.id tests dense
  intro values
  filter_upwards [representation (values : C(X, ℝ)),
    ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) measure (values : C(X, ℝ))]
      with point integralIdentity inputIdentity
  rw [integralIdentity, inputIdentity, Kernel.id_apply, integral_dirac]

end IGS.Sec31.CountableMarkov

namespace IGS.Sec31

open MeasureTheory

theorem exists_measurable_full_set_of_countable_ae
    {X Index : Type*} [MeasurableSpace X] [Countable Index]
    (measure : Measure X) (predicate : Index → X → Prop)
    (laws : ∀ index, ∀ᵐ point ∂measure, predicate index point) :
    ∃ good : Set X, MeasurableSet good ∧ measure goodᶜ = 0 ∧
      ∀ point ∈ good, ∀ index, predicate index point := by
  have common : ∀ᵐ point ∂measure, ∀ index, predicate index point := ae_all_iff.mpr laws
  obtain ⟨bad, badContains, badMeasurable, badNull⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp common)
  refine ⟨badᶜ, badMeasurable.compl, ?_, ?_⟩
  · simpa only [compl_compl] using badNull
  · intro point pointGood
    by_contra failure
    exact pointGood (badContains failure)

end IGS.Sec31

#print axioms IGS.Sec31.CountableMarkov.ae_kernel_eq_id_of_identity_representation
#print axioms IGS.Sec31.exists_measurable_full_set_of_countable_ae
