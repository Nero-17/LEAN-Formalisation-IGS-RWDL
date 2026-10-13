import RequestProject.Section31.MarkovKernelIntegralInvariance

/-! Countably many dense continuous tests determine actual probability kernels
outside one null set. The common set is obtained by a countable intersection,
then the continuity of the integral extends equality to every continuous test. -/

namespace IGS.Sec31.CountableMarkov

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X]

noncomputable def continuousIntegralFunctional (measure : Measure X) [IsFiniteMeasure measure] :
    C(X, ℝ) →L[ℝ] ℝ :=
  (L1.integralCLM (α := X) (E := ℝ) (μ := measure)).comp (ContinuousMap.toLp 1 measure ℝ)

theorem continuousIntegralFunctional_apply (measure : Measure X) [IsFiniteMeasure measure]
    (values : C(X, ℝ)) :
    continuousIntegralFunctional measure values = ∫ location, values location ∂measure := by
  change L1.integralCLM (ContinuousMap.toLp 1 measure ℝ values) = _
  rw [← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 1) measure values)

theorem measure_eq_of_dense_continuous_integrals
    (first second : Measure X) [IsFiniteMeasure first] [IsFiniteMeasure second]
    (tests : Set C(X, ℝ)) (dense : Dense tests)
    (equalTests : ∀ values ∈ tests,
      (∫ location, values location ∂first) = ∫ location, values location ∂second) :
    first = second := by
  have functionalEquality :
      (continuousIntegralFunctional first : C(X, ℝ) → ℝ) = continuousIntegralFunctional second :=
    dense.denseRange_val.equalizer (continuousIntegralFunctional first).continuous
      (continuousIntegralFunctional second).continuous (by
        funext values
        exact (continuousIntegralFunctional_apply first values.val).trans
          ((equalTests values.val values.property).trans
            (continuousIntegralFunctional_apply second values.val).symm))
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro values
  simpa only [continuousIntegralFunctional_apply] using
    congr_fun functionalEquality values.toContinuousMap

theorem ae_kernel_eq_of_countable_continuous_tests
    (measure : Measure X) (first second : Kernel X X)
    [IsMarkovKernel first] [IsMarkovKernel second]
    (tests : Submodule ℚ C(X, ℝ)) [Countable tests]
    (dense : Dense (tests : Set C(X, ℝ)))
    (equalTests : ∀ values : tests, ∀ᵐ point ∂measure,
      (∫ location, (values : C(X, ℝ)) location ∂first point) =
        ∫ location, (values : C(X, ℝ)) location ∂second point) :
    ∀ᵐ point ∂measure, first point = second point := by
  have commonTests := ae_all_iff.mpr equalTests
  filter_upwards [commonTests] with point pointTests
  exact measure_eq_of_dense_continuous_integrals (first point) (second point)
    tests dense (fun values membership => pointTests ⟨values, membership⟩)

end IGS.Sec31.CountableMarkov

#print axioms IGS.Sec31.CountableMarkov.continuousIntegralFunctional_apply
#print axioms IGS.Sec31.CountableMarkov.measure_eq_of_dense_continuous_integrals
#print axioms IGS.Sec31.CountableMarkov.ae_kernel_eq_of_countable_continuous_tests
