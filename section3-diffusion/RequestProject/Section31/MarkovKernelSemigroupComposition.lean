import RequestProject.Section31.MarkovKernelBoundedApproximation
import RequestProject.Section31.CountableMarkovKernelEquality

/-! Actual composition of invariant Markov kernels representing a real L2
semigroup. Bounded-L2 representation handles the intermediate operator
output. Invariance transfers the inner kernel's AE representative equality,
and a countable dense test family gives AE equality of actual measures.
This generic bridge does not remove exceptional starting points or assert
one common good set for uncountably many pairs of times. -/

namespace IGS.Sec31.CountableMarkov

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ProbabilityTheory NNReal

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
    (measure : Measure X) [IsFiniteMeasure measure]

theorem ae_kernel_composition_integral
    (firstOperator secondOperator : Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (firstKernel secondKernel : Kernel X X)
    [IsMarkovKernel firstKernel] [IsMarkovKernel secondKernel]
    (firstInvariant : firstKernel.Invariant measure)
    (firstRepresentation : ∀ values : C(X, ℝ), ∀ᵐ point ∂measure,
      (∫ location, values location ∂firstKernel point) =
        firstOperator (ContinuousMap.toLp 2 measure ℝ values) point)
    (secondRepresentation : ∀ values : C(X, ℝ), ∀ᵐ point ∂measure,
      (∫ location, values location ∂secondKernel point) =
        secondOperator (ContinuousMap.toLp 2 measure ℝ values) point)
    (secondBound : ∀ values : C(X, ℝ), ∀ᵐ point ∂measure,
      ‖secondOperator (ContinuousMap.toLp 2 measure ℝ values) point‖ ≤ ‖values‖)
    (values : C(X, ℝ)) :
    ∀ᵐ point ∂measure,
      (∫ location, values location ∂(secondKernel ∘ₖ firstKernel) point) =
        firstOperator (secondOperator (ContinuousMap.toLp 2 measure ℝ values)) point := by
  have secondIdentityComposed : ∀ᵐ location ∂(firstKernel ∘ₘ measure),
      (∫ target, values target ∂secondKernel location) =
        secondOperator (ContinuousMap.toLp 2 measure ℝ values) location := by
    simpa only [firstInvariant.def] using secondRepresentation values
  have secondIdentityTransported := Measure.ae_ae_of_ae_comp secondIdentityComposed
  have boundedRepresentation := ae_kernel_integral_of_bounded_L2 measure firstOperator
    firstKernel firstInvariant firstRepresentation
    (secondOperator (ContinuousMap.toLp 2 measure ℝ values)) ‖values‖ (norm_nonneg values)
    (secondBound values)
  filter_upwards [secondIdentityTransported, boundedRepresentation]
    with point secondIdentity boundedIdentity
  have integrable : Integrable values ((secondKernel ∘ₖ firstKernel) point) :=
    Integrable.of_bound values.continuous.measurable.aestronglyMeasurable ‖values‖
      (Eventually.of_forall values.norm_coe_le_norm)
  calc
    (∫ location, values location ∂(secondKernel ∘ₖ firstKernel) point) =
        ∫ location, ∫ target, values target ∂secondKernel location ∂firstKernel point :=
      Kernel.integral_comp integrable
    _ = ∫ location, secondOperator (ContinuousMap.toLp 2 measure ℝ values) location ∂firstKernel point :=
      integral_congr_ae secondIdentity
    _ = firstOperator (secondOperator (ContinuousMap.toLp 2 measure ℝ values)) point :=
      boundedIdentity

theorem ae_kernels_add_of_semigroup
    (tests : Submodule ℚ C(X, ℝ)) [Countable tests]
    (dense : Dense (tests : Set C(X, ℝ)))
    (semigroup : ℝ≥0 → Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (transition : ℝ≥0 → Kernel X X)
    (markov : ∀ time, IsMarkovKernel (transition time))
    (invariant : ∀ time, (transition time).Invariant measure)
    (representation : ∀ (time : ℝ≥0) (values : C(X, ℝ)), ∀ᵐ point ∂measure,
      (∫ location, values location ∂transition time point) =
        semigroup time (ContinuousMap.toLp 2 measure ℝ values) point)
    (bounded : ∀ (time : ℝ≥0) (values : C(X, ℝ)), ∀ᵐ point ∂measure,
      ‖semigroup time (ContinuousMap.toLp 2 measure ℝ values) point‖ ≤ ‖values‖)
    (addLaw : ∀ firstTime secondTime,
      semigroup (firstTime + secondTime) = (semigroup firstTime).comp (semigroup secondTime))
    (firstTime secondTime : ℝ≥0) :
    ∀ᵐ point ∂measure,
      (transition secondTime ∘ₖ transition firstTime) point =
        transition (firstTime + secondTime) point := by
  letI : IsMarkovKernel (transition firstTime) := markov firstTime
  letI : IsMarkovKernel (transition secondTime) := markov secondTime
  letI : IsMarkovKernel (transition (firstTime + secondTime)) := markov (firstTime + secondTime)
  apply ae_kernel_eq_of_countable_continuous_tests measure _ _ tests dense
  intro values
  have composite := ae_kernel_composition_integral measure (semigroup firstTime) (semigroup secondTime)
    (transition firstTime) (transition secondTime) (invariant firstTime)
    (representation firstTime) (representation secondTime) (bounded secondTime)
    (values : C(X, ℝ))
  filter_upwards [composite, representation (firstTime + secondTime) (values : C(X, ℝ))]
    with point compositeIdentity sumIdentity
  calc
    (∫ location, (values : C(X, ℝ)) location ∂(transition secondTime ∘ₖ transition firstTime) point) =
        semigroup firstTime (semigroup secondTime (ContinuousMap.toLp 2 measure ℝ (values : C(X, ℝ)))) point :=
      compositeIdentity
    _ = semigroup (firstTime + secondTime) (ContinuousMap.toLp 2 measure ℝ (values : C(X, ℝ))) point := by
      rw [addLaw firstTime secondTime]
      rfl
    _ = ∫ location, (values : C(X, ℝ)) location ∂transition (firstTime + secondTime) point :=
      sumIdentity.symm

end IGS.Sec31.CountableMarkov

#print axioms IGS.Sec31.CountableMarkov.ae_kernel_composition_integral
#print axioms IGS.Sec31.CountableMarkov.ae_kernels_add_of_semigroup
