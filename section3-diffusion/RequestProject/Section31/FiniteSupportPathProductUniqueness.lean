import RequestProject.Section31.FiniteSupportPathLawUniqueness
import RequestProject.Section31.FiniteSupportPathWeakEvaluations
import RequestProject.Section31.EIGSStationaryFinitePrefixWeakLimit

/-! Finite continuous product observations determine continuous path laws.
The product-test density is the proved compact Stone--Weierstrass result.
Applications still have to identify these observations from the actual walk;
no stationary initial distribution enters this uniqueness criterion. -/

namespace IGS.Sec31.FiniteProductWeak

open MeasureTheory Filter Topology
open scoped BigOperators BoundedContinuousFunction

theorem probability_eq_of_product_integrals
    {Coordinates Space : Type*} [Fintype Coordinates] [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (first second : ProbabilityMeasure (Coordinates → Space))
    (sameProducts : ∀ tests : Coordinates → Space →ᵇ ℝ,
      (∫ point, ∏ coordinate, tests coordinate (point coordinate) ∂(first : Measure (Coordinates → Space))) =
      (∫ point, ∏ coordinate, tests coordinate (point coordinate) ∂(second : Measure (Coordinates → Space)))) :
    first = second := by
  have convergence : Tendsto (fun _ : ℕ => first) atTop (𝓝 second) := by
    apply weak_tendsto_of_product_integrals
    intro tests
    rw [← sameProducts tests]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique tendsto_const_nhds convergence

end IGS.Sec31.FiniteProductWeak

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory Filter Topology
open scoped UniformConvergence BigOperators BoundedContinuousFunction

variable {Time State : Type*} [TopologicalSpace Time]
variable [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable {History : ℕ → Type*} [∀ level, Finite (History level)]

theorem finiteSupportPath_law_eq_of_dense_product_observations
    (paths : (level : ℕ) → History level → Time → State)
    (denseTimes : ℕ → Time) (timesDense : DenseRange denseTimes)
    (first second : ProbabilityMeasure (FiniteSupportPathSpace paths))
    (firstContinuous : ∀ᵐ path ∂(first : Measure (FiniteSupportPathSpace paths)),
      Continuous (UniformFun.toFun path.val))
    (secondContinuous : ∀ᵐ path ∂(second : Measure (FiniteSupportPathSpace paths)),
      Continuous (UniformFun.toFun path.val))
    (sameProducts : ∀ (dimension : ℕ) (indices : Fin dimension → ℕ)
        (tests : Fin dimension → State →ᵇ ℝ),
      (∫ path, ∏ index, tests index (UniformFun.toFun path.val (denseTimes (indices index)))
        ∂(first : Measure (FiniteSupportPathSpace paths))) =
      (∫ path, ∏ index, tests index (UniformFun.toFun path.val (denseTimes (indices index)))
        ∂(second : Measure (FiniteSupportPathSpace paths)))) :
    first = second := by
  apply finiteSupportPath_law_eq_of_dense_finite_evaluations paths denseTimes timesDense
    first second firstContinuous secondContinuous
  intro dimension indices
  have evaluationContinuous := finiteSupportPathSpace_continuous_finite_evaluations paths dimension
    (fun index => denseTimes (indices index))
  let firstEvaluations := first.map evaluationContinuous.measurable.aemeasurable
  let secondEvaluations := second.map evaluationContinuous.measurable.aemeasurable
  have sameEvaluations : firstEvaluations = secondEvaluations := by
    apply FiniteProductWeak.probability_eq_of_product_integrals
    intro tests
    have productContinuous : Continuous (fun point : Fin dimension → State =>
        ∏ index, tests index (point index)) := by
      apply continuous_finset_prod
      intro index _
      exact (tests index).continuous.comp (continuous_apply index)
    change (∫ point, ∏ index, tests index (point index)
      ∂(first : Measure (FiniteSupportPathSpace paths)).map
        (fun path => fun index => UniformFun.toFun path.val (denseTimes (indices index)))) =
      (∫ point, ∏ index, tests index (point index)
        ∂(second : Measure (FiniteSupportPathSpace paths)).map
          (fun path => fun index => UniformFun.toFun path.val (denseTimes (indices index))))
    rw [integral_map evaluationContinuous.measurable.aemeasurable productContinuous.measurable.aestronglyMeasurable,
      integral_map evaluationContinuous.measurable.aemeasurable productContinuous.measurable.aestronglyMeasurable]
    exact sameProducts dimension indices tests
  exact congrArg (fun law : ProbabilityMeasure (Fin dimension → State) =>
    (law : Measure (Fin dimension → State))) sameEvaluations

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.FiniteProductWeak.probability_eq_of_product_integrals
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPath_law_eq_of_dense_product_observations
