import RequestProject.Section31.FiniteSupportPathProductUniqueness
import RequestProject.Section31.FiniteBasisReindexedCompactness
import Mathlib.MeasureTheory.Measure.Prokhorov

/-! Tightness, continuity of cluster laws, and scalar product-observation
limits imply a full weak path limit. The inputs are explicit generic
criteria, to be supplied internally by the actual model consumer. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped UniformConvergence BigOperators BoundedContinuousFunction

variable {Time State : Type*} [TopologicalSpace Time]
variable [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable {History : ℕ → Type*} [∀ level, Finite (History level)]

theorem finiteSupportPath_weakLimit_product_integrals
    (paths : (level : ℕ) → History level → Time → State)
    (laws : ℕ → ProbabilityMeasure (FiniteSupportPathSpace paths))
    (limit : ProbabilityMeasure (FiniteSupportPathSpace paths))
    (weakConvergence : Tendsto laws atTop (𝓝 limit))
    (dimension : ℕ) (times : Fin dimension → Time) (tests : Fin dimension → State →ᵇ ℝ) :
    Tendsto (fun level => ∫ path, ∏ index, tests index (UniformFun.toFun path.val (times index))
      ∂(laws level : Measure (FiniteSupportPathSpace paths))) atTop
      (𝓝 (∫ path, ∏ index, tests index (UniformFun.toFun path.val (times index))
        ∂(limit : Measure (FiniteSupportPathSpace paths)))) := by
  let productFunction : (Fin dimension → State) →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact
      (FiniteProductWeak.productTest (fun index => (tests index).toContinuousMap))
  have evaluationContinuous := finiteSupportPathSpace_continuous_finite_evaluations paths dimension times
  have evaluationConvergence := finiteSupportPath_weakLimit_finite_evaluations paths laws limit
    weakConvergence dimension times
  have productConvergence := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    evaluationConvergence productFunction
  have integralIdentity (law : ProbabilityMeasure (FiniteSupportPathSpace paths)) :
      (∫ point, productFunction point ∂(law.map evaluationContinuous.measurable.aemeasurable : Measure _)) =
      ∫ path, ∏ index, tests index (UniformFun.toFun path.val (times index))
        ∂(law : Measure (FiniteSupportPathSpace paths)) := by
    change (∫ point, productFunction point ∂(law : Measure (FiniteSupportPathSpace paths)).map
      (fun path => fun index => UniformFun.toFun path.val (times index))) = _
    rw [integral_map evaluationContinuous.measurable.aemeasurable
      productFunction.continuous.measurable.aestronglyMeasurable]
    rfl
  simpa only [integralIdentity] using productConvergence

theorem finiteSupportPath_full_limit_of_product_observations
    (paths : (level : ℕ) → History level → Time → State)
    (laws : ℕ → ProbabilityMeasure (FiniteSupportPathSpace paths))
    (tightness : IsTightMeasureSet (Set.range
      (fun level => (laws level : Measure (FiniteSupportPathSpace paths)))))
    (continuousLimits : ∀ levels : ℕ → ℕ, StrictMono levels →
      ∀ limit : ProbabilityMeasure (FiniteSupportPathSpace paths),
        Tendsto (fun index => laws (levels index)) atTop (𝓝 limit) →
          ∀ᵐ path ∂(limit : Measure (FiniteSupportPathSpace paths)),
            Continuous (UniformFun.toFun path.val))
    (denseTimes : ℕ → Time) (timesDense : DenseRange denseTimes)
    (productLimits : ∀ (dimension : ℕ) (indices : Fin dimension → ℕ)
      (tests : Fin dimension → State →ᵇ ℝ), ∃ value : ℝ,
        Tendsto (fun level => ∫ path, ∏ index,
          tests index (UniformFun.toFun path.val (denseTimes (indices index)))
            ∂(laws level : Measure (FiniteSupportPathSpace paths))) atTop (𝓝 value)) :
    ∃ limit : ProbabilityMeasure (FiniteSupportPathSpace paths),
      Tendsto laws atTop (𝓝 limit) ∧
        ∀ᵐ path ∂(limit : Measure (FiniteSupportPathSpace paths)),
          Continuous (UniformFun.toFun path.val) := by
  have measuresRange :
      {((law : ProbabilityMeasure (FiniteSupportPathSpace paths)) : Measure (FiniteSupportPathSpace paths)) |
        law ∈ Set.range laws} = Set.range
          (fun level => (laws level : Measure (FiniteSupportPathSpace paths))) := by
    ext measure
    constructor
    · rintro ⟨law, ⟨level, rfl⟩, rfl⟩
      exact Set.mem_range_self level
    · rintro ⟨level, rfl⟩
      exact ⟨laws level, Set.mem_range_self level, rfl⟩
  have compact : IsCompact (closure (Set.range laws)) := by
    apply isCompact_closure_of_isTightMeasureSet
    rw [measuresRange]
    exact tightness
  obtain ⟨limit, _, levels, levelsStrict, weakConvergence⟩ :=
    compact.isSeqCompact (fun level => subset_closure (Set.mem_range_self level))
  have limitContinuous := continuousLimits levels levelsStrict limit weakConvergence
  refine ⟨limit, ?_, limitContinuous⟩
  apply IGS.Sec31.tendsto_of_every_strict_subsequence_has_further_limit laws limit
  intro selected selectedStrict
  obtain ⟨otherLimit, _, further, furtherStrict, otherConvergence⟩ :=
    compact.isSeqCompact (fun index => subset_closure (Set.mem_range_self (selected index)))
  have composedStrict : StrictMono (selected ∘ further) := selectedStrict.comp furtherStrict
  have otherContinuous := continuousLimits (selected ∘ further) composedStrict otherLimit otherConvergence
  have identification : otherLimit = limit := by
    apply finiteSupportPath_law_eq_of_dense_product_observations paths denseTimes timesDense
      otherLimit limit otherContinuous limitContinuous
    intro dimension indices tests
    obtain ⟨value, productConvergence⟩ := productLimits dimension indices tests
    have firstMoment := finiteSupportPath_weakLimit_product_integrals paths
      (fun index => laws (selected (further index))) otherLimit otherConvergence
      dimension (fun index => denseTimes (indices index)) tests
    have secondMoment := finiteSupportPath_weakLimit_product_integrals paths
      (fun index => laws (levels index)) limit weakConvergence
      dimension (fun index => denseTimes (indices index)) tests
    have firstValue := tendsto_nhds_unique firstMoment
      (productConvergence.comp composedStrict.tendsto_atTop)
    have secondValue := tendsto_nhds_unique secondMoment
      (productConvergence.comp levelsStrict.tendsto_atTop)
    exact firstValue.trans secondValue.symm
  exact ⟨further, identification ▸ otherConvergence⟩

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPath_weakLimit_product_integrals
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPath_full_limit_of_product_observations
