import RequestProject.Section31.FiniteHorizonMarkovStepPathLaw

/-! Actual finite-horizon step laws are concentrated on the corresponding
finite-level support. This supplies the support premise of the common-space
tightness construction without a support assumption on the initial law. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable {Vertex : ℕ → Type*} [∀ level, Fintype (Vertex level)]
variable [∀ level, MeasurableSpace (Vertex level)]
variable [∀ level, MeasurableSingletonClass (Vertex level)]

theorem finiteHorizonStepLaw_ae_level_support
    (horizon : ℝ≥0) (rates : ℕ → ℝ≥0)
    (embedding : (level : ℕ) → Vertex level → State)
    (kernels : (level : ℕ) → Kernel (Vertex level) (Vertex level))
    [∀ level, IsMarkovKernel (kernels level)]
    (initial : (level : ℕ) → ProbabilityMeasure (Vertex level)) (level : ℕ) :
    ∀ᵐ path ∂(finiteHorizonStepLaw horizon rates embedding kernels initial level : Measure _),
      path ∈ Set.range (finitePathEmbedding (finiteHorizonStepPaths horizon rates embedding) level) := by
  change ∀ᵐ path ∂(finiteHorizonPrefixLaw horizon rates kernels initial level).map
      (finitePathEmbedding (finiteHorizonStepPaths horizon rates embedding) level),
    path ∈ Set.range (finitePathEmbedding (finiteHorizonStepPaths horizon rates embedding) level)
  exact ae_map_mem_range _
    (finitePathEmbedding_range_finite (finiteHorizonStepPaths horizon rates embedding) level).measurableSet _

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizonStepLaw_ae_level_support
