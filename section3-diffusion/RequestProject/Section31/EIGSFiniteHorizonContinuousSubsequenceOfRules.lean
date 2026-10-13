import RequestProject.Section31.EIGSFiniteHorizonPathTightnessOfRules
import RequestProject.Section31.FiniteSupportPathContinuousLimit
import Mathlib.MeasureTheory.Measure.Prokhorov

/-! Subsequence existence for the actual finite-horizon floor-clock Xi walks.
For each fixed horizon and each family of initial distributions, the actual
path laws have a weakly convergent subsequence with strictly increasing
levels, and the limiting paths are almost surely continuous. This statement
does not assert uniqueness of that limit or convergence of the full sequence. -/

namespace EIGS

open MeasureTheory ProbabilityTheory Set Filter Topology
open IGS.Sec31.DiscreteMarkov
open scoped Classical NNReal UniformConvergence
noncomputable section
set_option maxHeartbeats 4000000

variable {K : ℕ}

theorem exists_xiFiniteHorizonNativeStepLaw_continuous_subsequence_of_rules
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (horizon : ℝ≥0) (initial : (level : ℕ) → ProbabilityMeasure (XiVtx system level)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    letI : CompactSpace parameters.LimitSpace :=
      xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
    letI : MeasurableSpace parameters.LimitSpace := borel _
    letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
    let rates := xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive
      normalization normalizationPositive
    let kernels := fun level =>
      xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level
    let paths := finiteHorizonStepPaths horizon rates parameters.vertexEmbedding
    let laws := fun level => finiteHorizonStepLaw horizon rates parameters.vertexEmbedding kernels initial level
    ∃ levels : ℕ → ℕ, StrictMono levels ∧
      ∃ limit : ProbabilityMeasure (FiniteSupportPathSpace paths),
        Tendsto (fun index => laws (levels index)) atTop (𝓝 limit) ∧
          ∀ᵐ path ∂(limit : Measure (FiniteSupportPathSpace paths)), Continuous (UniformFun.toFun path.val) := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI : CompactSpace parameters.LimitSpace :=
    xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  letI : MeasurableSpace parameters.LimitSpace := borel _
  letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  let rates := xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive
    normalization normalizationPositive
  let kernels := fun level =>
    xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level
  let paths := finiteHorizonStepPaths horizon rates parameters.vertexEmbedding
  let laws := fun level => finiteHorizonStepLaw horizon rates parameters.vertexEmbedding kernels initial level
  have tightness : IsTightMeasureSet (Set.range (fun level => (laws level : Measure (FiniteSupportPathSpace paths)))) :=
    xiFiniteHorizonNativeStepLaw_isTight_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive normalization normalizationPositive horizon initial
  have measuresRange :
      {((law : ProbabilityMeasure (FiniteSupportPathSpace paths)) : Measure (FiniteSupportPathSpace paths)) |
        law ∈ Set.range laws} = Set.range (fun level => (laws level : Measure (FiniteSupportPathSpace paths))) := by
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
  obtain ⟨limit, _, levels, levelsStrictMono, weakConvergence⟩ :=
    compact.isSeqCompact (fun level => subset_closure (Set.mem_range_self level))
  dsimp only
  refine ⟨levels, levelsStrictMono, limit, weakConvergence, ?_⟩
  apply finiteSupportPath_weakLimit_ae_continuous_of_asymptotic_modulus_toReal paths laws
    ?_ ?_ levels levelsStrictMono.tendsto_atTop limit weakConvergence
  · exact finiteHorizonStepLaw_ae_level_support horizon rates parameters.vertexEmbedding kernels initial
  · intro error errorPositive probabilityTolerance probabilityPositive
    obtain ⟨coarse, window, windowPositive, _, modulusBound⟩ :=
      exists_xiAsymptoticPathModulus_of_rules system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive normalization normalizationPositive
          (horizon : ℝ) error probabilityTolerance 1 horizon.property errorPositive probabilityPositive
            (by norm_num)
    refine ⟨window, windowPositive, coarse, ?_⟩
    intro level levelLarge
    obtain ⟨steps, rfl⟩ := Nat.exists_eq_add_of_le levelLarge
    change ((finiteHorizonStepLaw horizon rates parameters.vertexEmbedding kernels initial
      (coarse + steps) : Measure (FiniteSupportPathSpace paths))
        (finiteSupportPathModulusSet paths window error)ᶜ).toReal ≤ probabilityTolerance
    rw [finiteHorizonStepLaw_modulus_compl]
    have nativeBound := modulusBound steps (initial (coarse + steps))
    simpa only [rates, kernels, parameters, xiNativeFiniteJumpRateNNReal,
      xiNativeDiscreteKernel, xiActualPathModulusEvent] using nativeBound.le

end
end EIGS

#print axioms EIGS.exists_xiFiniteHorizonNativeStepLaw_continuous_subsequence_of_rules
