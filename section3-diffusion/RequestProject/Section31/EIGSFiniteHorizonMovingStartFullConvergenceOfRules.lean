import RequestProject.Section31.EIGSNativeSupArbitraryMovingStartProducts
import RequestProject.Section31.EIGSFiniteHorizonContinuousSubsequenceOfRules
import RequestProject.Section31.FiniteSupportPathFullConvergence

/-! Full finite-horizon weak path convergence for the actual floor-clock walk
from every geometrically convergent family of starting vertices. The native
resistance rate is identified with the canonical spectral radius internally.
Tightness and continuity of all cluster laws are supplied by the actual rules;
arbitrary finite product limits identify every cluster law. The same clock,
normalization and coherent continuous-semigroup family are retained. No Hunt
process or compatibility between different horizons is asserted here. -/

namespace EIGS

open MeasureTheory ProbabilityTheory Set Filter Topology IGS.Sec31
open IGS.Sec31.DiscreteMarkov
open scoped Classical NNReal UniformConvergence BigOperators BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

def XiFiniteHorizonMovingStartFullConvergenceProperties (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization) : Prop :=
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  ∀ (horizon : ℝ≥0) (starts : ∀ level, XiVtx system level) (start : parameters.LimitSpace),
    Tendsto (fun level => parameters.vertexEmbedding level (starts level)) atTop (𝓝 start) →
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    letI : CompactSpace parameters.LimitSpace :=
      xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
    letI : MeasurableSpace parameters.LimitSpace := borel _
    letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
    let initial : (level : ℕ) → ProbabilityMeasure (XiVtx system level) :=
      fun level => ⟨Measure.dirac (starts level), inferInstance⟩
    let rates := xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive
      normalization normalizationPositive
    let kernels := fun level =>
      xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level
    let paths := finiteHorizonStepPaths horizon rates parameters.vertexEmbedding
    let laws := fun level => finiteHorizonStepLaw horizon rates parameters.vertexEmbedding kernels initial level
    ∃ limit : ProbabilityMeasure (FiniteSupportPathSpace paths),
      Tendsto laws atTop (𝓝 limit) ∧
        ∀ᵐ path ∂(limit : Measure (FiniteSupportPathSpace paths)), Continuous (UniformFun.toFun path.val)

theorem xiFiniteHorizonMovingStartFullConvergenceProperties_of_arbitraryProducts (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (arbitraryProperties : XiNativeSupArbitraryProductProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate normalization) :
    XiFiniteHorizonMovingStartFullConvergenceProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive normalization normalizationPositive := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have rateEquality := system.resistanceSpectralRadius_eq_of_positive_eigenpair rulesConnected distancePositive
    ratePositive vectorPositive (funext renormalizationEigenpair)
  have canonicalProducts : XiNativeSupArbitraryProductProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive (system.resistanceSpectralRadius rulesConnected distancePositive)
      normalization := by
    rw [← rateEquality]
    exact arbitraryProperties
  dsimp only [XiNativeSupArbitraryProductProperties] at canonicalProducts
  dsimp only [XiFiniteHorizonMovingStartFullConvergenceProperties]
  intro horizon starts start startsConverge
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI : CompactSpace parameters.LimitSpace :=
    xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  letI : MeasurableSpace parameters.LimitSpace := borel _
  letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  let initial : (level : ℕ) → ProbabilityMeasure (XiVtx system level) :=
    fun level => ⟨Measure.dirac (starts level), inferInstance⟩
  let rates := xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive
    normalization normalizationPositive
  let kernels := fun level =>
    xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level
  let paths := finiteHorizonStepPaths horizon rates parameters.vertexEmbedding
  let laws := fun level => finiteHorizonStepLaw horizon rates parameters.vertexEmbedding kernels initial level
  have tightness : IsTightMeasureSet (Set.range (fun level => (laws level : Measure (FiniteSupportPathSpace paths)))) :=
    xiFiniteHorizonNativeStepLaw_isTight_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive normalization normalizationPositive horizon initial
  have continuousLimits : ∀ (levels : ℕ → ℕ), StrictMono levels →
      ∀ limit : ProbabilityMeasure (FiniteSupportPathSpace paths),
        Tendsto (fun index => laws (levels index)) atTop (𝓝 limit) →
          ∀ᵐ path ∂(limit : Measure (FiniteSupportPathSpace paths)), Continuous (UniformFun.toFun path.val) := by
    intro levels levelsStrict limit weakConvergence
    apply finiteSupportPath_weakLimit_ae_continuous_of_asymptotic_modulus_toReal paths laws
      ?_ ?_ levels levelsStrict.tendsto_atTop limit weakConvergence
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
  letI : Nonempty (Set.Icc (0 : ℝ) (horizon : ℝ)) := ⟨⟨0, le_rfl, horizon.property⟩⟩
  let denseTimes := TopologicalSpace.denseSeq (Set.Icc (0 : ℝ) (horizon : ℝ))
  have timesDense : DenseRange denseTimes := TopologicalSpace.denseRange_denseSeq _
  have productLimits : ∀ (dimension : ℕ) (indices : Fin dimension → ℕ)
      (tests : Fin dimension → parameters.LimitSpace →ᵇ ℝ), ∃ value : ℝ,
      Tendsto (fun level => ∫ path, ∏ index,
        tests index (UniformFun.toFun path.val (denseTimes (indices index)))
          ∂(laws level : Measure (FiniteSupportPathSpace paths))) atTop (𝓝 value) := by
    intro dimension indices tests
    let observationTimes : Fin dimension → ℝ≥0 :=
      fun index => ⟨(denseTimes (indices index)).val, (denseTimes (indices index)).property.1⟩
    obtain ⟨value, nativeConvergence⟩ := canonicalProducts starts start startsConverge dimension
      observationTimes (fun index => (tests index).toContinuousMap)
    have productContinuous : Continuous (fun path : FiniteSupportPathSpace paths =>
        ∏ index, tests index (UniformFun.toFun path.val (denseTimes (indices index)))) :=
      (FiniteProductWeak.productTest (fun index => (tests index).toContinuousMap)).continuous.comp
        (finiteSupportPathSpace_continuous_finite_evaluations paths dimension
          (fun index => denseTimes (indices index)))
    have integralIdentity (level : ℕ) :
        (∫ path, ∏ index, tests index (UniformFun.toFun path.val (denseTimes (indices index)))
          ∂(laws level : Measure (FiniteSupportPathSpace paths))) =
        ∫ path, ∏ index, tests index (parameters.vertexEmbedding level
          (path (Nat.floor ((observationTimes index : ℝ) * xiNativeFiniteJumpRate system level
            (system.resistanceSpectralRadius rulesConnected distancePositive) normalization))))
            ∂pathLaw (kernels level) (Measure.dirac (starts level)) := by
      change (∫ path, ∏ index, tests index (UniformFun.toFun path.val (denseTimes (indices index)))
        ∂(finiteHorizonStepLaw horizon rates parameters.vertexEmbedding kernels initial level :
          Measure (FiniteSupportPathSpace paths))) = _
      rw [finiteHorizonStepLaw_eq_map]
      rw [integral_map (finiteHorizonStepMap_measurable horizon rates parameters.vertexEmbedding level).aemeasurable
        productContinuous.measurable.aestronglyMeasurable]
      rfl
    refine ⟨value, ?_⟩
    convert nativeConvergence using 1
    funext level
    exact integralIdentity level
  exact finiteSupportPath_full_limit_of_product_observations paths laws tightness continuousLimits
    denseTimes timesDense productLimits

theorem exists_xiFiniteHorizonMovingStartFullConvergence_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
      ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (𝓝 (normalization • resistanceVector)) ∧
      XiNativeSupMovingStartProductProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive ∧
      XiFiniteHorizonMovingStartFullConvergenceProperties system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive normalization normalizationPositive := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, movingProperties, arbitraryProperties⟩ :=
    exists_xiNativeSupArbitraryMovingStartProducts_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, movingProperties, ?_⟩
  exact xiFiniteHorizonMovingStartFullConvergenceProperties_of_arbitraryProducts system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair normalization normalizationPositive arbitraryProperties

end
end EIGS

#print axioms EIGS.xiFiniteHorizonMovingStartFullConvergenceProperties_of_arbitraryProducts
#print axioms EIGS.exists_xiFiniteHorizonMovingStartFullConvergence_of_rules
