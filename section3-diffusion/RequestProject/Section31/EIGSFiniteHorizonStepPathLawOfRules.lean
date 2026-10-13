import RequestProject.Section31.FiniteHorizonMarkovStepPathLaw
import RequestProject.Section31.EIGSDiscreteFiniteObservations
import RequestProject.Section31.EIGSResistanceNormalization
import RequestProject.Section31.EIGSAddressMeasure

/-! Actual finite-horizon Xi walk laws in the uniform finite-support carrier.
The native clock is positive by the actual mass growth theorem. Metric
compactness and the resistance normalization are constructed from the rules.
This is a path-law construction and joint-distribution identity, not tightness. -/

namespace EIGS

open MeasureTheory ProbabilityTheory Filter Topology
open IGS.Sec31.DiscreteMarkov
open scoped BigOperators Classical NNReal UniformConvergence
noncomputable section
set_option maxHeartbeats 3000000

variable {K : ℕ}

def xiNativeFiniteJumpRateNNReal (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization) (level : ℕ) : ℝ≥0 :=
  ⟨xiNativeFiniteJumpRate system level
      (system.resistanceSpectralRadius rulesConnected distancePositive) normalization,
    (xiNativeFiniteJumpRate_positive system (xiMassParametersOfRules system rulesConnected distancePositive)
      level _ normalization
      (system.resistanceSpectralRadius_positive_eigenpair rulesConnected distancePositive).1
      normalizationPositive).le⟩

theorem xiNativeFiniteJumpRateNNReal_positive (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization) (level : ℕ) :
    0 < xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive
      normalization normalizationPositive level := by
  exact xiNativeFiniteJumpRate_positive system
    (xiMassParametersOfRules system rulesConnected distancePositive) level _ normalization
    (system.resistanceSpectralRadius_positive_eigenpair rulesConnected distancePositive).1
    normalizationPositive

def XiFiniteHorizonNativeStepLawProperties (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (horizon : ℝ≥0) (initial : (level : ℕ) → ProbabilityMeasure (XiVtx system level)) : Prop :=
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  letI : MeasurableSpace parameters.LimitSpace := borel _
  letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  let rates := xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive normalization normalizationPositive
  let paths := finiteHorizonStepPaths horizon rates parameters.vertexEmbedding
  ∃ laws : (level : ℕ) → ProbabilityMeasure (FiniteSupportPathSpace paths),
    (∀ level, (laws level : Measure (FiniteSupportPathSpace paths)) =
      (pathLaw (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
        (initial level)).map (finiteHorizonStepMap horizon rates parameters.vertexEmbedding level)) ∧
    (∀ level dimension (times : Fin dimension → Set.Icc (0 : ℝ) (horizon : ℝ)),
      (laws level : Measure (FiniteSupportPathSpace paths)).map
        (fun path : FiniteSupportPathSpace paths =>
          fun index => UniformFun.toFun path.val (times index)) =
      (pathLaw (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
        (initial level)).map (fun path : ℕ → XiVtx system level => fun index =>
          parameters.vertexEmbedding level
            (path ⌊(times index).val * xiNativeFiniteJumpRate system level
              (system.resistanceSpectralRadius rulesConnected distancePositive) normalization⌋₊))) ∧
    (∀ level (time : Set.Icc (0 : ℝ) (horizon : ℝ)),
      (laws level : Measure (FiniteSupportPathSpace paths)).map
        (fun path : FiniteSupportPathSpace paths => UniformFun.toFun path.val time) =
      ((xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level ^
          ⌊time.val * xiNativeFiniteJumpRate system level
            (system.resistanceSpectralRadius rulesConnected distancePositive) normalization⌋₊) ∘ₘ
        (initial level : Measure (XiVtx system level))).map (parameters.vertexEmbedding level))

theorem xiFiniteHorizonNativeStepLawProperties_construct (system : EIGSData K)
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
    XiFiniteHorizonNativeStepLawProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive normalization normalizationPositive horizon initial := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  letI : MeasurableSpace parameters.LimitSpace := borel _
  letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  let rates := xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive normalization normalizationPositive
  let kernels := fun level =>
    xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level
  dsimp only [XiFiniteHorizonNativeStepLawProperties]
  refine ⟨(fun level => finiteHorizonStepLaw horizon rates parameters.vertexEmbedding kernels initial level),
    ?_, ?_, ?_⟩
  · intro level
    exact finiteHorizonStepLaw_eq_map horizon rates parameters.vertexEmbedding kernels initial level
  · intro level dimension times
    simpa only [rates, xiNativeFiniteJumpRateNNReal] using
      finiteHorizonStepLaw_finite_evaluations horizon rates parameters.vertexEmbedding kernels initial
        level dimension times
  · intro level time
    simpa only [rates, xiNativeFiniteJumpRateNNReal] using
      finiteHorizonStepLaw_coordinate horizon rates parameters.vertexEmbedding kernels initial level time

theorem exists_xiFiniteHorizonNativeStepLaw_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      ∀ (horizon : ℝ≥0) (initial : (level : ℕ) → ProbabilityMeasure (XiVtx system level)),
      XiFiniteHorizonNativeStepLawProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive normalization normalizationPositive horizon initial := by
  obtain ⟨ratePositive, vector, vectorPositive, eigenpair⟩ :=
    system.resistanceSpectralRadius_positive_eigenpair rulesConnected distancePositive
  obtain ⟨normalization, normalizationPositive, normalizedConvergence⟩ :=
    exists_normalized_resistance_limit_of_positive_eigenpair system rulesConnected distancePositive
      (system.resistanceSpectralRadius rulesConnected distancePositive) ratePositive vector vectorPositive
      (fun colour => congrFun eigenpair colour)
  refine ⟨normalization, normalizationPositive, ?_⟩
  intro horizon initial
  exact xiFiniteHorizonNativeStepLawProperties_construct system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive normalization normalizationPositive horizon initial

end

end EIGS

#print axioms EIGS.xiNativeFiniteJumpRateNNReal_positive
#print axioms EIGS.xiFiniteHorizonNativeStepLawProperties_construct
#print axioms EIGS.exists_xiFiniteHorizonNativeStepLaw_of_rules
