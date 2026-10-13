import RequestProject.Section31.EIGSFiniteHorizonStepPathLawOfRules
import RequestProject.Section31.EIGSAsymptoticPathModulus
import RequestProject.Section31.FiniteHorizonModulusLaw
import RequestProject.Section31.FiniteHorizonSupportLaw
import RequestProject.Section31.FiniteSupportPathTightness

/-! Tightness of the actual finite-horizon floor-clock Xi walk laws.
The hypotheses are the original rule conditions and positivity of the clock
normalization. The finite-level support and probability modulus inputs are
proved from the actual laws and rules, rather than imposed on the laws. -/

namespace EIGS

open MeasureTheory ProbabilityTheory Filter Topology
open IGS.Sec31.DiscreteMarkov
open scoped Classical NNReal UniformConvergence
noncomputable section
set_option maxHeartbeats 4000000

variable {K : ℕ}

theorem xiFiniteHorizonNativeStepLaw_isTight_of_rules (system : EIGSData K)
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
    IsTightMeasureSet (Set.range (fun level =>
      (finiteHorizonStepLaw horizon rates parameters.vertexEmbedding kernels initial level : Measure (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates parameters.vertexEmbedding))))) := by
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
  dsimp only
  apply finiteSupportPath_isTightMeasureSet_of_asymptotic_modulus_toReal
    (finiteHorizonStepPaths horizon rates parameters.vertexEmbedding)
    (fun level => finiteHorizonStepLaw horizon rates parameters.vertexEmbedding kernels initial level)
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
    rw [finiteHorizonStepLaw_modulus_compl]
    have nativeBound := modulusBound steps (initial (coarse + steps))
    simpa only [rates, kernels, parameters, xiNativeFiniteJumpRateNNReal,
      xiNativeDiscreteKernel, xiActualPathModulusEvent] using nativeBound.le

end
end EIGS

#print axioms EIGS.xiFiniteHorizonNativeStepLaw_isTight_of_rules
