import RequestProject.Section31.EIGSFullHorizonModulusBound
import RequestProject.Section31.NativeModulusWindowChoice

/-! The actual floor-clock paths have a uniformly small modulus bad-event
probability at every sufficiently fine level, uniformly over their initial
laws. This is a probability estimate, not yet path-space tightness. -/

namespace EIGS

open MeasureTheory ProbabilityTheory Filter
open IGS.Sec31 IGS.Sec31.DiscreteMarkov
open scoped Classical
noncomputable section
set_option maxHeartbeats 4000000
variable {K : ℕ}

def xiActualPathModulusEvent (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (parameters : XiPathMetricData system rulesConnected) (normalization : ℝ)
    (level : ℕ) (horizon window tolerance : ℝ) : Set (ℕ → XiVtx system level) :=
  {path | ∃ first ∈ Set.Icc (0 : ℝ) horizon, ∃ second ∈ Set.Icc (0 : ℝ) horizon,
    |second - first| ≤ window ∧ tolerance <
      dist (parameters.vertexEmbedding level (path ⌊first * xiNativeFiniteJumpRate system level
        (system.resistanceSpectralRadius rulesConnected distancePositive) normalization⌋₊))
        (parameters.vertexEmbedding level (path ⌊second * xiNativeFiniteJumpRate system level
          (system.resistanceSpectralRadius rulesConnected distancePositive) normalization⌋₊))}

theorem exists_xiAsymptoticPathModulus_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    [∀ level, MeasurableSpace (XiVtx system level)]
    [∀ level, MeasurableSingletonClass (XiVtx system level)]
    (horizon tolerance probabilityTolerance maximumWindow : ℝ)
    (horizonNonnegative : 0 ≤ horizon) (tolerancePositive : 0 < tolerance)
    (probabilityPositive : 0 < probabilityTolerance) (maximumWindowPositive : 0 < maximumWindow) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    ∃ (coarse : ℕ) (window : ℝ), 0 < window ∧ window < maximumWindow ∧
      ∀ (steps : ℕ) (initial : ProbabilityMeasure (XiVtx system (coarse + steps))),
        let transition := finiteGraphTransitionKernel (XiSimpleGraph system (coarse + steps))
          (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex))
        ((pathLaw transition (initial : Measure _))
          (xiActualPathModulusEvent system rulesConnected distancePositive parameters normalization
            (coarse + steps) horizon window tolerance)).toReal < probabilityTolerance := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  dsimp only
  obtain ⟨fraction, probability, factor, fractionPositive, probabilityPositive', factorPositive,
      contractionNonnegative, contractionLessOne, fullBound⟩ :=
    exists_xiFullHorizonModulusBound_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive normalization normalizationPositive
  have spatialPositive : 0 < 3 * xiRuleRadius system parameters.lengths + 1 := by
    have radiusNonnegative := xiRuleRadius_nonnegative system
      (fun colour => (parameters.lengthsPositive colour).le)
    positivity
  obtain ⟨coarse, count, window, windowPositive, windowSmall, spatialBound, probabilityBound⟩ :=
    exists_nativeModulusWindowChoice
      (spatialConstant := 3 * xiRuleRadius system parameters.lengths + 1)
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
      (system.distanceSpectralRadius_sq_le_mass_mul_resistance rulesConnected rulesLoopless rulesUnique distancePositive)
      contractionNonnegative contractionLessOne horizonNonnegative fractionPositive factorPositive.le
      spatialPositive tolerancePositive probabilityPositive maximumWindowPositive
  refine ⟨coarse, window, windowPositive, windowSmall, ?_⟩
  intro steps initial
  let transition := finiteGraphTransitionKernel (XiSimpleGraph system (coarse + steps))
    (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex))
  have eventInclusion :
      xiActualPathModulusEvent system rulesConnected distancePositive parameters normalization
        (coarse + steps) horizon window tolerance ⊆
      xiFullHorizonModulusEvent system rulesConnected distancePositive parameters normalization
        coarse steps count horizon window := by
    intro path witness
    obtain ⟨first, firstBounds, second, secondBounds, close, far⟩ := witness
    exact ⟨first, firstBounds, second, secondBounds, close, spatialBound.trans far⟩
  have eventBound := ENNReal.toReal_mono (measure_ne_top (pathLaw transition (initial : Measure _)) _)
    (measure_mono eventInclusion)
  exact (eventBound.trans (fullBound coarse steps count initial horizon window windowPositive)).trans_lt probabilityBound

end
end EIGS

#print axioms EIGS.exists_xiAsymptoticPathModulus_of_rules
