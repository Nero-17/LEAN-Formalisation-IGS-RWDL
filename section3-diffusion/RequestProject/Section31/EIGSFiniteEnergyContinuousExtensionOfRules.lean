import RequestProject.Section31.EIGSFiniteEnergyContinuousExtension

/-! The resistance-rate-greater-than-one case of the actual energy domain:
every bounded-trace-energy vertex function extends continuously to the same
path-metric completion and retains its exact vertex values and energy.
The eigenpair, harmonic contraction and metric data are supplied internally
from the original rules. No resistance form or continuity of the vertex
function is assumed. Candidate source: compilation is not claimed. -/

namespace EIGS
open IGS.Sec31 Filter Topology
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem exists_xiFiniteEnergy_continuous_extension_of_rules
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (canonicalRateGreaterThanOne : 1 < system.resistanceSpectralRadius rulesConnected distancePositive) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    ∃ resistanceRate : ℝ, ∃ rateGreaterThanOne : 1 < resistanceRate,
    ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
    ∃ eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour,
    ∀ values : XiVertexUnion system → ℝ,
      values ∈ xiWeightedEnergyDomain system resistanceRate (zero_lt_one.trans rateGreaterThanOne)
        resistanceVector vectorPositive →
      ∃ extension : C(parameters.LimitSpace, ℝ),
        (∀ vertex, extension (xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected)
          (zero_lt_one.trans ((by norm_num : (1 : ℝ) < 2).trans_le
            (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)))
          parameters.eigenpair vertex) = values vertex) ∧
        xiExtendedWeightedEnergy system resistanceRate (zero_lt_one.trans rateGreaterThanOne)
          resistanceVector vectorPositive
          (extension ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius rulesConnected)
            (zero_lt_one.trans ((by norm_num : (1 : ℝ) < 2).trans_le
              (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)))
            parameters.eigenpair) =
          xiExtendedWeightedEnergy system resistanceRate (zero_lt_one.trans rateGreaterThanOne)
            resistanceVector vectorPositive values := by
  intro parameters
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj (system.plant_ne colour) (plantingNonadjacent colour)
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, eigenpair,
      contractionFactor, factorPositive, factorStrict, stepContraction⟩ :=
    exists_xiHarmonic_strict_contraction system rulesConnected distancePositive oneColourDistance
  have rateEquality := system.resistanceSpectralRadius_eq_of_positive_eigenpair rulesConnected distancePositive
    ratePositive vectorPositive (funext eigenpair)
  have rateGreaterThanOne : 1 < resistanceRate := by
    rw [rateEquality]
    exact canonicalRateGreaterThanOne
  refine ⟨resistanceRate, rateGreaterThanOne, resistanceVector, vectorPositive, eigenpair, ?_⟩
  intro values finiteEnergy
  exact exists_xiFiniteEnergy_continuous_extension_of_step_contraction system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair resistanceRate rateGreaterThanOne resistanceVector vectorPositive
    eigenpair contractionFactor factorPositive factorStrict stepContraction values finiteEnergy

end
end EIGS

#print axioms EIGS.exists_xiFiniteEnergy_continuous_extension_of_rules
