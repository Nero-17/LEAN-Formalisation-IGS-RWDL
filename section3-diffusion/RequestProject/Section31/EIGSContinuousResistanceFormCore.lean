import RequestProject.Section31.EIGSEnergyConstantsQuotient
import RequestProject.Section31.EIGSClosedRegularity
import RequestProject.Section31.EIGSL2EnergyConstants
import RequestProject.Section31.UniformDenseFiniteInterpolation

/-! The actual continuous energy form: its null space consists exactly of
constants, every finite subset admits arbitrary finite-energy interpolation,
and all real normal contractions decrease energy. No resistance-form axiom
is an input to these statements. Candidate source: compilation is not claimed. -/

namespace EIGS
open IGS.Sec31
noncomputable section
variable {K : ℕ}
variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)

local instance : CompactSpace (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) :=
  xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair

def xiContinuousResistanceQuadraticForm : QuadraticForm ℝ
    (xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive) :=
  (limitTraceQuadraticForm
    (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive)
    (xiUnionWeightedNetwork_energy_increasing_of_eigenpair system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair)).comp
    (xiContinuousEnergyToUnionDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive)

theorem xiContinuousResistanceQuadraticForm_value
    (function : xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive) :
    xiContinuousResistanceQuadraticForm system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair function =
    (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (function.val ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal := rfl

theorem xiContinuousResistanceQuadraticForm_nonnegative
    (function : xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive) :
    0 ≤ xiContinuousResistanceQuadraticForm system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair function :=
  ENNReal.toReal_nonneg

theorem xiContinuousResistanceQuadraticForm_zero_iff_constant
    (function : xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive)
    (anchor : XiVertexUnion system) :
    xiContinuousResistanceQuadraticForm system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair function = 0 ↔
    ∀ point, function.val point = function.val (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive
      distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair anchor) := by
  rw [xiContinuousResistanceQuadraticForm_value]
  have skeleton := xiWeightedEnergy_zero_iff_constant system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive anchor
    (xiContinuousEnergyToUnionDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive function)
  constructor
  · intro zeroEnergy point
    have constant := skeleton.mp zeroEnergy
    refine (xiCompletionUnionEmbedding_denseRange system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair).induction_on point
      (isClosed_eq function.val.continuous continuous_const) ?_
    exact constant
  · intro constant
    exact skeleton.mpr (fun vertex => constant _)

theorem xiContinuousResistanceQuadraticForm_normal_contraction
    (contraction : ℝ → ℝ)
    (contractionBound : ∀ first second, |contraction first - contraction second| ≤ |first - second|)
    (function : xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive) :
    ∃ contracted : xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive,
      (∀ point, contracted.val point = contraction (function.val point)) ∧
      xiContinuousResistanceQuadraticForm system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair contracted ≤
      xiContinuousResistanceQuadraticForm system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair function := by
  have contractionContinuous : Continuous contraction :=
    (LipschitzWith.mk_one (fun first second => by simpa only [Real.dist_eq] using contractionBound first second)).continuous
  let contractedContinuous := ContinuousMap.comp ⟨contraction, contractionContinuous⟩ function.val
  have finiteEnergy : contractedContinuous ∈ xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive :=
    traceEnergyDomain_comp _ contraction contractionBound function.property
  refine ⟨⟨contractedContinuous, finiteEnergy⟩, fun _ => rfl, ?_⟩
  rw [xiContinuousResistanceQuadraticForm_value, xiContinuousResistanceQuadraticForm_value]
  apply ENNReal.toReal_mono
    ((xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive _).mp function.property)
  exact extendedTraceEnergy_comp_le _ contraction contractionBound _

include eigenpair in
theorem xiContinuousFiniteEnergy_finite_interpolation
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (mass : XiMassParameters system)
    (points : Finset (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)) :
    Function.Surjective (fun function : xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive =>
        fun vertex : points => function.val vertex.val) := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  apply uniformDenseSubmodule_finite_evaluation_surjective
  exact (xiClosedLpEnergy_regular_core system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
    oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate
    ratePositive resistanceVector vectorPositive eigenpair).1

end
end EIGS

#print axioms EIGS.xiContinuousResistanceQuadraticForm_zero_iff_constant
#print axioms EIGS.xiContinuousResistanceQuadraticForm_normal_contraction
#print axioms EIGS.xiContinuousFiniteEnergy_finite_interpolation
