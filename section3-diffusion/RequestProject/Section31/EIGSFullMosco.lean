import RequestProject.Section31.EIGSFullMoscoLower
import RequestProject.Section31.EIGSFullMoscoRecovery

/-! Full Mosco convergence for the actual original-unit graph energies and
actual varying speed L2 spaces. Every metric, mass, resistance and normalization
parameter, including the common normalized Psi limit, is constructed from the
original finite rules. The target is the genuine extended closed energy. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped ENNReal

set_option maxHeartbeats 3000000

variable {K : ℕ}

theorem exists_xiFullMosco_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
    let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    let oneColourDistance : K = 1 → ∀ colour,
        2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
      intro _ colour
      exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
        (system.plant_ne colour) (plantingNonadjacent colour)
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ ratePositive : 0 < resistanceRate, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, 0 < normalization ∧
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (nhds (normalization • resistanceVector)) ∧
      let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive
      let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
        intro sequence energyCauchy ambientZero
        exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
          mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
          (by simpa using ambientZero.norm)
      (∀ (sequence : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
        (target : Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass)),
        core.Weak sequence target →
        QuadraticEnergySpace.closedExtendedEnergy originalDomain originalForm nonnegative closable target ≤
          Filter.liminf (fun level => ENNReal.ofReal
            (xiNativeScaledUnitEnergy system mass resistanceRate normalization level (sequence level))) atTop) ∧
      (∀ target : Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass),
        ∃ sequence : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level),
          core.Strong sequence target ∧
          Filter.limsup (fun level => ENNReal.ofReal
            (xiNativeScaledUnitEnergy system mass resistanceRate normalization level (sequence level))) atTop ≤
              QuadraticEnergySpace.closedExtendedEnergy originalDomain originalForm nonnegative closable target) := by
  classical
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  have coloursPositive : 0 < K := lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt
  obtain ⟨resistanceVector, resistanceRate, vectorPositive, ratePositive, _, eigenpair⟩ :=
    (system.connectedRuleSystem rulesConnected).distance_positive_eigenpair coloursPositive distancePositive
  have renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour :=
    fun colour => congrFun eigenpair colour
  obtain ⟨normalization, normalizationPositive, normalizedConvergence⟩ :=
    exists_normalized_resistance_limit_of_positive_eigenpair system rulesConnected distancePositive resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_, ?_⟩
  · exact xiClosedExtendedEnergy_mosco_lower system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive normalizedConvergence
  · exact xiClosedExtendedEnergy_mosco_recovery system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive normalizedConvergence

end EIGS

#print axioms EIGS.exists_xiFullMosco_of_rules
