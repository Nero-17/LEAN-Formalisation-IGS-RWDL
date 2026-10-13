import RequestProject.Section31.EIGSNativeProjectionTail
import RequestProject.Section31.EIGSAnalyticTimeScale

/-! The actual native projection tail under the original rule hypotheses.
The strict mass--resistance scale inequality is proved, not assumed. -/

namespace EIGS

variable {K : ℕ}

theorem exists_xiUnitProjection_native_tail_for_eigenpair (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ coarseLevel fineLevel
      (levelsOrdered : coarseLevel ≤ fineLevel) (values : XiVtx system fineLevel → ℝ),
      ‖xiFiniteSpeedL2 system mass fineLevel values -
        xiFiniteSpeedL2 system mass fineLevel
          (xiUnitEnergyProjection system rulesConnected coarseLevel fineLevel levelsOrdered values)‖ ≤
      constant * (Real.sqrt (mass.rate * resistanceRate))⁻¹ ^ coarseLevel *
        Real.sqrt (xiScaledUnitEnergy system resistanceRate normalization fineLevel values) := by
  have scaleGreaterOne := xiAnalyticTimeRate_gt_one system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive mass resistanceRate ratePositive resistanceVector vectorPositive
    (funext renormalizationEigenpair)
  exact exists_xiUnitProjection_native_tail system rulesConnected distancePositive mass resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair scaleGreaterOne normalization normalizationPositive

theorem exists_xiUnitProjection_native_tail_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      0 < resistanceRate ∧ (∀ colour, 0 < resistanceVector colour) ∧
      (∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour) ∧
      ∀ normalization : ℝ, 0 < normalization → ∃ constant : ℝ, 0 < constant ∧
      ∀ coarseLevel fineLevel (levelsOrdered : coarseLevel ≤ fineLevel) (values : XiVtx system fineLevel → ℝ),
      ‖xiFiniteSpeedL2 system mass fineLevel values -
        xiFiniteSpeedL2 system mass fineLevel
          (xiUnitEnergyProjection system rulesConnected coarseLevel fineLevel levelsOrdered values)‖ ≤
      constant * (Real.sqrt (mass.rate * resistanceRate))⁻¹ ^ coarseLevel *
        Real.sqrt (xiScaledUnitEnergy system resistanceRate normalization fineLevel values) := by
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  have coloursPositive : 0 < K := lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt
  obtain ⟨resistanceVector, resistanceRate, vectorPositive, ratePositive, _, eigenpair⟩ :=
    (system.connectedRuleSystem rulesConnected).distance_positive_eigenpair coloursPositive distancePositive
  have coordinateEigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour := fun colour => congrFun eigenpair colour
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, coordinateEigenpair, ?_⟩
  intro normalization normalizationPositive
  exact exists_xiUnitProjection_native_tail_for_eigenpair system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive mass resistanceRate ratePositive resistanceVector vectorPositive coordinateEigenpair
    normalization normalizationPositive

end EIGS
