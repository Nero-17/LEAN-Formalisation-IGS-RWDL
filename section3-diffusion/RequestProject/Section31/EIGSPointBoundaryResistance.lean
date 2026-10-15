import RequestProject.Section31.EIGSPointCellEnergy
import RequestProject.Section31.EIGSCompletedResistanceVariational

/-! The actual completed resistance from any point in a physical closed cell
to either original cell terminal is at most a common constant times the
resistance scale. The extension is arbitrary with the established skeleton
agreement, so this estimate preserves a previously selected realization. -/

namespace EIGS
open IGS.Sec31
noncomputable section
variable {K : ℕ}
variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (resistanceRate : ℝ) (rateGreaterThanOne : 1 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (anchor : XiVertexUnion system)

local instance : CompactSpace (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) :=
  xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair

variable (extension : XiAnchoredEnergyHilbert system rulesConnected resistanceRate
    (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive eigenpair anchor →L[ℝ]
      C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ))
    (agreement : ∀ values vertex, extension values (xiCompletionUnionEmbedding system rulesConnected
      lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) =
        values.value.val vertex)

include agreement in
theorem exists_xiPhysicalClosedCell_point_boundary_resistance_bound
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour)) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ level (edge : XiEdge system.toRuleData level) point,
        point ∈ xiPhysicalClosedCell system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair level edge →
      ∀ terminal : XiVtx system level,
        (terminal = XiTail system level edge ∨ terminal = XiHead system level edge) →
        xiCompletedResistance system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
          metricEigenpair resistanceRate (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive
          eigenpair anchor extension point (xiCompletionEmbedding system rulesConnected lengths lengthsPositive
            distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level terminal) ≤
          constant / resistanceRate ^ level := by
  obtain ⟨constant, constantPositive, energyBound⟩ :=
    exists_xiPhysicalClosedCell_point_terminal_energy_bound system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate rateGreaterThanOne resistanceVector vectorPositive
      eigenpair distancePositive oneColourDistance
  refine ⟨constant, constantPositive, ?_⟩
  intro level edge point membership terminal terminalMembership
  obtain ⟨function, valueIdentity, energyIdentity⟩ := exists_xiCompletedResistance_attaining_function system
    rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair resistanceRate
    (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive eigenpair anchor extension agreement point
    (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level terminal)
  have squaredBound := energyBound function level edge point membership terminal terminalMembership
  rw [valueIdentity] at squaredBound
  rw [xiContinuousResistanceQuadraticForm_value] at energyIdentity
  rw [energyIdentity] at squaredBound
  have resistanceNonnegative : 0 ≤
      xiCompletedResistance system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair resistanceRate (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive
        eigenpair anchor extension point (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level terminal) := sq_nonneg _
  nlinarith [div_pos constantPositive (pow_pos (zero_lt_one.trans rateGreaterThanOne) level)]

end
end EIGS

#print axioms EIGS.exists_xiPhysicalClosedCell_point_boundary_resistance_bound
