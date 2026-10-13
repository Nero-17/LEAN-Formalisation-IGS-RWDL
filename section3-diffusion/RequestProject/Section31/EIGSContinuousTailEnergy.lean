import RequestProject.Section31.EIGSRuleZeroBoundaryEnergy
import RequestProject.Section31.EIGSDiscreteTraceConvergence
import RequestProject.Section31.EIGSLimitEnergy
import RequestProject.Section31.TraceEnergyPythagoras
import RequestProject.Section31.EIGSMetricCompletion

/-! Actual sampled unit energies are uniformly bounded by the finite extended
weighted energy. No trace-convergence or projection-tail estimate is assumed. -/

namespace EIGS

open IGS.Sec31
open scoped BigOperators

variable {K : ℕ}

theorem xiScaledUnitEnergy_le_extendedWeightedEnergy (system : EIGSData K)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (upper : ℝ) (resistancesBounded : ∀ colour, resistanceVector colour ≤ upper)
    (target : xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive)
    (level : ℕ) :
    xiScaledUnitEnergy system resistanceRate 1 level
        (fun vertex => target.val (xiVertexEmbedding system level vertex)) ≤
      upper * (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive target).toReal := by
  have upperPositive : 0 < upper := (vectorPositive system.initCol).trans_le (resistancesBounded system.initCol)
  have unitBound := (XiNetwork system level).unit_potential_energy_le resistanceVector vectorPositive
    upper resistancesBounded (fun vertex => target.val (xiVertexEmbedding system level vertex))
  have finiteBound := finite_energy_le_traceEnergyValue
    (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive) target level
  have samplingEnergy :
      (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy
          (fun vertex => target.val (xiVertexEmbedding system level vertex)) =
        (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy target := rfl
  calc
    xiScaledUnitEnergy system resistanceRate 1 level
        (fun vertex => target.val (xiVertexEmbedding system level vertex)) ≤
        upper * (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy
          (fun vertex => target.val (xiVertexEmbedding system level vertex)) := by
      rw [xiScaledUnitEnergy, one_mul, xiWeightedFiniteNetwork_energy_eq_potential]
      simpa only [mul_assoc, mul_left_comm] using
        mul_le_mul_of_nonneg_left unitBound (pow_pos ratePositive level).le
    _ = upper * (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy target :=
      congrArg (upper * ·) samplingEnergy
    _ ≤ upper * (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive target).toReal :=
      mul_le_mul_of_nonneg_left finiteBound upperPositive.le

theorem exists_xiScaledUnitEnergy_le_extendedWeightedEnergy (system : EIGSData K)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour) :
    ∃ upper : ℝ, 0 < upper ∧
      ∀ (target : xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive) level,
        xiScaledUnitEnergy system resistanceRate 1 level
            (fun vertex => target.val (xiVertexEmbedding system level vertex)) ≤
          upper * (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive target).toReal := by
  have vectorBound : ∀ colour, resistanceVector colour ≤ ∑ edgeColour, resistanceVector edgeColour :=
    fun colour => Finset.single_le_sum (fun edgeColour _ => (vectorPositive edgeColour).le) (Finset.mem_univ colour)
  refine ⟨∑ colour, resistanceVector colour, (vectorPositive system.initCol).trans_le (vectorBound system.initCol), ?_⟩
  exact fun target level => xiScaledUnitEnergy_le_extendedWeightedEnergy system resistanceRate ratePositive
    resistanceVector vectorPositive _ vectorBound target level

theorem xiCompletion_sampled_unit_energy_le_extendedWeightedEnergy (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRatePositive : 0 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (upper : ℝ) (resistancesBounded : ∀ colour, resistanceVector colour ≤ upper)
    (target : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair → ℝ)
    (targetFinite : xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair) ≠ ⊤)
    (level : ℕ) :
    xiScaledUnitEnergy system resistanceRate 1 level
        (fun vertex => target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair level vertex)) ≤
      upper * (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair)).toReal := by
  let targetDomain : xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive :=
    ⟨target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair,
      (xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive _).2 targetFinite⟩
  exact xiScaledUnitEnergy_le_extendedWeightedEnergy system resistanceRate ratePositive
    resistanceVector vectorPositive upper resistancesBounded targetDomain level

end EIGS

#print axioms EIGS.xiScaledUnitEnergy_le_extendedWeightedEnergy
#print axioms EIGS.exists_xiScaledUnitEnergy_le_extendedWeightedEnergy
#print axioms EIGS.xiCompletion_sampled_unit_energy_le_extendedWeightedEnergy

