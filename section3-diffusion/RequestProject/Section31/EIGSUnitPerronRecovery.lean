import RequestProject.Section31.EIGSResistanceNormalization
import RequestProject.Section31.EIGSUnitEnergyRecovery
import RequestProject.Section31.EIGSUnitUniformConvergence

/-! Original-unit harmonic recovery for any prescribed positive resistance
eigenpair, so independently constructed limit energy domains use the same data. -/

namespace EIGS

open Filter Topology

set_option maxHeartbeats 1800000

variable {K : ℕ}

theorem exists_xiUnitPotential_uniform_energy_convergence_for_eigenpair (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour) :
    ∃ normalization : ℝ, 0 < normalization ∧
      ∀ initialLevel (initialValues : XiVtx system initialLevel → ℝ),
        Tendsto (xiUnitPotentialUniformError system rulesConnected initialLevel initialValues
          (xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
            renormalizationEigenpair initialLevel initialValues)) atTop (nhds 0) ∧
        Tendsto (xiUnitPotentialScaledEnergy system rulesConnected resistanceRate normalization initialLevel initialValues)
          atTop (nhds ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive initialLevel).energy
            initialValues)) := by
  obtain ⟨normalization, normalizationPositive, normalizedConvergence⟩ :=
    exists_normalized_resistance_limit_of_positive_eigenpair system rulesConnected distancePositive resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair
  obtain ⟨profiles, contractionFactor, factorPositive, factorStrict, profilesPlus, profilesMinus,
      profilesMinimal, profilesOscillation⟩ := exists_rule_harmonic_profiles_strict_oscillation system rulesConnected
    distancePositive oneColourDistance resistanceVector vectorPositive
  have stepContraction := xiHarmonicStep_child_edge_contraction system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair profiles profilesPlus profilesMinus profilesMinimal
    contractionFactor profilesOscillation
  refine ⟨normalization, normalizationPositive, ?_⟩
  intro initialLevel initialValues
  have initialEdgeBound : ∀ edge : XiEdge system.toRuleData initialLevel,
      |initialValues (XiTail system initialLevel edge) - initialValues (XiHead system initialLevel edge)| ≤ 2 * ‖initialValues‖ := by
    intro edge
    have firstBound := norm_le_pi_norm initialValues (XiTail system initialLevel edge)
    have secondBound := norm_le_pi_norm initialValues (XiHead system initialLevel edge)
    rw [Real.norm_eq_abs] at firstBound secondBound
    exact (abs_sub _ _).trans (by linarith)
  constructor
  · exact xiUnitPotentialUniformError_tendsto_of_edge_decay system rulesConnected resistanceRate normalization ratePositive
      normalizationPositive resistanceVector vectorPositive renormalizationEigenpair normalizedConvergence initialLevel initialValues
      (xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair initialLevel initialValues)
      (xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair initialLevel initialValues) contractionFactor (2 * ‖initialValues‖) factorPositive.le factorStrict
      (by positivity) (xiHarmonicValues_edge_decay_of_step_contraction system rulesConnected resistanceRate ratePositive
        resistanceVector vectorPositive renormalizationEigenpair contractionFactor factorPositive.le stepContraction initialLevel
        initialValues (2 * ‖initialValues‖) initialEdgeBound)
  · exact xiUnitPotentialScaledEnergy_tendsto system rulesConnected resistanceRate normalization ratePositive normalizationPositive
      resistanceVector vectorPositive normalizedConvergence initialLevel initialValues

end EIGS
