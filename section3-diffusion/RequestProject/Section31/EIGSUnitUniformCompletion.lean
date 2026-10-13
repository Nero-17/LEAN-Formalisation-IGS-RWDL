import RequestProject.Section31.EIGSUnitUniformConvergence
import RequestProject.Section31.EIGSHarmonicContinuity

/-! The original-unit uniform harmonic limit is continuous on the constructed
compact completion, with metric and resistance parameters obtained from rules. -/

namespace EIGS

open Filter Topology

set_option maxHeartbeats 1800000

variable {K : ℕ}

theorem exists_xiUnitPotential_continuous_uniform_limit_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ ratePositive : 0 < resistanceRate,
      ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∀ initialLevel (initialValues : XiVtx system initialLevel → ℝ),
        ∃ extension : C(parameters.LimitSpace, ℝ),
          (∀ vertex : XiVertexUnion system,
            extension (xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
              (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair vertex) =
              xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
                renormalizationEigenpair initialLevel initialValues vertex) ∧
          Tendsto (xiUnitPotentialUniformError system rulesConnected initialLevel initialValues
            (extension ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
              (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair)) atTop (nhds 0) := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro oneColour colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj (system.plant_ne colour) (plantingNonadjacent colour)
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair, uniformConvergence⟩ :=
    exists_xiUnitPotential_uniform_harmonic_convergence system rulesConnected distancePositive oneColourDistance
  obtain ⟨profiles, contractionFactor, factorPositive, factorStrict, profilesPlus, profilesMinus,
      profilesMinimal, profilesOscillation⟩ := exists_rule_harmonic_profiles_strict_oscillation system rulesConnected
    distancePositive oneColourDistance resistanceVector vectorPositive
  have stepContraction := xiHarmonicStep_child_edge_contraction system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair profiles profilesPlus profilesMinus profilesMinimal
    contractionFactor profilesOscillation
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair, ?_⟩
  intro initialLevel initialValues
  have initialEdgeBound : ∀ edge : XiEdge system.toRuleData initialLevel,
      |initialValues (XiTail system initialLevel edge) - initialValues (XiHead system initialLevel edge)| ≤ 2 * ‖initialValues‖ := by
    intro edge
    have firstBound := norm_le_pi_norm initialValues (XiTail system initialLevel edge)
    have secondBound := norm_le_pi_norm initialValues (XiHead system initialLevel edge)
    rw [Real.norm_eq_abs] at firstBound secondBound
    exact (abs_sub _ _).trans (by linarith)
  have edgeDecay := xiHarmonicValues_edge_decay_of_step_contraction system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair contractionFactor factorPositive.le stepContraction
    initialLevel initialValues (2 * ‖initialValues‖) initialEdgeBound
  obtain ⟨extension, extensionValues⟩ := exists_xiHarmonic_completion_extension_of_edge_decay system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne
    parameters.eigenpair resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair initialLevel
    initialValues contractionFactor (2 * ‖initialValues‖) factorPositive factorStrict (by positivity) edgeDecay
  refine ⟨extension, extensionValues, ?_⟩
  have unionAgreement : extension ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair =
      xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair initialLevel initialValues := funext extensionValues
  change Tendsto (xiUnitPotentialUniformError system rulesConnected initialLevel initialValues
    (extension ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair)) atTop (nhds 0)
  rw [unionAgreement]
  exact uniformConvergence initialLevel initialValues

end EIGS
