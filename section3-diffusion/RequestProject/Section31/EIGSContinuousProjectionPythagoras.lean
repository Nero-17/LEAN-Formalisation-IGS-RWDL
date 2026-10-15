import RequestProject.Section31.EIGSHarmonicJointEnergy

/-! Exact energy Pythagoras for the actual continuous harmonic projection.
The approximation premise identifies the actual prescribed-boundary harmonic
function, and is not an orthogonality or energy-identity hypothesis.
This new public endpoint extracts the identity already used inside the proved
residual-energy convergence theorem. Candidate until whole-file acceptance. -/

namespace EIGS

open IGS.Sec31 Filter Topology

set_option maxHeartbeats 1800000

variable {K : ℕ}

section MetricEigenpair

variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRatePositive : 0 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (target : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair, ℝ))
    (approximation : ℕ → C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair, ℝ))
    (approximationAgreement : ∀ level (vertex : XiVertexUnion system),
      approximation level (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair vertex) =
        xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair level
          (fun finiteVertex => target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair level finiteVertex)) vertex)

include renormalizationEigenpair approximationAgreement in
theorem xiContinuousHarmonicProjection_energy_pythagoras
    (targetFinite : xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair) ≠ ⊤)
    (level : ℕ) :
    (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair)).toReal =
    (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (approximation level ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair)).toReal +
    (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (fun vertex => target (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair vertex) -
        approximation level (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair vertex))).toReal := by
  let targetDomain : xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive :=
    ⟨target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair,
      (xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive _).2 targetFinite⟩
  have approximationFinite : ∀ level, (approximation level ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair) ∈
      xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive := by
    intro level
    apply (xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive _).2
    rw [xiContinuousHarmonicProjection_energy system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair target approximation approximationAgreement level]
    exact ENNReal.ofReal_ne_top
  let approximationDomain : ℕ → xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive := fun level =>
    ⟨approximation level ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair, approximationFinite level⟩
  have approximationCore : ∀ level, approximationDomain level ∈ xiHarmonicCoreAt system resistanceRate ratePositive resistanceVector vectorPositive level := by
    intro level
    change xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (approximation level ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair) = _
    rw [xiContinuousHarmonicProjection_energy system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair target approximation approximationAgreement level]
    congr 1
    apply congrArg (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy
    funext vertex
    exact (xiContinuousHarmonicProjection_boundary system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair target approximation approximationAgreement level vertex).symm
  have pythagoras := xiHarmonicCoreAt_energy_pythagoras system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    level (approximationDomain level) targetDomain (approximationCore level)
    (fun vertex => (xiContinuousHarmonicProjection_boundary system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair target approximation approximationAgreement level vertex).symm)
  change (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair)).toReal =
    (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (approximation level ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair)).toReal +
    (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (fun vertex => target (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair vertex) -
        approximation level (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair vertex))).toReal at pythagoras
  exact pythagoras

end MetricEigenpair
end EIGS

#print axioms EIGS.xiContinuousHarmonicProjection_energy_pythagoras
