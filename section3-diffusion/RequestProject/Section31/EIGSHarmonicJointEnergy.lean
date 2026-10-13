import RequestProject.Section31.EIGSHarmonicL2Density
import RequestProject.Section31.EIGSEnergyRecovery

/-! Exact energy and residual-energy convergence of the actual continuous
harmonic projections, for a continuous target with finite extended energy. -/

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

include renormalizationEigenpair approximationAgreement

theorem xiContinuousHarmonicProjection_energy (level : ℕ) :
    xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (approximation level ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair) =
      ENNReal.ofReal ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy
        (fun vertex => target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair level vertex))) := by
  apply xiContinuousHarmonic_extended_energy system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair level _ (approximation level)
  intro offset vertex
  exact (approximationAgreement level (xiVertexEmbedding system (level + offset) vertex)).trans
    (xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair level _ offset vertex)

theorem xiContinuousHarmonicProjection_boundary (level : ℕ) (vertex : XiVtx system level) :
    approximation level (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair level vertex) =
      target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair level vertex) := by
  exact (approximationAgreement level (xiVertexEmbedding system level vertex)).trans
    (xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair level _ 0 vertex)

theorem xiContinuousHarmonicProjection_energy_tendsto
    (targetFinite : xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair) ≠ ⊤) :
    Tendsto (fun level => (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (approximation level ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair)).toReal)
      atTop (nhds ((xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair)).toReal)) := by
  let targetDomain : xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive :=
    ⟨target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair,
      (xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive _).2 targetFinite⟩
  have finiteEnergyLimit := finite_energy_tendsto_traceEnergyValue
    (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive)
    (xiUnionWeightedNetwork_energy_increasing_of_eigenpair system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair)
    targetDomain
  convert finiteEnergyLimit using 1
  ext level
  rw [xiContinuousHarmonicProjection_energy system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair target approximation approximationAgreement level]
  exact ENNReal.toReal_ofReal ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy_nonneg _)

theorem xiContinuousHarmonicProjection_residual_energy_tendsto
    (targetFinite : xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair) ≠ ⊤) :
    Tendsto (fun level => (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (fun vertex => target (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair vertex) -
        approximation level (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair vertex))).toReal)
      atTop (nhds 0) := by
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
  have residualLimit := (tendsto_const_nhds (x := (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair)).toReal)).sub
    (xiContinuousHarmonicProjection_energy_tendsto system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair target approximation approximationAgreement targetFinite)
  rw [sub_self] at residualLimit
  apply residualLimit.congr
  intro level
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
  linarith

end MetricEigenpair

end EIGS

