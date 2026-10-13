import RequestProject.Section31.EIGSNativeDiscreteEnergy
import RequestProject.Section31.EIGSHarmonicJointDensity
import RequestProject.Section31.EIGSUnitPerronRecovery
import RequestProject.Section31.VaryingCoreRecovery

/-! Full-original-index joint state and actual unit-energy recovery for every
continuous finite-energy function on the actual compact completion. The rows
are the original graph's unit Dirichlet minimizers, and their selection is
constructed. Closedness and the weak Mosco lower bound are separate questions. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

set_option maxHeartbeats 1800000

variable {K : ℕ}

theorem exists_xiNative_joint_recovery (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
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
      ∀ target : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ),
      xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) ≠ ⊤ →
      letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair
      let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass
      ∃ selection : ℕ → ℕ, Tendsto selection atTop atTop ∧
        core.Strong (fun level => xiUnitNativeL2 system rulesConnected mass (selection level)
          (fun vertex => target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair (selection level) vertex)) level)
          (core.embed (BoundedContinuousFunction.mkOfCompact target)) ∧
        Tendsto (fun level => xiNativeScaledUnitEnergy system mass resistanceRate normalization level
          (xiUnitNativeL2 system rulesConnected mass (selection level)
            (fun vertex => target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair (selection level) vertex)) level))
          atTop (nhds ((xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal)) := by
  classical
  obtain ⟨normalization, normalizationPositive, fixedRecovery⟩ :=
    exists_xiUnitPotential_uniform_energy_convergence_for_eigenpair system rulesConnected distancePositive
      oneColourDistance resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  refine ⟨normalization, normalizationPositive, ?_⟩
  intro target targetFinite
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  obtain ⟨approximation, approximationAgreement, _, approximationState, approximationEnergy, _⟩ :=
    exists_xiContinuousHarmonic_joint_recovery system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass distancePositive oneColourDistance resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair target targetFinite
  have rowState : ∀ initialLevel, core.Strong
      (xiUnitNativeL2 system rulesConnected mass initialLevel
        (fun vertex => target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair initialLevel vertex)))
      (core.embed (BoundedContinuousFunction.mkOfCompact (approximation initialLevel))) := by
    intro initialLevel
    apply xiUnitNativeL2_strong_of_uniform system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass initialLevel _ (approximation initialLevel)
    have agreement : approximation initialLevel ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair =
      xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair initialLevel (fun vertex => target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair initialLevel vertex)) :=
      funext (approximationAgreement initialLevel)
    rw [agreement]
    exact (fixedRecovery initialLevel _).1
  have rowEnergy : ∀ initialLevel,
      Tendsto (fun level => xiNativeScaledUnitEnergy system mass resistanceRate normalization level
        (xiUnitNativeL2 system rulesConnected mass initialLevel
          (fun vertex => target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair initialLevel vertex)) level))
        atTop (nhds ((xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
          (approximation initialLevel ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal)) := by
    intro initialLevel
    simp_rw [xiNativeScaledUnitEnergy_unitNativeL2 system rulesConnected]
    rw [xiContinuousHarmonicProjection_energy system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair resistanceRate ratePositive resistanceVector
      vectorPositive renormalizationEigenpair target approximation approximationAgreement initialLevel,
      ENNReal.toReal_ofReal ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive initialLevel).energy_nonneg _)]
    exact (fixedRecovery initialLevel _).2
  obtain ⟨selection, selectionTendsto, jointConvergence⟩ := IGS.Sec31.exists_diagonal_tendsto
    (fun initialLevel =>
      (‖core.embed (BoundedContinuousFunction.mkOfCompact (approximation initialLevel)) -
        core.embed (BoundedContinuousFunction.mkOfCompact target)‖,
      (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (approximation initialLevel ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal))
    (fun initialLevel level =>
      (‖xiUnitNativeL2 system rulesConnected mass initialLevel
          (fun vertex => target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair initialLevel vertex)) level -
        core.restrict level (BoundedContinuousFunction.mkOfCompact target)‖,
      xiNativeScaledUnitEnergy system mass resistanceRate normalization level
        (xiUnitNativeL2 system rulesConnected mass initialLevel
          (fun vertex => target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair initialLevel vertex)) level)))
    (0, (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal)
    (approximationState.prodMk_nhds approximationEnergy)
    (fun initialLevel => (core.strong_norm_sub_tendsto (rowState initialLevel)
      (core.strong_restrict (BoundedContinuousFunction.mkOfCompact target))).prodMk_nhds (rowEnergy initialLevel))
  refine ⟨selection, selectionTendsto, ?_, ?_⟩
  · apply core.strong_of_norm_sub_tendsto_zero _
      (fun level => core.restrict level (BoundedContinuousFunction.mkOfCompact target)) _
      (core.strong_restrict (BoundedContinuousFunction.mkOfCompact target))
    exact (continuous_fst.tendsto _).comp jointConvergence
  · exact (continuous_snd.tendsto _).comp jointConvergence

end EIGS
