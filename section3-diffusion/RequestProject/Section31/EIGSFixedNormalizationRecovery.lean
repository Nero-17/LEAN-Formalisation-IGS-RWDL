import RequestProject.Section31.EIGSUnitPerronRecovery
import RequestProject.Section31.EIGSNativeJointRecovery
import RequestProject.Section31.EIGSClosedRecoveryWithoutPrimitive

/-! Recovery at one prescribed positive normalization with the actual
normalized resistance-iterate limit. The final existence wrapper obtains that
limit from the proved Perron convergence theorem and retains it in its result,
so lower-bound and recovery arguments can share the same normalization. -/

namespace EIGS

open MeasureTheory Filter Topology IGS.Sec31
open scoped BoundedContinuousFunction

set_option maxHeartbeats 3000000

variable {K : ℕ}

theorem xiUnitPotential_uniform_energy_convergence_fixed_normalization (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector))) :
      ∀ initialLevel (initialValues : XiVtx system initialLevel → ℝ),
        Tendsto (xiUnitPotentialUniformError system rulesConnected initialLevel initialValues
          (xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
            renormalizationEigenpair initialLevel initialValues)) atTop (nhds 0) ∧
        Tendsto (xiUnitPotentialScaledEnergy system rulesConnected resistanceRate normalization initialLevel initialValues)
          atTop (nhds ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive initialLevel).energy
            initialValues)) := by
  obtain ⟨profiles, contractionFactor, factorPositive, factorStrict, profilesPlus, profilesMinus,
      profilesMinimal, profilesOscillation⟩ := exists_rule_harmonic_profiles_strict_oscillation system rulesConnected
    distancePositive oneColourDistance resistanceVector vectorPositive
  have stepContraction := xiHarmonicStep_child_edge_contraction system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair profiles profilesPlus profilesMinus profilesMinimal
    contractionFactor profilesOscillation
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

theorem exists_xiNative_joint_recovery_fixed_normalization (system : EIGSData K)
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
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector))) :
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
  have fixedRecovery := xiUnitPotential_uniform_energy_convergence_fixed_normalization system rulesConnected distancePositive
    oneColourDistance resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence
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

theorem exists_xiClosed_native_joint_recovery_fixed_normalization_without_primitive (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector))) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
      intro sequence energyCauchy ambientZero
      exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
        mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
        (by simpa using ambientZero.norm)
    ∀ target : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative,
      ∃ sequence : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level),
        core.Strong sequence target.val ∧
        Tendsto (fun level => xiNativeScaledUnitEnergy system mass resistanceRate normalization level (sequence level))
          atTop (nhds (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable target)) := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  have closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  have continuousRecovery := exists_xiNative_joint_recovery_fixed_normalization system rulesConnected
    lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass distancePositive oneColourDistance
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence
  dsimp only
  intro target
  obtain ⟨approximation, stateApproximation, energyApproximation⟩ :=
    QuadraticEnergySpace.exists_original_state_energy_approximation originalDomain originalForm nonnegative closable target
  let representatives := fun depth => (xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).symm (approximation depth)
  have representativeFinite : ∀ depth, xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      ((representatives depth).val ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) ≠ ⊤ := by
    intro depth
    exact (xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive _).1
      (representatives depth).property
  have representativeImage : ∀ depth,
      core.embed (BoundedContinuousFunction.mkOfCompact (representatives depth).val) = (approximation depth).val := by
    intro depth
    exact congrArg Subtype.val ((xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).apply_symm_apply
      (approximation depth))
  have representativeEnergy : ∀ depth,
      (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        ((representatives depth).val ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal = originalForm (approximation depth) := by
    intro depth
    symm
    simpa only [representatives, originalForm, LinearEquiv.apply_symm_apply] using xiContinuousLpEnergyQuadraticForm_of_continuous system rulesConnected
      lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair (representatives depth)
  choose rowSelection rowSelectionTendsto rowState rowEnergy using
    fun depth => continuousRecovery (representatives depth).val (representativeFinite depth)
  let rows := fun depth level => xiUnitNativeL2 system rulesConnected mass (rowSelection depth level)
    (fun vertex => (representatives depth).val (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair (rowSelection depth level) vertex)) level
  have rowStateActual : ∀ depth, core.Strong (rows depth) (approximation depth).val := by
    intro depth
    have state := rowState depth
    change core.Strong (rows depth)
      (core.embed (BoundedContinuousFunction.mkOfCompact (representatives depth).val)) at state
    rw [representativeImage] at state
    exact state
  have rowEnergyActual : ∀ depth,
      Tendsto (fun level => xiNativeScaledUnitEnergy system mass resistanceRate normalization level (rows depth level))
        atTop (nhds (originalForm (approximation depth))) := by
    intro depth
    simpa only [representativeEnergy] using rowEnergy depth
  obtain ⟨reference, referenceStrong⟩ := core.exists_strong_recovery target.val
  have distancesZero : Tendsto (fun depth => ‖(approximation depth).val - target.val‖) atTop (nhds 0) := by
    simpa only [sub_self, norm_zero] using (stateApproximation.sub (tendsto_const_nhds (x := target.val))).norm
  obtain ⟨selection, _, diagonalLimit⟩ := IGS.Sec31.exists_diagonal_tendsto
    (fun depth => (‖(approximation depth).val - target.val‖, originalForm (approximation depth)))
    (fun depth level => (‖rows depth level - reference level‖,
      xiNativeScaledUnitEnergy system mass resistanceRate normalization level (rows depth level)))
    (0, QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable target)
    (distancesZero.prodMk_nhds energyApproximation)
    (fun depth => (core.strong_norm_sub_tendsto (rowStateActual depth) referenceStrong).prodMk_nhds
      (rowEnergyActual depth))
  refine ⟨fun level => rows (selection level) level, ?_, ?_⟩
  · exact core.strong_of_norm_sub_tendsto_zero _ reference target.val referenceStrong
      ((continuous_fst.tendsto _).comp diagonalLimit)
  · exact (continuous_snd.tendsto _).comp diagonalLimit

theorem exists_xiClosed_native_joint_recovery_with_normalized_limit_without_primitive (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
      intro sequence energyCauchy ambientZero
      exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
        mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
        (by simpa using ambientZero.norm)
    ∃ normalization : ℝ, 0 < normalization ∧
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (nhds (normalization • resistanceVector)) ∧
      ∀ target : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative,
      ∃ sequence : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level),
        core.Strong sequence target.val ∧
        Tendsto (fun level => xiNativeScaledUnitEnergy system mass resistanceRate normalization level (sequence level))
          atTop (nhds (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable target)) := by
  classical
  obtain ⟨normalization, normalizationPositive, normalizedConvergence⟩ :=
    exists_normalized_resistance_limit_of_positive_eigenpair system rulesConnected distancePositive resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair
  refine ⟨normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact exists_xiClosed_native_joint_recovery_fixed_normalization_without_primitive system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair normalization normalizationPositive normalizedConvergence

end EIGS

#print axioms EIGS.xiUnitPotential_uniform_energy_convergence_fixed_normalization
#print axioms EIGS.exists_xiNative_joint_recovery_fixed_normalization
#print axioms EIGS.exists_xiClosed_native_joint_recovery_fixed_normalization_without_primitive
#print axioms EIGS.exists_xiClosed_native_joint_recovery_with_normalized_limit_without_primitive
