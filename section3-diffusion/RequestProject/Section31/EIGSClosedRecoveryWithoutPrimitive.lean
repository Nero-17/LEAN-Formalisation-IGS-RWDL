import RequestProject.Section31.EIGSL2ClosabilityWithoutPrimitive
import RequestProject.Section31.EIGSNativeJointRecovery
import RequestProject.Section31.QuadraticEnergyClosureRecovery

/-! No primitive degree-matrix assumption is needed.

Full-original-index recovery on the entire constructed closed energy
domain. Continuous representatives are only used for an approximating core;
the target is an arbitrary element of the native closed domain. -/

namespace EIGS

open MeasureTheory Filter Topology IGS.Sec31
open scoped BoundedContinuousFunction

set_option maxHeartbeats 3000000

variable {K : ℕ}

theorem exists_xiClosed_native_joint_recovery_without_primitive (system : EIGSData K)
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
  obtain ⟨normalization, normalizationPositive, continuousRecovery⟩ := exists_xiNative_joint_recovery system rulesConnected
    lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass distancePositive oneColourDistance
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  dsimp only
  refine ⟨normalization, normalizationPositive, ?_⟩
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

end EIGS

#print axioms EIGS.exists_xiClosed_native_joint_recovery_without_primitive
