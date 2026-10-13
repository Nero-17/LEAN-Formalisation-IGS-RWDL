import RequestProject.Section31.EIGSSelectedMoscoLower
import RequestProject.Section31.EIGSNativeFiniteResolventMinimum
import RequestProject.Section31.QuadraticEnergySmallStepMinimum
import RequestProject.Section31.EIGSL2EnergyDensity

/-! Actual native finite resolvents converge strongly to the actual closed-form
resolvent. The proof uses genuine forcing Strong convergence, the proved native
compactness and selected lower bound, exact joint recovery, and actual minimum
gaps. Steps satisfy 0 < step <= 1, matching the constructed target resolvent. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped ENNReal

set_option maxHeartbeats 4000000

private theorem objective_le_of_energy_liminf
    (step : ℝ) (stepPositive : 0 < step)
    (energies recoveryEnergies solutionDistances recoveryDistances : ℕ → ℝ)
    (limitEnergy recoveryEnergy solutionDistance recoveryDistance : ℝ)
    (energiesNonnegative : ∀ index, 0 ≤ energies index)
    (lower : ENNReal.ofReal limitEnergy ≤ liminf (fun index => ENNReal.ofReal (energies index)) atTop)
    (recoveryLimit : Tendsto recoveryEnergies atTop (nhds recoveryEnergy))
    (solutionDistanceLimit : Tendsto solutionDistances atTop (nhds solutionDistance))
    (recoveryDistanceLimit : Tendsto recoveryDistances atTop (nhds recoveryDistance))
    (minimal : ∀ index, step * energies index + solutionDistances index ≤
      step * recoveryEnergies index + recoveryDistances index) :
    step * limitEnergy + solutionDistance ≤ step * recoveryEnergy + recoveryDistance := by
  have upperLimit : Tendsto
      (fun index => (step * recoveryEnergies index + recoveryDistances index - solutionDistances index) / step)
      atTop (nhds ((step * recoveryEnergy + recoveryDistance - solutionDistance) / step)) :=
    (((tendsto_const_nhds.mul recoveryLimit).add recoveryDistanceLimit).sub solutionDistanceLimit).div_const step
  have pointwise : ∀ index, energies index ≤
      (step * recoveryEnergies index + recoveryDistances index - solutionDistances index) / step := by
    intro index
    apply (le_div_iff₀ stepPositive).mpr
    nlinarith [minimal index]
  have upperNonnegative : 0 ≤ (step * recoveryEnergy + recoveryDistance - solutionDistance) / step := by
    apply ge_of_tendsto upperLimit
    exact Eventually.of_forall fun index => (energiesNonnegative index).trans (pointwise index)
  have upperExtended := ENNReal.continuous_ofReal.continuousAt.tendsto.comp upperLimit
  have upperComparison := limsup_le_limsup (f := atTop)
    (Eventually.of_forall fun index => ENNReal.ofReal_le_ofReal (pointwise index))
  have realComparison : limitEnergy ≤ (step * recoveryEnergy + recoveryDistance - solutionDistance) / step :=
    (ENNReal.ofReal_le_ofReal_iff upperNonnegative).mp
      (lower.trans ((liminf_le_limsup).trans (upperComparison.trans upperExtended.limsup_eq.le)))
  have scaled := (le_div_iff₀ stepPositive).mp realComparison
  nlinarith

variable {K : ℕ}

theorem xiNativeFiniteResolvent_strong_limit (system : EIGSData K)
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
    ∀ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass))),
      ∀ (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1)
        (forcing : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
        (target : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass)),
      core.Strong forcing target →
      core.Strong (fun level => xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive (forcing level))
        (QuadraticEnergySpace.smallStepResolvent originalDomain originalForm nonnegative closable
          originalDense step stepPositive stepAtMostOne target) := by
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
  dsimp only
  intro originalDense step stepPositive stepAtMostOne forcing target forcingStrong
  let solutions := fun level => xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive (forcing level)
  let targetLift := QuadraticEnergySpace.smallStepLift originalDomain originalForm nonnegative closable
    originalDense step stepPositive stepAtMostOne target
  have targetLiftImage : (targetLift.value : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass)) =
      QuadraticEnergySpace.smallStepResolvent originalDomain originalForm nonnegative closable
        originalDense step stepPositive stepAtMostOne target :=
    QuadraticEnergySpace.smallStepLift_value originalDomain originalForm nonnegative closable originalDense
      step stepPositive stepAtMostOne target
  obtain ⟨recovery, recoveryStrong, recoveryEnergy⟩ :=
    exists_xiClosed_native_joint_recovery_fixed_normalization_without_primitive system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive normalizedConvergence targetLift.value
  have recoveryStrongResolvent : core.Strong recovery
      (QuadraticEnergySpace.smallStepResolvent originalDomain originalForm nonnegative closable
        originalDense step stepPositive stepAtMostOne target) := by
    simpa only [targetLiftImage] using recoveryStrong
  obtain ⟨normBound, forcingNormBound⟩ := core.weak_norm_bounded (core.strong_implies_weak forcingStrong)
  have normBoundNonnegative : 0 ≤ normBound := (norm_nonneg (forcing 0)).trans (forcingNormBound 0)
  have solutionNormBound : ∀ level, ‖solutions level‖ ≤ normBound := by
    intro level
    exact ((xiNativeFiniteResolvent_properties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive).1
        (forcing level)).2.2 |>.trans (forcingNormBound level)
  have solutionEnergyBound : ∀ level,
      xiNativeScaledUnitEnergy system mass resistanceRate normalization level (solutions level) ≤ normBound ^ 2 / step := by
    intro level
    have minimal := xiNativeFiniteResolvent_minimizes system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive (forcing level) 0
    simp only [xiNativeScaledUnitEnergy_zero system rulesConnected, mul_zero, zero_sub, norm_neg, zero_add] at minimal
    change step * xiNativeScaledUnitEnergy system mass resistanceRate normalization level (solutions level) +
      ‖solutions level - forcing level‖ ^ 2 ≤ ‖forcing level‖ ^ 2 at minimal
    have squareBound := pow_le_pow_left₀ (norm_nonneg (forcing level)) (forcingNormBound level) 2
    apply (le_div_iff₀ stepPositive).mpr
    nlinarith [sq_nonneg ‖solutions level - forcing level‖]
  have subsequentialLimit : ∀ (levels : ℕ → ℕ) (levelsStrict : StrictMono levels),
      ∃ selection : ℕ → ℕ, ∃ selectionStrict : StrictMono selection,
        (core.reindex (levels ∘ selection) (levelsStrict.comp selectionStrict).tendsto_atTop).Strong
          (fun index => solutions (levels (selection index)))
          (QuadraticEnergySpace.smallStepResolvent originalDomain originalForm nonnegative closable
            originalDense step stepPositive stepAtMostOne target) := by
    intro levels levelsStrict
    obtain ⟨selection, selectionStrict, limit, strongConvergence, limitBound⟩ :=
      exists_xiNativeEnergy_closed_subsequence system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive
        normalizedConvergence levels levelsStrict solutions normBound (normBound ^ 2 / step)
        (fun index => solutionNormBound (levels index)) (fun index => solutionEnergyBound (levels index))
    have limitMembership : limit ∈ QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative :=
      (QuadraticEnergySpace.closedExtendedEnergy_ne_top_iff originalDomain originalForm nonnegative closable limit).mp
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top limitBound)
    have lower := xiClosedExtendedEnergy_selected_mosco_lower system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive
      normalizedConvergence (levels ∘ selection) (levelsStrict.comp selectionStrict) solutions limit
      ((core.reindex (levels ∘ selection) (levelsStrict.comp selectionStrict).tendsto_atTop).strong_implies_weak strongConvergence)
    rw [QuadraticEnergySpace.closedExtendedEnergy_of_mem originalDomain originalForm nonnegative closable limit limitMembership] at lower
    simp only [Function.comp_def] at lower
    have selectedForcing := core.strong_reindex (levels ∘ selection)
      (levelsStrict.comp selectionStrict).tendsto_atTop forcingStrong
    have selectedRecovery := core.strong_reindex (levels ∘ selection)
      (levelsStrict.comp selectionStrict).tendsto_atTop recoveryStrong
    have solutionDistance := (core.reindex (levels ∘ selection)
      (levelsStrict.comp selectionStrict).tendsto_atTop).strong_norm_sub_tendsto strongConvergence selectedForcing
    have recoveryDistance := (core.reindex (levels ∘ selection)
      (levelsStrict.comp selectionStrict).tendsto_atTop).strong_norm_sub_tendsto selectedRecovery selectedForcing
    have limitMinimal := objective_le_of_energy_liminf step stepPositive
      (fun index => xiNativeScaledUnitEnergy system mass resistanceRate normalization (levels (selection index))
        (solutions (levels (selection index))))
      (fun index => xiNativeScaledUnitEnergy system mass resistanceRate normalization (levels (selection index))
        (recovery (levels (selection index))))
      (fun index => ‖solutions (levels (selection index)) - forcing (levels (selection index))‖ ^ 2)
      (fun index => ‖recovery (levels (selection index)) - forcing (levels (selection index))‖ ^ 2)
      (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable ⟨limit, limitMembership⟩)
      (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable targetLift.value)
      (‖limit - target‖ ^ 2) (‖(targetLift.value : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass)) - target‖ ^ 2)
      (fun index => xiNativeScaledUnitEnergy_nonnegative system mass resistanceRate normalization ratePositive.le
        normalizationPositive.le _ _)
      lower (recoveryEnergy.comp (levelsStrict.comp selectionStrict).tendsto_atTop)
      (solutionDistance.pow 2) (recoveryDistance.pow 2)
      (fun index => xiNativeFiniteResolvent_minimizes system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass (levels (selection index)) resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive
        (forcing (levels (selection index))) (recovery (levels (selection index))))
    let closedLimit : QuadraticEnergySpace
        (QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative)
        (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable)
        (QuadraticEnergySpace.closedForm_nonnegative originalDomain originalForm nonnegative closable) :=
      ⟨⟨limit, limitMembership⟩⟩
    have unique := QuadraticEnergySpace.smallStep_minimizer_unique originalDomain originalForm nonnegative closable
      originalDense step stepPositive stepAtMostOne target closedLimit limitMinimal
    have limitEquality : limit = QuadraticEnergySpace.smallStepResolvent originalDomain originalForm nonnegative closable
        originalDense step stepPositive stepAtMostOne target := by
      have equality := congrArg
        (fun values : QuadraticEnergySpace
          (QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative)
          (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable)
          (QuadraticEnergySpace.closedForm_nonnegative originalDomain originalForm nonnegative closable) =>
          (values.value : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass))) unique
      simpa only [closedLimit, targetLiftImage, QuadraticEnergySpace.smallStepLift_value] using equality
    refine ⟨selection, selectionStrict, ?_⟩
    simpa only [limitEquality] using strongConvergence
  apply core.strong_of_norm_sub_tendsto_zero solutions recovery _ recoveryStrongResolvent
  apply Metric.tendsto_nhds.mpr
  intro tolerance tolerancePositive
  simp only [Real.dist_eq, sub_zero, abs_norm]
  by_contra notEventually
  have frequent : ∃ᶠ level in atTop, tolerance ≤ ‖solutions level - recovery level‖ :=
    (Filter.not_eventually.mp notEventually).mono fun _ contrary => le_of_not_gt contrary
  obtain ⟨levels, levelsStrict, bad⟩ := extraction_forall_of_frequently (fun _ : ℕ => frequent)
  obtain ⟨selection, selectionStrict, selectedStrong⟩ := subsequentialLimit levels levelsStrict
  have differenceLimit := (core.reindex (levels ∘ selection)
    (levelsStrict.comp selectionStrict).tendsto_atTop).strong_norm_sub_tendsto selectedStrong
    (core.strong_reindex (levels ∘ selection) (levelsStrict.comp selectionStrict).tendsto_atTop recoveryStrongResolvent)
  have differenceZero : Tendsto (fun index => ‖solutions (levels (selection index)) - recovery (levels (selection index))‖)
      atTop (nhds 0) := by
    simpa only [Function.comp_def, sub_self, norm_zero] using differenceLimit
  obtain ⟨index, small⟩ := (differenceZero.eventually_lt_const tolerancePositive).exists
  exact (not_le_of_gt small) (bad (selection index))

theorem exists_xiNativeFiniteResolventStrong_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
    let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    let oneColourDistance : K = 1 → ∀ colour,
        2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
      intro _ colour
      exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
        (system.plant_ne colour) (plantingNonadjacent colour)
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ ratePositive : 0 < resistanceRate, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (nhds (normalization • resistanceVector)) ∧
      let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive
      let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
        intro sequence energyCauchy ambientZero
        exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
          mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
          (by simpa using ambientZero.norm)
      ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass))),
        ∀ (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1)
          (forcing : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
          (target : Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass)),
        core.Strong forcing target →
        core.Strong (fun level => xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive (forcing level))
          (QuadraticEnergySpace.smallStepResolvent originalDomain originalForm nonnegative closable
            originalDense step stepPositive stepAtMostOne target) := by
  classical
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
      originalDense, originalNonnegative⟩ :=
    exists_xiDenseLpQuadraticEnergy_of_rules system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  obtain ⟨normalization, normalizationPositive, normalizedConvergence⟩ :=
    exists_normalized_resistance_limit_of_positive_eigenpair system rulesConnected distancePositive resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, originalDense, ?_⟩
  exact xiNativeFiniteResolvent_strong_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence originalDense

end EIGS

#print axioms EIGS.xiNativeFiniteResolvent_strong_limit

#print axioms EIGS.exists_xiNativeFiniteResolventStrong_of_rules
