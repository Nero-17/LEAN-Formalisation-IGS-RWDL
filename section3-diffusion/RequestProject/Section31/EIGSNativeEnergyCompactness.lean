import RequestProject.Section31.EIGSUnitProjectionCoefficients

/-! Bounded actual native norm and original-unit energy yield a genuinely
strongly convergent subsequence in the varying speed L² spaces. This theorem
does not yet assert closed-energy-domain membership or an energy liminf bound. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

set_option maxHeartbeats 2400000

variable {K : ℕ}

theorem exists_xiNativeEnergy_strong_subsequence (system : EIGSData K)
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
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (levels : ℕ → ℕ) (levelsStrict : StrictMono levels)
    (sequence : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
    (normBound energyBound : ℝ) (normsBounded : ∀ index, ‖sequence (levels index)‖ ≤ normBound)
    (energiesBounded : ∀ index, xiNativeScaledUnitEnergy system mass resistanceRate normalization (levels index) (sequence (levels index)) ≤ energyBound) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
    ∃ selection : ℕ → ℕ, ∃ selectionStrict : StrictMono selection,
      ∃ limit : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass),
      (core.reindex (levels ∘ selection) (levelsStrict.comp selectionStrict).tendsto_atTop).Strong (fun index => sequence (levels (selection index))) limit ∧
      ∃ boundaryLimits : ∀ coarseLevel, XiVtx system coarseLevel → ℝ,
      (∀ coarseLevel, Tendsto
        (fun index => xiNativeBoundaryValues system mass coarseLevel (levels (selection index)) (sequence (levels (selection index))))
        atTop (nhds (boundaryLimits coarseLevel))) ∧
      ∃ approximations : ℕ → C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ),
      (∀ coarseLevel vertex, approximations coarseLevel
          (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) =
        xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
          coarseLevel (boundaryLimits coarseLevel) vertex) ∧
      Tendsto (fun coarseLevel => core.embed (BoundedContinuousFunction.mkOfCompact (approximations coarseLevel)))
        atTop (nhds limit) := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  obtain ⟨boundaryLimits, selection, selectionStrict, coefficientConvergence⟩ :=
    exists_xiNativeBoundaryValues_common_subsequence system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive levels levelsStrict.tendsto_atTop sequence
      normBound energyBound normsBounded energiesBounded
  choose extensionMap extensionAgreement extensionInjective inverseConstant inversePositive inverseBound using
    fun coarseLevel => exists_xiHarmonic_boundary_L2_control system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass distancePositive oneColourDistance resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair coarseLevel
  obtain ⟨recoveryNormalization, recoveryPositive, recovery⟩ := exists_xiUnitPotential_uniform_energy_convergence_for_eigenpair
    system rulesConnected distancePositive oneColourDistance resistanceRate ratePositive resistanceVector vectorPositive eigenpair
  have fixedConvergence : ∀ coarseLevel (values : XiVtx system coarseLevel → ℝ),
      core.Strong (xiUnitNativeL2 system rulesConnected mass coarseLevel values)
        (xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass (extensionMap coarseLevel values)) := by
    intro coarseLevel values
    apply xiUnitNativeL2_strong_of_uniform system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass coarseLevel values (extensionMap coarseLevel values)
    have agreement : extensionMap coarseLevel values ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair =
        xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair coarseLevel values :=
      funext (extensionAgreement coarseLevel values)
    rw [agreement]
    exact (recovery coarseLevel values).1
  have movingConvergence : ∀ coarseLevel,
      (core.reindex (levels ∘ selection) (levelsStrict.comp selectionStrict).tendsto_atTop).Strong
        (fun index => xiUnitNativeL2 system rulesConnected mass coarseLevel
          (xiNativeBoundaryValues system mass coarseLevel (levels (selection index)) (sequence (levels (selection index)))) (levels (selection index)))
        (xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
          (extensionMap coarseLevel (boundaryLimits coarseLevel))) := by
    intro coarseLevel
    refine (core.reindex (levels ∘ selection) (levelsStrict.comp selectionStrict).tendsto_atTop).strong_linear_rows_of_coordinates_tendsto
      (fun index => xiUnitNativeLinearMap system rulesConnected mass coarseLevel (levels (selection index)))
      ((xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass).toLinearMap.comp
        (extensionMap coarseLevel)) ?_
      (fun index => xiNativeBoundaryValues system mass coarseLevel (levels (selection index)) (sequence (levels (selection index))))
      (boundaryLimits coarseLevel) (coefficientConvergence coarseLevel)
    intro values
    simpa only [xiUnitNativeLinearMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      using core.strong_reindex (levels ∘ selection) (levelsStrict.comp selectionStrict).tendsto_atTop
        (fixedConvergence coarseLevel values)
  obtain ⟨tailConstant, tailPositive, tailBound⟩ := exists_xiUnitProjection_native_tail_for_eigenpair system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive mass resistanceRate ratePositive resistanceVector vectorPositive
    eigenpair normalization normalizationPositive
  have actualTail : ∀ coarseLevel, ∀ᶠ index in atTop,
      ‖sequence (levels (selection index)) - xiUnitNativeL2 system rulesConnected mass coarseLevel
        (xiNativeBoundaryValues system mass coarseLevel (levels (selection index)) (sequence (levels (selection index)))) (levels (selection index))‖ ≤
      tailConstant * (Real.sqrt (mass.rate * resistanceRate))⁻¹ ^ coarseLevel * Real.sqrt energyBound := by
    intro coarseLevel
    filter_upwards [(levelsStrict.comp selectionStrict).tendsto_atTop.eventually (eventually_ge_atTop coarseLevel)] with index levelsOrdered
    have estimate := tailBound coarseLevel (levels (selection index)) levelsOrdered (fun vertex => sequence (levels (selection index)) vertex)
    rw [xiFiniteSpeedL2_representative,
      ← xiNativeBoundaryValues_projection_eq system rulesConnected mass coarseLevel (levels (selection index)) levelsOrdered] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (energiesBounded (selection index)))
      (mul_nonneg tailPositive.le (pow_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) coarseLevel)))
  have scaleGreaterOne := xiAnalyticTimeRate_gt_one system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive mass resistanceRate ratePositive resistanceVector vectorPositive (funext eigenpair)
  have rootGreaterOne : 1 < Real.sqrt (mass.rate * resistanceRate) :=
    Real.lt_sqrt_of_sq_lt (by simpa only [one_pow] using scaleGreaterOne)
  have errorsTendsto : Tendsto
      (fun coarseLevel : ℕ => tailConstant * (Real.sqrt (mass.rate * resistanceRate))⁻¹ ^ coarseLevel * Real.sqrt energyBound)
      atTop (nhds 0) := by
    have geometric := tendsto_pow_atTop_nhds_zero_of_lt_one
      (inv_nonneg.2 (Real.sqrt_nonneg (mass.rate * resistanceRate)))
      ((inv_lt_one₀ (zero_lt_one.trans rootGreaterOne)).2 rootGreaterOne)
    simpa only [mul_zero, zero_mul] using (geometric.const_mul tailConstant).mul_const (Real.sqrt energyBound)
  obtain ⟨limit, approximationConvergence, strongLimit, _⟩ := (core.reindex (levels ∘ selection) (levelsStrict.comp selectionStrict).tendsto_atTop).exists_strong_limit_of_projection_tails
    (fun index => sequence (levels (selection index)))
    (fun coarseLevel index => xiUnitNativeL2 system rulesConnected mass coarseLevel
      (xiNativeBoundaryValues system mass coarseLevel (levels (selection index)) (sequence (levels (selection index)))) (levels (selection index)))
    (fun coarseLevel => xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass (extensionMap coarseLevel (boundaryLimits coarseLevel)))
    (fun coarseLevel => tailConstant * (Real.sqrt (mass.rate * resistanceRate))⁻¹ ^ coarseLevel * Real.sqrt energyBound)
    movingConvergence actualTail errorsTendsto
  exact ⟨selection, selectionStrict, limit, strongLimit, boundaryLimits, coefficientConvergence,
    (fun coarseLevel => extensionMap coarseLevel (boundaryLimits coarseLevel)),
    (fun coarseLevel => extensionAgreement coarseLevel (boundaryLimits coarseLevel)), approximationConvergence⟩

end EIGS

#print axioms EIGS.exists_xiNativeEnergy_strong_subsequence


