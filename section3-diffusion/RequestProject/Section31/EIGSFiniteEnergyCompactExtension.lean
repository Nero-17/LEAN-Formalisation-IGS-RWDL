import RequestProject.Section31.EIGSFiniteEnergyContinuousLinearExtension
import RequestProject.Section31.EIGSFiniteEnergyGeometricTail
import RequestProject.Section31.CompactContinuousKernelRows
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The actual anchored energy extension into continuous functions is compact
when resistanceRate > 1. Its actual finite-level harmonic projections factor
through finite-dimensional vertex values and converge in operator norm by the
uniform geometric energy tail. Compactness is proved here, not a model input.
Candidate source: compilation is not claimed. -/

namespace EIGS
open IGS.Sec31 Filter Topology
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

def xiHarmonicAnchoredEnergyMap
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (anchor : XiVertexUnion system) (level : ℕ) :
    (XiVtx system level → ℝ) →ₗ[ℝ]
      XiAnchoredEnergyHilbert system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        eigenpair anchor where
  toFun values := ⟨⟨xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair level values, by
    apply (xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive _).2
    rw [xiHarmonicUnionExtension_energy]
    exact ENNReal.ofReal_ne_top⟩⟩
  map_add' := by
    intro first second
    apply (AnchoredTraceEnergySpace.equivDomain _ _ _ _).injective
    apply Subtype.ext
    exact map_add (xiHarmonicUnionLinearMap system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair level) first second
  map_smul' := by
    intro scalar values
    apply (AnchoredTraceEnergySpace.equivDomain _ _ _ _).injective
    apply Subtype.ext
    exact map_smul (xiHarmonicUnionLinearMap system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair level) scalar values

theorem xiAnchoredEnergy_continuous_extension_isCompact
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (resistanceRate : ℝ) (rateGreaterThanOne : 1 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (contractionFactor : ℝ) (factorPositive : 0 < contractionFactor) (factorStrict : contractionFactor < 1)
    (stepContraction : ∀ level (oldValues : XiVtx system level → ℝ) (edge : XiEdge system.toRuleData (level + 1)),
      |xiHarmonicStep system rulesConnected resistanceRate (zero_lt_one.trans rateGreaterThanOne)
          resistanceVector vectorPositive eigenpair level oldValues (XiTail system (level + 1) edge) -
        xiHarmonicStep system rulesConnected resistanceRate (zero_lt_one.trans rateGreaterThanOne)
          resistanceVector vectorPositive eigenpair level oldValues (XiHead system (level + 1) edge)| ≤
        |oldValues (XiTail system level edge.1) - oldValues (XiHead system level edge.1)| * contractionFactor)
    (anchor : XiVertexUnion system) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    ∀ extension : XiAnchoredEnergyHilbert system rulesConnected resistanceRate (zero_lt_one.trans rateGreaterThanOne)
        resistanceVector vectorPositive eigenpair anchor →L[ℝ]
      C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ),
      (∀ values vertex, extension values (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive
        distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) = values.value.val vertex) →
      IsCompactOperator extension := by
  let ratePositive := zero_lt_one.trans rateGreaterThanOne
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  intro extension agreement
  let restriction := fun level => ContinuousLinearMap.pi (fun vertex : XiVtx system level =>
    xiAnchoredEnergyEvaluation system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair anchor (xiVertexEmbedding system level vertex))
  let harmonic := fun level => (xiHarmonicAnchoredEnergyMap system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive eigenpair anchor level).toContinuousLinearMap
  let approximation := fun level => (extension.comp (harmonic level)).comp (restriction level)
  have approximationCompact : ∀ level, IsCompactOperator (approximation level) := by
    intro level
    have harmonicCompact : IsCompactOperator (harmonic level) := by
      refine ⟨(harmonic level) '' Metric.closedBall 0 1,
        (isCompact_closedBall (0 : XiVtx system level → ℝ) 1).image (harmonic level).continuous, ?_⟩
      apply Filter.mem_of_superset (Metric.closedBall_mem_nhds _ (by norm_num : (0 : ℝ) < 1))
      intro values membership
      exact ⟨values, membership, rfl⟩
    exact (harmonicCompact.clm_comp extension).comp_clm (restriction level)
  obtain ⟨tailConstant, tailPositive, tailBound⟩ :=
    exists_xiContinuousHarmonicProjection_geometric_energy_tail system rulesConnected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair resistanceRate rateGreaterThanOne resistanceVector
      vectorPositive eigenpair contractionFactor factorPositive factorStrict stepContraction
  have operatorBound : ∀ level, ‖approximation level - extension‖ ≤
      tailConstant * Real.sqrt resistanceRate⁻¹ ^ level := by
    intro level
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro values valuesUnit
    have restrictionIdentity : extension values ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive
        distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair = values.value.val :=
      funext (agreement values)
    have targetFinite : extension values ∈ xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive
        distanceRate distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive := by
      change extension values ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair ∈
          xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive
      rw [restrictionIdentity]
      exact values.value.property
    have approximationAgreement : ∀ index vertex, approximation index values
        (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) =
        xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
          eigenpair index (extension values ∘ xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair index) vertex := by
      intro index vertex
      change extension ((harmonic index) ((restriction index) values)) _ = _
      rw [agreement]
      change xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        eigenpair index (fun finiteVertex => values.value.val (xiVertexEmbedding system index finiteVertex)) vertex = _
      congr 2
      funext finiteVertex
      exact (agreement values (xiVertexEmbedding system index finiteVertex)).symm
    have errorBound := tailBound ⟨extension values, targetFinite⟩
      (fun index => approximation index values) approximationAgreement level
    rw [restrictionIdentity] at errorBound
    have energyAtMostOne : (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        values.value.val).toReal ≤ 1 := by
      have normIdentity := xiAnchoredEnergyHilbert_norm_sq system rulesConnected resistanceRate ratePositive
        resistanceVector vectorPositive eigenpair anchor values
      rw [valuesUnit] at normIdentity
      nlinarith [sq_nonneg (values.value.val anchor)]
    have rootAtMostOne : Real.sqrt
        ((xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
          values.value.val).toReal) ≤ 1 := by
      have rootBound := Real.sqrt_le_sqrt energyAtMostOne
      simpa only [Real.sqrt_one] using rootBound
    change ‖approximation level values - extension values‖ ≤ _
    calc
      _ ≤ tailConstant * Real.sqrt
          ((xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            values.value.val).toReal) * Real.sqrt resistanceRate⁻¹ ^ level := errorBound
      _ ≤ tailConstant * 1 * Real.sqrt resistanceRate⁻¹ ^ level := by
        gcongr
      _ = tailConstant * Real.sqrt resistanceRate⁻¹ ^ level := by ring
  have factorStrict' : Real.sqrt resistanceRate⁻¹ < 1 := by
    have inverseStrict := (inv_lt_one₀ ratePositive).mpr rateGreaterThanOne
    have square := Real.sq_sqrt (inv_pos.mpr ratePositive).le
    nlinarith [Real.sqrt_nonneg resistanceRate⁻¹]
  have boundZero : Tendsto (fun level : ℕ => tailConstant * Real.sqrt resistanceRate⁻¹ ^ level) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg _) factorStrict').const_mul tailConstant
  have normZero : Tendsto (fun level => ‖approximation level - extension‖) atTop (𝓝 0) :=
    squeeze_zero (fun level => (approximation level - extension).opNorm_nonneg) operatorBound boundZero
  have operatorConvergence : Tendsto approximation atTop (𝓝 extension) := by
    with_reducible_and_instances
      exact (tendsto_iff_norm_sub_tendsto_zero (f := approximation) (b := extension)).2 normZero
  exact isCompactOperator_of_tendsto operatorConvergence
    (Filter.Eventually.of_forall approximationCompact)

theorem exists_xiAnchoredEnergy_compact_continuous_extension_of_rules
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (canonicalRateGreaterThanOne : 1 < system.resistanceSpectralRadius rulesConnected distancePositive) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
    ∃ resistanceRate : ℝ, ∃ rateGreaterThanOne : 1 < resistanceRate,
    ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
    ∃ eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour,
    ∀ anchor : XiVertexUnion system,
    ∃ extension : XiAnchoredEnergyHilbert system rulesConnected resistanceRate (zero_lt_one.trans rateGreaterThanOne)
        resistanceVector vectorPositive eigenpair anchor →L[ℝ] C(parameters.LimitSpace, ℝ),
      IsCompactOperator extension ∧
      ∀ values vertex, extension values (xiCompletionUnionEmbedding system rulesConnected parameters.lengths
        parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
        (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair vertex) = values.value.val vertex := by
  intro parameters distanceGreaterThanOne
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj (system.plant_ne colour) (plantingNonadjacent colour)
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, eigenpair,
      contractionFactor, factorPositive, factorStrict, stepContraction⟩ :=
    exists_xiHarmonic_strict_contraction system rulesConnected distancePositive oneColourDistance
  have rateEquality := system.resistanceSpectralRadius_eq_of_positive_eigenpair rulesConnected distancePositive
    ratePositive vectorPositive (funext eigenpair)
  have rateGreaterThanOne : 1 < resistanceRate := by
    rw [rateEquality]
    exact canonicalRateGreaterThanOne
  have bijective : Function.Bijective (xiFiniteEnergyRestriction system rulesConnected parameters.lengths
      parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
      resistanceRate (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive) :=
    ⟨xiFiniteEnergyRestriction_injective system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair resistanceRate
        (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive,
      xiFiniteEnergyRestriction_surjective_of_step_contraction system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair resistanceRate rateGreaterThanOne
        resistanceVector vectorPositive eigenpair contractionFactor factorPositive factorStrict stepContraction⟩
  refine ⟨resistanceRate, rateGreaterThanOne, resistanceVector, vectorPositive, eigenpair, fun anchor => ?_⟩
  obtain ⟨extension, agreement⟩ := exists_xiAnchoredEnergy_continuous_linear_extension_of_bijective system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne
    parameters.eigenpair resistanceRate (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive eigenpair anchor bijective
  refine ⟨extension, ?_, agreement⟩
  exact xiAnchoredEnergy_continuous_extension_isCompact system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair resistanceRate rateGreaterThanOne
    resistanceVector vectorPositive eigenpair contractionFactor factorPositive factorStrict stepContraction anchor extension agreement

end
end EIGS

#print axioms EIGS.xiHarmonicAnchoredEnergyMap
#print axioms EIGS.xiAnchoredEnergy_continuous_extension_isCompact
#print axioms EIGS.exists_xiAnchoredEnergy_compact_continuous_extension_of_rules
