import RequestProject.Section31.EIGSClosedFiniteBornPointEvaluation
import RequestProject.Section31.EIGSAddressStarAnchorEnergy
import RequestProject.Section31.AddressStarPointIdentification
import RequestProject.Section31.QuadraticEnergyFunctionalRecovery

/-! Every actual graph-bounded core evaluation agrees with any continuous
representative of a value in the same closed domain. Strong original recovery,
actual weighted-star anchors, star mass and mesh, and the already proved
incidence-resistance decay fill the two-limit argument internally.
Candidate source, awaiting compilation. -/
namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical BigOperators BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 7000000
variable {K : ℕ}

theorem xiClosedFiniteBorn_evaluation_eq_continuous (system : EIGSData K)
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
    :
    letI xiClosedBornStatementCompactSpace := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
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
    ∀ (birth : ℕ) (vertex : XiVtx system birth)
      (evaluation : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative →ₗ[ℝ] ℝ)
      (normConstant energyConstant : ℝ), 0 ≤ normConstant → 0 ≤ energyConstant →
      (∀ values : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative,
        evaluation values ^ 2 ≤ normConstant * ‖values.val‖ ^ 2 +
          energyConstant * QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable values) →
      (∀ values : originalDomain,
        evaluation ⟨values.val, QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative values⟩ =
          ((xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).symm values).val
              (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
                (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair birth vertex)) →
      ∀ (target : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative)
        (representative : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)),
        xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass representative = target.val →
        evaluation target = representative (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair birth vertex) := by

  letI xiClosedBornProofCompactSpace := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
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
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  dsimp only
  intro birth vertex evaluation normConstant energyConstant normNonnegative energyNonnegative
    evaluationBound agreement target representative representativeImage
  obtain ⟨sequence, ambientConvergence, energyConvergence, evaluationConvergence⟩ :=
    QuadraticEnergySpace.exists_original_functional_approximation originalDomain originalForm nonnegative closable
      evaluation normConstant energyConstant normNonnegative energyNonnegative evaluationBound target
  let energyEquiv := xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let continuousSequence := fun index => (energyEquiv.symm (sequence index)).val
  have sequenceImage (index : ℕ) : core.embed (BoundedContinuousFunction.mkOfCompact (continuousSequence index)) =
      (sequence index).val := congrArg Subtype.val (energyEquiv.apply_symm_apply (sequence index))
  have sequenceFinite (index : ℕ) : xiExtendedWeightedEnergy system resistanceRate ratePositive
      resistanceVector vectorPositive (continuousSequence index ∘ xiCompletionUnionEmbedding system rulesConnected
        lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) ≠ ⊤ :=
    (xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive _).1
      (energyEquiv.symm (sequence index)).property
  have sequenceEnergy (index : ℕ) :
      (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (continuousSequence index ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal = originalForm (sequence index) := by
    symm
    simpa only [continuousSequence, energyEquiv, originalForm, LinearEquiv.apply_symm_apply] using
      xiContinuousLpEnergyQuadraticForm_of_continuous system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair (energyEquiv.symm (sequence index))
  have representativeCore : core.embed (BoundedContinuousFunction.mkOfCompact representative) = target.val :=
    representativeImage
  have ambientError : Tendsto (fun index =>
      ∫ address, (continuousSequence index (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair address) -
        representative (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair address)) ^ 2 ∂mass.addressMeasure) atTop (𝓝 0) := by
    have identities (index : ℕ) := xiContinuous_L2_norm_sq_address_integral system rulesConnected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair mass (continuousSequence index - representative)
    have errorConvergence := ((ambientConvergence.sub_const target.val).norm.pow 2)
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at errorConvergence
    have equality (index : ℕ) :
        (∫ address, (continuousSequence index (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair address) -
          representative (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair address)) ^ 2 ∂mass.addressMeasure) =
          ‖(sequence index).val - target.val‖ ^ 2 := by
      rw [← identities]
      change ‖core.embed (BoundedContinuousFunction.mkOfCompact (continuousSequence index) -
        BoundedContinuousFunction.mkOfCompact representative)‖ ^ 2 = _
      rw [map_sub, sequenceImage, representativeCore]
    simpa only [equality] using errorConvergence
  have pointConvergence : Tendsto (fun index => continuousSequence index
      (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair birth vertex)) atTop (𝓝 (evaluation target)) := by
    simpa only [agreement, continuousSequence, energyEquiv] using evaluationConvergence
  obtain ⟨anchorConstant, anchorPositive, anchorBound⟩ := exists_xiAddressStar_anchor_energy_bound system
    rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance
    lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair
  obtain ⟨massLower, massUpper, massLowerPositive, massUpperPositive, massBounds⟩ :=
    exists_xiAddressStarWeight_mass_comparison system mass
  let weights := fun age => xiAddressStarWeight system (birth + age) (xiForward system birth age vertex)
  have starMassPositive (age : ℕ) : 0 < ∫ address, weights age address ∂mass.addressMeasure := by
    have incidencePositive : 0 < (xiVertexIncidenceCount system (birth + age) (xiForward system birth age vertex) : ℝ) := by
      exact_mod_cast xiVertexIncidenceCount_positive system rulesConnected _ _
    exact (mul_pos (div_pos massLowerPositive (pow_pos mass.rate_positive _)) incidencePositive).trans_le
      (massBounds (birth + age) (xiForward system birth age vertex)).1
  let decay := fun age => 1 / ((mass.rate * resistanceRate) ^ (birth + age) *
    (∫ address, weights age address ∂mass.addressMeasure))
  have decayBound (age : ℕ) : decay age ≤ (1 / massLower) *
      (1 / ((xiVertexIncidenceCount system (birth + age) (xiForward system birth age vertex) : ℝ) *
        resistanceRate ^ (birth + age))) := by
    have denominatorBound := mul_le_mul_of_nonneg_left
      (massBounds (birth + age) (xiForward system birth age vertex)).1
      (pow_pos (mul_pos mass.rate_positive ratePositive) (birth + age)).le
    have denominatorIdentity : (mass.rate * resistanceRate) ^ (birth + age) *
        (massLower / mass.rate ^ (birth + age) *
          (xiVertexIncidenceCount system (birth + age) (xiForward system birth age vertex) : ℝ)) =
        massLower * ((xiVertexIncidenceCount system (birth + age) (xiForward system birth age vertex) : ℝ) *
          resistanceRate ^ (birth + age)) := by
      rw [mul_pow]
      field_simp [(pow_pos mass.rate_positive (birth + age)).ne']
      <;> ring
    rw [denominatorIdentity] at denominatorBound
    have incidencePositive : 0 < (xiVertexIncidenceCount system (birth + age) (xiForward system birth age vertex) : ℝ) := by
      exact_mod_cast xiVertexIncidenceCount_positive system rulesConnected _ _
    have bound := one_div_le_one_div_of_le
      (mul_pos massLowerPositive (mul_pos incidencePositive (pow_pos ratePositive (birth + age)))) denominatorBound
    simpa only [decay, one_div, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using bound
  have decayLimit : Tendsto decay atTop (𝓝 0) := by
    have inverseLimit := (xiIncidence_resistance_inverse_tendsto_zero_without_primitive system rulesConnected
      plantingNonadjacent resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      birth vertex).const_mul (1 / massLower)
    apply squeeze_zero (fun age => (one_div_pos.mpr
      (mul_pos (pow_pos (mul_pos mass.rate_positive ratePositive) (birth + age))
        (starMassPositive age))).le) decayBound
    simpa only [mul_zero] using inverseLimit
  let mesh := fun age => (xiMaximumColourLength system lengths +
    (xiRuleRadius system lengths * distanceRate⁻¹) / (1 - distanceRate⁻¹)) * distanceRate⁻¹ ^ (birth + age)
  have meshLimit : Tendsto mesh atTop (𝓝 0) := by
    have geometric := tendsto_pow_atTop_nhds_zero_of_lt_one
      (inv_pos.mpr (zero_lt_one.trans distanceRateGreaterThanOne)).le
      ((inv_lt_one₀ (zero_lt_one.trans distanceRateGreaterThanOne)).mpr distanceRateGreaterThanOne)
    have convergence := (geometric.const_mul (distanceRate⁻¹ ^ birth)).const_mul
      (xiMaximumColourLength system lengths + (xiRuleRadius system lengths * distanceRate⁻¹) / (1 - distanceRate⁻¹))
    simpa only [mesh, pow_add, mul_zero] using convergence
  apply continuous_point_limit_eq_of_weighted_stars mass.addressMeasure
    (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair)
    (measurable_xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair)
    (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair birth vertex)
    weights
    (fun age => (measurable_of_countable (xiEdgeStarMultiplicity system (birth + age)
      (xiForward system birth age vertex))).comp (measurable_xiAddressEdge system (birth + age)))
    (fun age address => (xiEdgeStarMultiplicity_bounds system (birth + age) (xiForward system birth age vertex) _).1)
    (fun age address => (xiEdgeStarMultiplicity_bounds system (birth + age) (xiForward system birth age vertex) _).2)
    starMassPositive mesh meshLimit
    (fun age address supported => by
      have bound := xiAddressStarWeight_support_mesh system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair (birth + age) (xiForward system birth age vertex) address supported
      simpa only [xiCompletionEmbedding_forward] using bound)
    decay decayLimit anchorConstant continuousSequence representative
    (fun index => originalForm (sequence index))
    (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable target)
    energyConvergence (evaluation target) pointConvergence ambientError
  intro index age anchor
  have bound := anchorBound (continuousSequence index) (sequenceFinite index) (birth + age)
    (xiForward system birth age vertex) anchor
  rw [xiCompletionEmbedding_forward, sequenceEnergy] at bound
  have coefficientIdentity : anchorConstant * decay age *
      (∫ address, weights age address ∂mass.addressMeasure) =
        anchorConstant / (mass.rate * resistanceRate) ^ (birth + age) := by
    dsimp only [decay]
    field_simp [(starMassPositive age).ne',
      (pow_pos (mul_pos mass.rate_positive ratePositive) (birth + age)).ne']
    <;> ring
  rw [coefficientIdentity]
  exact bound

theorem exists_xiClosedFiniteBorn_point_evaluation_with_continuous_agreement (system : EIGSData K)
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
    (primitiveDegree : (degreeMatrix system).IsPrimitive) :
    letI xiClosedBornStatementCompactSpace := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
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
    ∀ (birth : ℕ) (vertex : XiVtx system birth),
      ∃ normConstant energyConstant : ℝ, 0 < normConstant ∧ 0 < energyConstant ∧
      ∃ evaluation : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative →ₗ[ℝ] ℝ,
        (∀ values : originalDomain,
          evaluation ⟨values.val, QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative values⟩ =
            ((xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
              distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).symm values).val
              (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
                (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair birth vertex)) ∧
        (∀ age (target : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative),
          evaluation target ^ 2 ≤
            normConstant * (mass.rate ^ (birth + age) /
              finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age) * ‖target.val‖ ^ 2 +
            energyConstant * (1 / (finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age *
              resistanceRate ^ (birth + age))) *
                QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable target) ∧
        ∀ (target : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative)
          (representative : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)),
          xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass representative = target.val →
          evaluation target = representative (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair birth vertex) := by

  letI xiClosedBornProofCompactSpace := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
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
  dsimp only
  intro birth vertex
  obtain ⟨normConstant, energyConstant, normPositive, energyPositive, evaluation, agreement, bounds⟩ :=
    exists_xiClosedFiniteBorn_point_evaluation system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair primitiveDegree birth vertex
  refine ⟨normConstant, energyConstant, normPositive, energyPositive, evaluation, agreement, bounds, ?_⟩
  intro target representative representativeImage
  exact xiClosedFiniteBorn_evaluation_eq_continuous system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
    mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair birth vertex evaluation
    (normConstant * mass.rate ^ birth) (energyConstant * (1 / resistanceRate ^ birth))
    (mul_nonneg normPositive.le (pow_pos mass.rate_positive birth).le)
    (mul_nonneg energyPositive.le (one_div_pos.mpr (pow_pos ratePositive birth)).le)
    (by simpa only [Nat.add_zero, pow_zero, div_one, one_mul] using bounds 0)
    agreement target representative representativeImage
end
end EIGS

#print axioms EIGS.xiClosedFiniteBorn_evaluation_eq_continuous
#print axioms EIGS.exists_xiClosedFiniteBorn_point_evaluation_with_continuous_agreement