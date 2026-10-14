import RequestProject.Section31.EIGSClosedFiniteBornPointEvaluation
import RequestProject.Section31.EIGSClosedContinuousDomain

/-! Every actual graph-bounded core evaluation agrees with any continuous
representative of a value in the same closed domain. The already proved
continuous closed-domain characterization puts this representative in the
original finite-energy core; its actual embedding and the core agreement
identify the evaluation without a second recovery argument.
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
  dsimp only
  intro birth vertex evaluation normConstant energyConstant normNonnegative energyNonnegative
    evaluationBound agreement target representative representativeImage
  have representativeFinite : representative ∈ xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive := by
    apply (xiContinuous_mem_closedDomain_iff system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair representative).mp
    rw [representativeImage]
    exact target.property
  let energyEquiv := xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let original : originalDomain := energyEquiv ⟨representative, representativeFinite⟩
  have originalImage : original.val = target.val := by
    change xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass representative = target.val
    exact representativeImage
  have closedOriginal : (⟨original.val,
      QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative original⟩ :
        QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative) = target :=
    Subtype.ext originalImage
  calc
    evaluation target = evaluation ⟨original.val,
        QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative original⟩ :=
      congrArg evaluation closedOriginal.symm
    _ = (energyEquiv.symm original).val (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair birth vertex) := agreement original
    _ = _ := by simp only [original, LinearEquiv.symm_apply_apply]

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