import RequestProject.Section31.EIGSFiniteBornPointEnergyBound
import RequestProject.Section31.QuadraticEnergyFunctionalExtension
import RequestProject.Section31.EIGSL2ClosabilityWithoutPrimitive

/-! Actual finite-born core evaluations extend to the same closed energy
domain, and the degree-corrected bounds hold for this single extension at
every scale. Agreement with arbitrary continuous closed representatives is
not an input or a conclusion of this module. -/

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped BigOperators Classical BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem exists_xiClosedFiniteBorn_point_evaluation (system : EIGSData K)
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
        ∀ age (target : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative),
          evaluation target ^ 2 ≤
            normConstant * (mass.rate ^ (birth + age) /
              finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age) * ‖target.val‖ ^ 2 +
            energyConstant * (1 / (finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age *
              resistanceRate ^ (birth + age))) *
                QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable target := by
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
  have massPositive := mass.rate_positive
  dsimp only
  intro birth vertex
  obtain ⟨normConstant, energyConstant, normPositive, energyPositive, pointBound⟩ :=
    exists_xiFiniteBorn_point_energy_bound system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector
      vectorPositive renormalizationEigenpair primitiveDegree birth vertex
  let finiteDomain := xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive
  let energyEquiv := xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let evaluation : originalDomain →ₗ[ℝ] ℝ :=
    (ContinuousMap.evalCLM (R := ℝ) (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair birth vertex)).toLinearMap.comp
        (finiteDomain.subtype.comp energyEquiv.symm.toLinearMap)
  have originalBounds : ∀ age (values : originalDomain),
      evaluation values ^ 2 ≤
        (normConstant * (mass.rate ^ (birth + age) /
          finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age)) * ‖values.val‖ ^ 2 +
        (energyConstant * (1 / (finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age *
          resistanceRate ^ (birth + age)))) * originalForm values := by
    intro age values
    let representative := energyEquiv.symm values
    have representativeFinite : xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (representative.val ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) ≠ ⊤ :=
      (xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive _).1 representative.property
    have representativeImage : core.embed (BoundedContinuousFunction.mkOfCompact representative.val) = values.val :=
      congrArg Subtype.val (energyEquiv.apply_symm_apply values)
    have representativeEnergy :
        (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
          (representative.val ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal = originalForm values := by
      symm
      simpa only [representative, energyEquiv, originalForm, LinearEquiv.apply_symm_apply] using
        xiContinuousLpEnergyQuadraticForm_of_continuous system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
          renormalizationEigenpair representative
    have bound := pointBound age representative.val representativeFinite
    rw [representativeImage, representativeEnergy] at bound
    exact bound
  have baseBound := originalBounds 0
  have baseNormNonnegative : 0 ≤ normConstant * (mass.rate ^ birth) := by positivity
  have baseEnergyNonnegative : 0 ≤ energyConstant * (1 / resistanceRate ^ birth) := by positivity
  obtain ⟨extension, extensionAgreement, extensionBounds⟩ :=
    QuadraticEnergySpace.exists_closed_energy_functional originalDomain originalForm nonnegative closable evaluation
      (normConstant * mass.rate ^ birth) (energyConstant * (1 / resistanceRate ^ birth))
      baseNormNonnegative baseEnergyNonnegative (by simpa only [Nat.add_zero, pow_zero, div_one, one_mul] using baseBound)
  refine ⟨normConstant, energyConstant, normPositive, energyPositive, extension, extensionAgreement, ?_⟩
  intro age target
  exact extensionBounds
    (normConstant * (mass.rate ^ (birth + age) / finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age))
    (energyConstant * (1 / (finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age * resistanceRate ^ (birth + age))))
    (originalBounds age) target

end
end EIGS

#print axioms EIGS.exists_xiClosedFiniteBorn_point_evaluation
