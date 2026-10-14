import RequestProject.Section31.EIGSClosedEvaluationContinuousRepresentative
import RequestProject.Section31.QuadraticEnergyRieszDiagonal
import RequestProject.Section2PrimitiveIntegerGrowth
import RequestProject.Section2DegreeMassGap
import RequestProject.Section31.EIGSAnalyticTimeScale

/-! A finite-born diagonal upper estimate from the actual rules. Both the
closed point evaluation and agreement with continuous representatives are
constructed internally. The logarithmic degree correction uses the actual
primitive matrix and its proved strict mass gap. Compatible half-time lifts
are quantified operators, not assumed heat-kernel estimates. -/

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped BigOperators Classical BoundedContinuousFunction NNReal
noncomputable section
set_option maxHeartbeats 6000000
variable {K : ℕ}

theorem exists_xiFiniteBorn_riesz_diagonal_upper (system : EIGSData K)
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
    ∀ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected
      lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass))),
    ∀ (birth : ℕ) (vertex : XiVtx system birth),
      ∃ upperConstant : ℝ, 0 < upperConstant ∧
        ∀ (time : ℝ≥0), 0 < time → (time : ℝ) ≤ 1 →
        ∀ smoothing : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass) →L[ℝ]
            C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ),
          (∀ forcing, xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass (smoothing forcing) =
              QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable
                originalDense (time / 2) forcing) →
          ‖continuousOperatorKernelRow smoothing (xiCompletionEmbedding system rulesConnected lengths lengthsPositive
            distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair birth vertex)‖ ^ 2 ≤
              upperConstant / (time : ℝ) ^ ((Real.log mass.rate -
                Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system))) /
                  Real.log (mass.rate * resistanceRate)) := by
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
  intro originalDense birth vertex
  have massPositive := mass.rate_positive
  obtain ⟨normConstant, energyConstant, normPositive, energyPositive, evaluation, _, bounds, agreement⟩ :=
    exists_xiClosedFiniteBorn_point_evaluation_with_continuous_agreement system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair primitiveDegree birth vertex
  have degreePositive : 0 < finiteRealMatrixSpectralRadius (degreeMatrix system) :=
    zero_lt_one.trans (degree_spectralRadius_gt_one_of_primitive system primitiveDegree)
  have degreeMass : finiteRealMatrixSpectralRadius (degreeMatrix system) < mass.rate := by
    rw [XiMassParameters.rate_eq_spectralRadius system mass]
    exact degree_spectralRadius_lt_mass_of_primitive system rulesConnected rulesLoopless
      plantingNonadjacent distancePositive primitiveDegree
  have timeRateGreaterThanOne : 1 < mass.rate * resistanceRate :=
    xiAnalyticTimeRate_gt_one system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive mass resistanceRate ratePositive resistanceVector vectorPositive (by
        funext colour
        exact renormalizationEigenpair colour)
  refine ⟨(normConstant * mass.rate ^ birth + energyConstant / resistanceRate ^ birth) *
    (mass.rate / finiteRealMatrixSpectralRadius (degreeMatrix system)), by positivity, ?_⟩
  intro time timePositive timeAtMostOne smoothing compatibility
  have recurrence := QuadraticEnergySpace.closedSemigroup_riesz_diagonal_recurrence
    originalDomain originalForm nonnegative closable originalDense
    (xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass) evaluation
    (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair birth vertex)
    agreement
    (fun age => normConstant * (mass.rate ^ (birth + age) /
      finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age))
    (fun age => energyConstant * (1 / (finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age *
      resistanceRate ^ (birth + age))))
    (fun _ => by positivity) (fun _ => by positivity) bounds time timePositive smoothing compatibility
  apply degree_corrected_diagonal_heat_upper mass.rate
    (finiteRealMatrixSpectralRadius (degreeMatrix system)) resistanceRate normConstant energyConstant
    (time : ℝ)
    (‖continuousOperatorKernelRow smoothing (xiCompletionEmbedding system rulesConnected lengths lengthsPositive
      distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair birth vertex)‖ ^ 2)
    mass.rate_positive degreePositive ratePositive degreeMass.le timeRateGreaterThanOne
    normPositive.le energyPositive.le birth timePositive timeAtMostOne (sq_nonneg _)
  intro age
  simpa only [mul_one_div, div_div, mul_assoc] using recurrence age

end
end EIGS

#print axioms EIGS.exists_xiFiniteBorn_riesz_diagonal_upper
