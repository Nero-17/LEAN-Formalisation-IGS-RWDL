import RequestProject.Section31.EIGSPointEvaluation
import RequestProject.Section31.EIGSL2QuadraticEnergy
import RequestProject.Section31.QuadraticEnergyPositiveEvaluation

/-! Actual finite-level point evaluation is continuous in the energy-plus-L2
norm. This does not assign continuous representatives to arbitrary closed-domain
elements. -/

namespace EIGS

open MeasureTheory Filter Topology IGS.Sec31
open scoped BoundedContinuousFunction

set_option maxHeartbeats 3000000

variable {K : ℕ} (system : EIGSData K)
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

include rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance

theorem exists_xiPoint_energy_functional (level : ℕ) (vertex : XiVtx system level) :
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    ∃ functional : QuadraticEnergySpace originalDomain originalForm nonnegative →L[ℝ] ℝ,
      ∀ values, functional values =
        ((xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
          metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).symm values.value).val
            (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex) := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let evaluation : QuadraticEnergySpace originalDomain originalForm nonnegative →ₗ[ℝ] ℝ :=
    (ContinuousMap.evalCLM (R := ℝ) (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex)).toLinearMap.comp
      ((xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive).subtype.comp
        ((xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
          metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).symm.toLinearMap.comp
            (QuadraticEnergySpace.linearEquivDomain originalDomain originalForm nonnegative).toLinearMap))
  obtain ⟨tailConstant, tailPositive, pointConstant, pointPositive, pointBound⟩ :=
    exists_xiContinuous_point_energy_bound system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let normCoefficient := 2 * mass.rate ^ level /
    (pointConstant * (xiVertexIncidenceCount system level vertex : ℝ))
  let energyCoefficient := (2 * tailConstant ^ 2 / pointConstant) *
    (1 / ((xiVertexIncidenceCount system level vertex : ℝ) * resistanceRate ^ level))
  have massPositive := mass.rate_positive
  have normCoefficientNonnegative : 0 ≤ normCoefficient := by dsimp only [normCoefficient]; positivity
  have energyCoefficientNonnegative : 0 ≤ energyCoefficient := by dsimp only [energyCoefficient]; positivity
  have bound : ∀ values, ‖evaluation values‖ ≤ Real.sqrt (normCoefficient + energyCoefficient) * ‖values‖ := by
    intro values
    let representative := (xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).symm values.value
    have finite := (xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive _).1
      representative.property
    have pointControl := pointBound representative.val finite level vertex
    have sameClass := congrArg Subtype.val
      ((xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).apply_symm_apply values.value)
    have sameEnergy := xiContinuousLpEnergyQuadraticForm_of_continuous system rulesConnected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair representative
    rw [LinearEquiv.apply_symm_apply] at sameEnergy
    have sameNorm : ‖(xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass).embed (BoundedContinuousFunction.mkOfCompact representative.val)‖ =
        ‖(values.value : _)‖ := congrArg norm sameClass
    have squareBound : (evaluation values) ^ 2 ≤
        normCoefficient * ‖(values.value : _)‖ ^ 2 + energyCoefficient * originalForm values.value := by
      rw [sameNorm, ← sameEnergy] at pointControl
      exact pointControl
    have identity := QuadraticEnergySpace.norm_sq originalDomain originalForm nonnegative values
    change ‖values‖ ^ 2 = originalForm values.value + ‖values.value‖ ^ 2 at identity
    have energyBound := mul_nonneg normCoefficientNonnegative (nonnegative values.value)
    change 0 ≤ normCoefficient * originalForm values.value at energyBound
    have normBound := mul_nonneg energyCoefficientNonnegative (sq_nonneg ‖(values.value : _)‖)
    have sqrtIdentity := Real.sq_sqrt (add_nonneg normCoefficientNonnegative energyCoefficientNonnegative)
    have sqrtNonnegative := Real.sqrt_nonneg (normCoefficient + energyCoefficient)
    rw [Real.norm_eq_abs]
    have combinedBound : (evaluation values) ^ 2 ≤ (normCoefficient + energyCoefficient) * ‖values‖ ^ 2 := by
      rw [identity]
      nlinarith only [squareBound, energyBound, normBound]
    have rightSquare : (Real.sqrt (normCoefficient + energyCoefficient) * ‖values‖) ^ 2 =
        (normCoefficient + energyCoefficient) * ‖values‖ ^ 2 := by rw [mul_pow, sqrtIdentity]
    rw [← rightSquare] at combinedBound
    exact (sq_le_sq₀ (abs_nonneg (evaluation values))
      (mul_nonneg sqrtNonnegative (norm_nonneg values))).1 (by simpa only [sq_abs] using combinedBound)
  exact ⟨evaluation.mkContinuous (Real.sqrt (normCoefficient + energyCoefficient)) bound, fun _ => rfl⟩

end EIGS

#print axioms EIGS.exists_xiPoint_energy_functional

