import RequestProject.Section31.EIGSTypicalLogarithmicHeatKernelOfRules
import RequestProject.Section3.SpectralDimension

/-! The physical almost-everywhere spectral dimension for the same actual
strict jointly continuous heat kernel. Only epsilon equal to one is used
from the typical logarithmic lower family. The conservative global upper
bound is restricted to a small time interval before the analytic squeeze.
The final assumptions are the original rules and the standing primitive
degree condition; no lower estimate or spectral limit is assumed by the
actual existence theorem. Candidate source: compilation is not claimed. -/

namespace IGS.Sec31
open Filter Topology
open scoped NNReal

theorem tendsto_spectral_dimension_of_positive_kernel_bounds
    (diagonal : {time : ℝ≥0 // 0 < time} → ℝ)
    (exponent logExponent lowerConstant upperConstant localThreshold upperThreshold : ℝ)
    (lowerConstantPositive : 0 < lowerConstant) (upperConstantPositive : 0 < upperConstant)
    (localThresholdPositive : 0 < localThreshold) (upperThresholdPositive : 0 < upperThreshold)
    (lowerBound : ∀ time : {time : ℝ≥0 // 0 < time}, (time.val : ℝ) ≤ localThreshold →
      lowerConstant * (time.val : ℝ) ^ (-exponent) *
        |Real.log (time.val : ℝ)| ^ (-logExponent) ≤ diagonal time)
    (upperBound : ∀ time : {time : ℝ≥0 // 0 < time},
      diagonal time ≤ upperConstant / (min ((time.val : ℝ) / 2) upperThreshold) ^ exponent) :
    Tendsto (fun time : ℝ => -2 * Real.log
      (if positive : 0 < time then diagonal ⟨⟨time, positive.le⟩, positive⟩ else 0) / Real.log time)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * exponent)) := by
  apply IGS.tendsto_spectral_dimension_of_bounds _ exponent logExponent lowerConstant
    (upperConstant * (2 : ℝ) ^ exponent) (min localThreshold (2 * upperThreshold))
    lowerConstantPositive (mul_pos upperConstantPositive (Real.rpow_pos_of_pos (by norm_num) _))
    (lt_min localThresholdPositive (mul_pos (by norm_num) upperThresholdPositive))
  · intro time inRange
    have bound := lowerBound ⟨⟨time, inRange.1.le⟩, inRange.1⟩
      (inRange.2.le.trans (min_le_left _ _))
    simp only [dif_pos inRange.1]
    convert bound using 1 <;> ring
  · intro time inRange
    have small : time / 2 ≤ upperThreshold := by
      have := inRange.2.le.trans (min_le_right localThreshold (2 * upperThreshold))
      linarith
    have bound := upperBound ⟨⟨time, inRange.1.le⟩, inRange.1⟩
    change (if positive : 0 < time then diagonal ⟨⟨time, positive.le⟩, positive⟩ else 0) ≤
      (upperConstant * (2 : ℝ) ^ exponent) * time ^ (-exponent)
    rw [dif_pos inRange.1]
    change diagonal ⟨⟨time, inRange.1.le⟩, inRange.1⟩ ≤
      upperConstant * (2 : ℝ) ^ exponent * time ^ (-exponent)
    change diagonal ⟨⟨time, inRange.1.le⟩, inRange.1⟩ ≤
      upperConstant / (min (time / 2) upperThreshold) ^ exponent at bound
    rw [min_eq_left small] at bound
    calc
      diagonal ⟨⟨time, inRange.1.le⟩, inRange.1⟩ ≤ upperConstant / (time / 2) ^ exponent := bound
      _ = upperConstant * (2 : ℝ) ^ exponent * time ^ (-exponent) := by
        rw [Real.div_rpow inRange.1.le (by norm_num), div_div_eq_mul_div, Real.rpow_neg inRange.1.le]
        ring

end IGS.Sec31

namespace EIGS
open MeasureTheory Filter Topology IGS.Sec31
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 7000000
variable {K : ℕ}

def XiTypicalHeatSpectralDimensionProperties (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour) : Prop :=
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass))),
    ∃ semigroup : ℝ≥0 → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ),
      (∀ time, ‖semigroup time‖ ≤ 1) ∧
      semigroup 0 = ContinuousLinearMap.id ℝ C(parameters.LimitSpace, ℝ) ∧
      (∀ firstTime secondTime, semigroup (firstTime + secondTime) =
        (semigroup firstTime).comp (semigroup secondTime)) ∧
      Continuous (fun point : C(parameters.LimitSpace, ℝ) × ℝ≥0 => semigroup point.2 point.1) ∧
      (∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
        xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
          (semigroup time function) =
        QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time
          (xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass function)) ∧
      ∃ timeThreshold : ℝ, 0 < timeThreshold ∧ ∃ upperConstant : ℝ, 0 < upperConstant ∧
        ∃ kernel : {time : ℝ≥0 // 0 < time} → parameters.LimitSpace → parameters.LimitSpace → ℝ,
          Continuous (fun point : {time : ℝ≥0 // 0 < time} × parameters.LimitSpace × parameters.LimitSpace =>
            kernel point.1 point.2.1 point.2.2) ∧
          (∀ time : {time : ℝ≥0 // 0 < time},
            (∀ first second, kernel time first second = kernel time second first) ∧
            (∀ first second, 0 < kernel time first second) ∧
            (∀ first second, kernel time first second ≤ upperConstant / (min ((time.val : ℝ) / 2) timeThreshold) ^
              (Real.log mass.rate / Real.log (mass.rate * resistanceRate))) ∧
            (∀ point, (∫ other, kernel time point other ∂xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
              (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass) = 1) ∧
            (∀ (function : C(parameters.LimitSpace, ℝ)) point,
              semigroup time.val function point = ∫ other, kernel time point other * function other
                ∂xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
                  (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass) ∧
            ∃ lifted : Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
                (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass) →L[ℝ]
                C(parameters.LimitSpace, ℝ),
              (∀ forcing point, lifted forcing point = ∫ other, kernel time point other * forcing other
                ∂xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
                  (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass) ∧
              ∀ forcing,
                xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
                  (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
                  (lifted forcing) =
                QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time.val forcing) ∧
          (∀ epsilon : ℝ, 0 < epsilon →
          ∀ᵐ point ∂xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass,
          ∃ lowerConstant : ℝ, 0 < lowerConstant ∧ ∃ timeThreshold : ℝ, 0 < timeThreshold ∧
          ∀ time : {time : ℝ≥0 // 0 < time}, (time.val : ℝ) ≤ timeThreshold →
          lowerConstant * (time.val : ℝ) ^ (-(Real.log mass.rate / Real.log (mass.rate * resistanceRate))) *
            |Real.log (time.val : ℝ)| ^
              (-(1 / (Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) - 1) + epsilon)) ≤
          kernel time point point) ∧
          ∀ᵐ point ∂xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass,
          Tendsto (fun time : ℝ => -2 * Real.log
            (if positive : 0 < time then kernel ⟨⟨time, positive.le⟩, positive⟩ point point else 0) /
              Real.log time) (𝓝[>] (0 : ℝ))
            (𝓝 (2 * (Real.log mass.rate / Real.log (mass.rate * resistanceRate))))

theorem xiTypicalHeatSpectralDimensionProperties_of_typical (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (typicalProperties : XiTypicalLogarithmicHeatKernelProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair) :
    XiTypicalHeatSpectralDimensionProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  dsimp only [XiTypicalLogarithmicHeatKernelProperties, XiTypicalHeatSpectralDimensionProperties]
    at typicalProperties ⊢
  obtain ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous,
    intertwining, timeThreshold, timeThresholdPositive, upperConstant, upperConstantPositive,
    kernel, jointContinuous, kernelProperties, lowerFamily⟩ := typicalProperties
  refine ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous,
    intertwining, timeThreshold, timeThresholdPositive, upperConstant, upperConstantPositive,
    kernel, jointContinuous, kernelProperties, lowerFamily, ?_⟩
  filter_upwards [lowerFamily 1 (by norm_num)] with point lower
  obtain ⟨lowerConstant, lowerConstantPositive, localThreshold, localThresholdPositive, lowerBound⟩ := lower
  exact IGS.Sec31.tendsto_spectral_dimension_of_positive_kernel_bounds
    (fun time => kernel time point point)
    (Real.log mass.rate / Real.log (mass.rate * resistanceRate))
    (1 / (Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) - 1) + 1)
    lowerConstant upperConstant localThreshold timeThreshold
    lowerConstantPositive upperConstantPositive localThresholdPositive timeThresholdPositive
    lowerBound (fun time => (kernelProperties time).2.2.1 point point)

theorem exists_xiTypicalHeatSpectralDimension_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (primitiveDegree : (degreeMatrix system).IsPrimitive) :
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
      ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (𝓝 (normalization • resistanceVector)) ∧
      XiTypicalHeatSpectralDimensionProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, typicalProperties⟩ :=
    exists_xiTypicalLogarithmicHeatKernel_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive primitiveDegree
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiTypicalHeatSpectralDimensionProperties_of_typical system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair typicalProperties

end
end EIGS

#print axioms IGS.Sec31.tendsto_spectral_dimension_of_positive_kernel_bounds
#print axioms EIGS.xiTypicalHeatSpectralDimensionProperties_of_typical
#print axioms EIGS.exists_xiTypicalHeatSpectralDimension_of_rules
