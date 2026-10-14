import RequestProject.Section31.EIGSTypicalLogarithmicHeatKernelOfRules
import RequestProject.Section31.LogarithmicHeatLowerCommonAE

/-! The same actual kernel has its precise logarithmic lower estimate on
one physical full-measure set for every positive epsilon. The countable
cofinal strengthening is performed explicitly, retaining all strict-kernel
and global-upper fields. Original rules and the standing primitive-degree
condition are the only final mathematical assumptions. Candidate source:
no compilation is claimed. -/

namespace EIGS
open MeasureTheory Filter Topology IGS.Sec31
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 7000000
variable {K : ℕ}

def XiTypicalLogarithmicHeatKernelCommonAEProperties (system : EIGSData K)
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
          ∀ᵐ point ∂xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass,
          ∀ epsilon : ℝ, 0 < epsilon →
          ∃ lowerConstant : ℝ, 0 < lowerConstant ∧ ∃ timeThreshold : ℝ, 0 < timeThreshold ∧
          ∀ time : {time : ℝ≥0 // 0 < time}, (time.val : ℝ) ≤ timeThreshold →
          lowerConstant * (time.val : ℝ) ^ (-(Real.log mass.rate / Real.log (mass.rate * resistanceRate))) *
            |Real.log (time.val : ℝ)| ^
              (-(1 / (Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) - 1) + epsilon)) ≤
          kernel time point point

theorem xiTypicalLogarithmicHeatKernelCommonAEProperties_of_typical (system : EIGSData K)
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
    XiTypicalLogarithmicHeatKernelCommonAEProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
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
  dsimp only [XiTypicalLogarithmicHeatKernelProperties, XiTypicalLogarithmicHeatKernelCommonAEProperties]
    at typicalProperties ⊢
  obtain ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous,
    intertwining, timeThreshold, timeThresholdPositive, upperConstant, upperConstantPositive,
    kernel, jointContinuous, kernelProperties, lowerFamily⟩ := typicalProperties
  refine ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous,
    intertwining, timeThreshold, timeThresholdPositive, upperConstant, upperConstantPositive,
    kernel, jointContinuous, kernelProperties, ?_⟩
  exact logarithmic_heat_lower_common_ae
    (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
    (fun time point => kernel time point point)
    (Real.log mass.rate / Real.log (mass.rate * resistanceRate))
    (1 / (Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) - 1)) lowerFamily

theorem exists_xiTypicalLogarithmicHeatKernelCommonAE_of_rules (system : EIGSData K)
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
      XiTypicalLogarithmicHeatKernelCommonAEProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, typicalProperties⟩ :=
    exists_xiTypicalLogarithmicHeatKernel_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive primitiveDegree
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiTypicalLogarithmicHeatKernelCommonAEProperties_of_typical system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair typicalProperties

end
end EIGS

#print axioms EIGS.xiTypicalLogarithmicHeatKernelCommonAEProperties_of_typical
#print axioms EIGS.exists_xiTypicalLogarithmicHeatKernelCommonAE_of_rules
