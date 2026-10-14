import RequestProject.Section31.EIGSStrictKernelLocalStayOfRules
import RequestProject.Section31.EIGSSameClosedSemigroupLiftCompact
import RequestProject.Section31.ContinuousKernelStayLowerBound
import RequestProject.Section31.EIGSAddressSupport

/-! An actual all-point inverse-ball-mass diagonal lower estimate for the
same strict jointly continuous kernel. Native stay expectations, compact
half lifts, positive ball mass and continuous-lift identification are all
filled internally. No exit, volume, stay or compactness target hypothesis
is retained in the original-rule existential theorem.
Candidate source: no compilation is claimed. -/

namespace EIGS
open MeasureTheory Filter Topology IGS.Sec31
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 7000000
variable {K : ℕ}

def XiContinuousKernelLocalStayLowerProperties (system : EIGSData K)
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
          ∃ fraction : ℝ, 0 < fraction ∧ ∃ count : ℕ,
          ∀ (coarse : ℕ) (time : {time : ℝ≥0 // 0 < time}),
          (time.val : ℝ) ≤ (2 * fraction) *
            (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
              system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse →
          let radius := (count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
            (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse)
          ∀ point : parameters.LimitSpace,
          (9 / 16 : ℝ) /
            (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
              (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass).real
              (Metric.closedBall point (4 * radius)) ≤ kernel time point point

theorem xiContinuousKernelLocalStayLowerProperties_of_shared_semigroup (system : EIGSData K)
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
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (strictProperties : XiStrictPositiveJointContinuousHeatKernelDensityProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair)
    (stayProperties : XiContinuousSemigroupLocalStayProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive) :
    XiContinuousKernelLocalStayLowerProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
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
  dsimp only [XiStrictPositiveJointContinuousHeatKernelDensityProperties,
    XiContinuousSemigroupLocalStayProperties, XiContinuousKernelLocalStayLowerProperties]
    at strictProperties stayProperties ⊢
  obtain ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous,
    intertwining, timeThreshold, timeThresholdPositive, upperConstant, upperConstantPositive,
    kernel, jointContinuous, kernelProperties⟩ := strictProperties
  obtain ⟨stayDense, staySemigroup, stayCompatibility, fraction, fractionPositive, count, stay⟩ := stayProperties
  have denseEquality : stayDense = originalDense := Subsingleton.elim _ _
  subst stayDense
  let embedding := xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  have embeddingInjective : Function.Injective embedding := xiContinuousL2Map_injective system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair mass
  have semigroupEquality : staySemigroup = semigroup := by
    funext time
    apply ContinuousLinearMap.ext
    intro function
    apply embeddingInjective
    exact (stayCompatibility time function).trans (intertwining time function).symm
  subst staySemigroup
  refine ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous,
    intertwining, timeThreshold, timeThresholdPositive, upperConstant, upperConstantPositive,
    kernel, jointContinuous, kernelProperties, fraction, fractionPositive, count, ?_⟩
  intro coarse time timeBound radius point
  let law := xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  have radiusPositive : 0 < radius := by
    have ruleRadiusNonnegative := xiRuleRadius_nonnegative system
      (fun colour => (parameters.lengthsPositive colour).le)
    have distanceRatePositive := zero_lt_one.trans distanceGreaterThanOne
    dsimp only [radius]
    positivity
  have timePositive : 0 < time.val := time.property
  let halfTime : {time : ℝ≥0 // 0 < time} := ⟨time.val / 2, by positivity⟩
  obtain ⟨_, _, _, _, _, fullLift, fullRepresentation, fullCompatibility⟩ := kernelProperties time
  obtain ⟨_, _, _, _, _, halfLift, _, halfCompatibility⟩ := kernelProperties halfTime
  have compactProperties := xiSameClosedSemigroupLiftCompactProperties_of_rules
    system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  dsimp only [XiSameClosedSemigroupLiftCompactProperties] at compactProperties
  have halfCompact := compactProperties originalDense semigroup semigroupNorm semigroupZero semigroupAdd
    semigroupContinuous intertwining halfTime.val halfTime.property halfLift halfCompatibility
  have embeddingAE (function : C(parameters.LimitSpace, ℝ)) :
      (embedding function : parameters.LimitSpace → ℝ) =ᵐ[law] function := by
    exact ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) law function
  have outerRadiusPositive : 0 < 4 * radius := by positivity
  have ballPositive : 0 < law (Metric.closedBall point (4 * radius)) :=
    (xiLimitMeasure_ball_positive system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
      point outerRadiusPositive).trans_le (measure_mono Metric.ball_subset_closedBall)
  have realBallPositive : 0 < law.real (Metric.closedBall point (4 * radius)) :=
    ENNReal.toReal_pos ballPositive.ne' (measure_ne_top law _)
  have halfBound : (halfTime.val : ℝ) ≤ fraction *
      (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse := by
    change (time.val : ℝ) / 2 ≤ _
    nlinarith [timeBound]
  have expectation := stay coarse halfTime.val halfBound point
  have diagonal := continuousKernel_diagonal_lower_of_local_test law originalDomain originalForm nonnegative
    closable originalDense embedding embeddingInjective embeddingAE time.val halfLift fullLift halfCompact
    halfCompatibility fullCompatibility (semigroup (time.val / 2)) (intertwining (time.val / 2))
    (kernel time) (jointContinuous.comp (continuous_const.prodMk continuous_id)) fullRepresentation
    point (continuousMetricBallCutoff point (2 * radius)) (Metric.closedBall point (4 * radius))
    isClosed_closedBall.measurableSet realBallPositive
    (fun other => continuousMetricBallCutoff_bounds point other (2 * radius))
    (fun other outside => by
      apply continuousMetricBallCutoff_eq_zero_outside point other (2 * radius) (by positivity)
      convert outside using 1 <;> congr 1 <;> ring)
    (3 / 4) (by norm_num) expectation
  norm_num at diagonal
  exact diagonal

theorem exists_xiContinuousKernelLocalStayLower_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
      ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (𝓝 (normalization • resistanceVector)) ∧
      XiContinuousKernelLocalStayLowerProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, strictProperties, stayProperties⟩ :=
    exists_xiStrictKernelLocalStay_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiContinuousKernelLocalStayLowerProperties_of_shared_semigroup system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair normalization normalizationPositive strictProperties stayProperties

end
end EIGS

#print axioms EIGS.xiContinuousKernelLocalStayLowerProperties_of_shared_semigroup
#print axioms EIGS.exists_xiContinuousKernelLocalStayLower_of_rules
