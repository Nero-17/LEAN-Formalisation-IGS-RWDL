import RequestProject.Section31.EIGSContinuousSemigroupCompactSmoothingOfRules
import RequestProject.Section31.EIGSConservativeMarkovSemigroup
import RequestProject.Section31.ContinuousKernelDensity

/-! A continuous symmetric nonnegative density for the same actual semigroup,
constructed from compact half-time Riesz rows. It represents arbitrary L²
inputs through the actual continuous lift, has mass one, and has the small-time
upper bound with the actual logarithmic exponent. Strict positivity is not
asserted here. No kernel density or compactness premise is assumed. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped BoundedContinuousFunction NNReal
noncomputable section
set_option maxHeartbeats 6000000
variable {K : ℕ}

def XiContinuousHeatKernelDensityProperties (system : EIGSData K)
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
        ∀ time : ℝ≥0, 0 < time → (time : ℝ) ≤ timeThreshold →
          ∃ kernel : parameters.LimitSpace → parameters.LimitSpace → ℝ,
            Continuous (fun points : parameters.LimitSpace × parameters.LimitSpace => kernel points.1 points.2) ∧
            (∀ first second, kernel first second = kernel second first) ∧
            (∀ first second, 0 ≤ kernel first second) ∧
            (∀ first second, kernel first second ≤ upperConstant / ((time : ℝ) / 2) ^
              (Real.log mass.rate / Real.log (mass.rate * resistanceRate))) ∧
            (∀ point, (∫ other, kernel point other ∂xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
              (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass) = 1) ∧
            (∀ (function : C(parameters.LimitSpace, ℝ)) point,
              semigroup time function point = ∫ other, kernel point other * function other
                ∂xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
                  (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass) ∧
            ∃ lifted : Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
                (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass) →L[ℝ]
                C(parameters.LimitSpace, ℝ),
              (∀ forcing point, lifted forcing point = ∫ other, kernel point other * forcing other
                ∂xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
                  (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass) ∧
              ∀ forcing,
                xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
                  (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
                  (lifted forcing) =
                QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time forcing

theorem xiContinuousHeatKernelDensityProperties_of_compactSmoothing (system : EIGSData K)
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
    (compactSmoothingProperties : XiContinuousSemigroupCompactSmoothingProperties system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair) :
    XiContinuousHeatKernelDensityProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
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
  dsimp only [XiContinuousSemigroupCompactSmoothingProperties, XiContinuousHeatKernelDensityProperties]
    at compactSmoothingProperties ⊢
  obtain ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd,
    semigroupContinuous, intertwining, timeThreshold, timeThresholdPositive, upperConstant,
    upperConstantPositive, smoothing⟩ := compactSmoothingProperties
  let measure := xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  let embedding := xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  have embeddingInjective : Function.Injective embedding := xiContinuousL2Map_injective system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair mass
  have embeddingAE (function : C(parameters.LimitSpace, ℝ)) :
      (embedding function : parameters.LimitSpace → ℝ) =ᵐ[measure] function := by
    exact ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) measure function
  have markovProperties := xiConservativeMarkovSemigroupProperties_of_dense_core system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair originalDense
  dsimp only [XiConservativeMarkovSemigroupProperties] at markovProperties
  obtain ⟨markovDense, closedMarkov, closedConstants, _, _, _, _⟩ := markovProperties
  have densityEquality : markovDense = originalDense := Subsingleton.elim _ _
  subst markovDense
  have embeddingConstant : embedding (ContinuousMap.const parameters.LimitSpace (1 : ℝ)) =
      (xiContinuousLpEnergyConstant system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive 1 : Lp ℝ 2 measure) := by
    apply Lp.ext
    exact (embeddingAE (ContinuousMap.const parameters.LimitSpace (1 : ℝ))).trans
      (xiContinuousLpEnergyConstant_ae system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive 1).symm
  have preservesOne (time : ℝ≥0) : semigroup time 1 = 1 := by
    have constantEquality : semigroup time (ContinuousMap.const parameters.LimitSpace (1 : ℝ)) =
        ContinuousMap.const parameters.LimitSpace (1 : ℝ) := by
      apply embeddingInjective
      rw [intertwining, embeddingConstant, closedConstants, ← embeddingConstant]
    simpa using constantEquality
  refine ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd,
    semigroupContinuous, intertwining, timeThreshold, timeThresholdPositive,
    upperConstant, upperConstantPositive, ?_⟩
  intro time timePositive timeAtMost
  let halfTime : ℝ≥0 := time / 2
  have halfTimePositive : 0 < halfTime := div_pos timePositive (by norm_num)
  have halfTimeAtMost : (halfTime : ℝ) ≤ timeThreshold := by
    have halfAtMost : halfTime ≤ time := div_le_self time.coe_nonneg (by norm_num)
    exact (show (halfTime : ℝ) ≤ (time : ℝ) from halfAtMost).trans timeAtMost
  obtain ⟨halfLifted, halfNorm, halfCompact, _, halfCompatibility⟩ :=
    smoothing halfTime halfTimePositive halfTimeAtMost
  let halfOperator := QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense halfTime
  let lifted := halfLifted.comp halfOperator
  let kernel := continuousOperatorComposedKernel measure halfLifted
  have halfAdd : halfTime + halfTime = time := add_halves time
  have liftedCompatibility (forcing : Lp ℝ 2 measure) : embedding (lifted forcing) =
      QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time forcing := by
    change embedding (halfLifted (halfOperator forcing)) = _
    rw [halfCompatibility]
    change (halfOperator.comp halfOperator) forcing = _
    rw [← QuadraticEnergySpace.closedSemigroup_add, halfAdd]
  have liftedAgreement (function : C(parameters.LimitSpace, ℝ)) :
      lifted (embedding function) = semigroup time function := by
    apply embeddingInjective
    rw [liftedCompatibility, intertwining]
  have representation (forcing : Lp ℝ 2 measure) (point : parameters.LimitSpace) :
      lifted forcing point = ∫ other, kernel point other * forcing other ∂measure :=
    continuousOperatorComposedKernel_integral measure embedding embeddingAE halfLifted halfOperator
      (QuadraticEnergySpace.closedSemigroup_selfAdjoint originalDomain originalForm nonnegative closable originalDense halfTime)
      halfCompatibility point forcing
  have continuousRepresentation (function : C(parameters.LimitSpace, ℝ)) (point : parameters.LimitSpace) :
      semigroup time function point = ∫ other, kernel point other * function other ∂measure := by
    rw [← liftedAgreement, representation]
    apply integral_congr_ae
    filter_upwards [embeddingAE function] with other representative
    rw [representative]
  have liftedPositive (forcing : Lp ℝ 2 measure) (forcingNonnegative : ∀ᵐ point ∂measure, 0 ≤ forcing point) :
      ∀ point, 0 ≤ lifted forcing point := by
    have closedNonnegative := (closedMarkov time forcing).1 forcingNonnegative
    have embeddingNonnegative : ∀ᵐ point ∂measure, 0 ≤ embedding (lifted forcing) point := by
      rw [liftedCompatibility]
      exact closedNonnegative
    have continuousNonnegative : ∀ᵐ point ∂measure, 0 ≤ lifted forcing point := by
      filter_upwards [embeddingNonnegative, embeddingAE (lifted forcing)] with point nonnegative representative
      change 0 ≤ embedding (lifted forcing) point at nonnegative
      change embedding (lifted forcing) point = lifted forcing point at representative
      rw [representative] at nonnegative
      exact nonnegative
    exact continuous_nonnegative_of_ae_nonnegative measure (lifted forcing) continuousNonnegative
  have kernelContinuous : Continuous (fun points : parameters.LimitSpace × parameters.LimitSpace =>
      kernel points.1 points.2) := continuousOperatorComposedKernel_continuous measure halfLifted halfCompact
  have kernelNonnegative : ∀ first second, 0 ≤ kernel first second :=
    continuousKernel_nonnegative_of_positive_L2_representation measure kernel kernelContinuous lifted representation liftedPositive
  have kernelUpper (first second : parameters.LimitSpace) : kernel first second ≤
      upperConstant / ((time : ℝ) / 2) ^ (Real.log mass.rate / Real.log (mass.rate * resistanceRate)) := by
    have normSquared := pow_le_pow_left₀ (norm_nonneg halfLifted) halfNorm 2
    rw [Real.sq_sqrt (by positivity)] at normSquared
    have bound := (le_abs_self (kernel first second)).trans
      ((continuousOperatorComposedKernel_abs_le measure halfLifted first second).trans normSquared)
    simpa only [halfTime, NNReal.coe_div, NNReal.coe_ofNat] using bound
  have kernelMass (point : parameters.LimitSpace) : (∫ other, kernel point other ∂measure) = 1 := by
    have identity := continuousRepresentation 1 point
    rw [preservesOne] at identity
    simpa only [ContinuousMap.one_apply, mul_one] using identity.symm
  exact ⟨kernel, kernelContinuous, continuousOperatorComposedKernel_symmetric measure halfLifted,
    kernelNonnegative, kernelUpper, kernelMass, continuousRepresentation, lifted, representation, liftedCompatibility⟩

theorem exists_xiContinuousHeatKernelDensity_of_rules (system : EIGSData K)
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
      XiContinuousHeatKernelDensityProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, continuousProperties⟩ :=
    exists_xiContinuousSemigroupCompactSmoothing_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiContinuousHeatKernelDensityProperties_of_compactSmoothing system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair continuousProperties

end
end EIGS

#print axioms EIGS.xiContinuousHeatKernelDensityProperties_of_compactSmoothing
#print axioms EIGS.exists_xiContinuousHeatKernelDensity_of_rules