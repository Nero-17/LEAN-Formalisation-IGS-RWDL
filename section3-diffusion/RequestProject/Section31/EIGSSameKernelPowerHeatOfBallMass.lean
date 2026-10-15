import RequestProject.Section31.EIGSSameNativeJointFullHeatEstimatesOfRules
import RequestProject.Section31.GeometricInverseBallLowerOptimization
import RequestProject.Section31.ContinuousKernelPowerBoundsOfBallMass

/-! Pure-power bounds for every kernel of the original closed semigroup.
The same native discrete witness supplies local stay and the inverse-ball
lower bound internally. Only the actual geometric ball upper bound is
left for the bounded-degree rule consumer, which must supply it internally. -/
namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical NNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 12000000
variable {K : ℕ}
def XiSameKernelPowerHeatEstimatesProperties (system : EIGSData K)
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
    (normalization : ℝ) (normalizationPositive : 0 < normalization) : Prop :=
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
  ∀ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass))),
  ∀ semigroup : ℝ≥0 → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ),
    (∀ time, ‖semigroup time‖ ≤ 1) →
    semigroup 0 = ContinuousLinearMap.id ℝ C(parameters.LimitSpace, ℝ) →
    (∀ firstTime secondTime, semigroup (firstTime + secondTime) =
      (semigroup firstTime).comp (semigroup secondTime)) →
    Continuous (fun point : C(parameters.LimitSpace, ℝ) × ℝ≥0 => semigroup point.2 point.1) →
    (∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
      xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
        (semigroup time function) =
      QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time
        (xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass function)) →
    ∀ timeThreshold upperConstant : ℝ, 0 < timeThreshold → 0 < upperConstant →
    ∀ kernel : {time : ℝ≥0 // 0 < time} → parameters.LimitSpace → parameters.LimitSpace → ℝ,
      PositiveClosedKernelData
        (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
        (xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
        (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense)
        (Real.log mass.rate / Real.log (mass.rate * resistanceRate)) semigroup timeThreshold upperConstant kernel →
      ∃ cutoffTime lowerConstant upperPowerConstant : ℝ,
        0 < cutoffTime ∧ 0 < lowerConstant ∧ 0 < upperPowerConstant ∧
        ∀ time : {time : ℝ≥0 // 0 < time}, (time.val : ℝ) ≤ cutoffTime →
        ∀ point : parameters.LimitSpace,
          lowerConstant / (time.val : ℝ) ^ (Real.log mass.rate / Real.log (mass.rate * resistanceRate)) ≤
            kernel time point point ∧
          kernel time point point ≤ upperPowerConstant /
            (time.val : ℝ) ^ (Real.log mass.rate / Real.log (mass.rate * resistanceRate))
theorem xiSameKernelPowerHeatEstimatesProperties_of_discrete_and_volume (system : EIGSData K)
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
    (volumeUpper :
      let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
      let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
        (by norm_num : (1 : ℝ) < 2).trans_le
          (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
      let mass := xiMassParametersOfRules system rulesConnected distancePositive
      ∃ volumeConstant volumeRadius : ℝ, 0 < volumeConstant ∧ 0 < volumeRadius ∧
        ∀ point : parameters.LimitSpace, ∀ radius : ℝ, 0 < radius → radius ≤ volumeRadius →
          (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass).real
              (Metric.ball point radius) ≤ volumeConstant * radius ^
                (Real.log mass.rate / Real.log (system.distanceSpectralRadius rulesConnected)))
    (discreteProperties : XiNativeSupDiscreteConvergenceProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair normalization normalizationPositive) :
    XiSameKernelPowerHeatEstimatesProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive := by
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
  have stayProperties := xiContinuousSemigroupLocalStayProperties_of_discreteConvergence system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair normalization normalizationPositive discreteProperties
  dsimp only [XiSameKernelPowerHeatEstimatesProperties]
  intro originalDense semigroup semigroupNorm semigroupZero semigroupAdd semigroupContinuous intertwining
    timeThreshold upperConstant timeThresholdPositive upperConstantPositive kernel kernelData
  obtain ⟨jointContinuous, kernelProperties⟩ := kernelData
  have continuousProperties : XiContinuousSemigroupProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair := by
    dsimp only [XiContinuousSemigroupProperties]
    exact ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, intertwining⟩
  have smoothing := xiContinuousSemigroupSmoothingProperties_of_continuousSemigroup system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair continuousProperties
  have compactSmoothing := xiContinuousSemigroupCompactSmoothingProperties_of_smoothing system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair smoothing
  have allTimeCompact := xiContinuousAllTimeCompactSmoothingProperties_of_compactSmoothing system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair compactSmoothing
  have strictProperties : XiStrictPositiveJointContinuousHeatKernelDensityProperties system rulesConnected
      rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
      vectorPositive renormalizationEigenpair := by
    dsimp only [XiStrictPositiveJointContinuousHeatKernelDensityProperties]
    exact ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous,
      intertwining, timeThreshold, timeThresholdPositive, upperConstant, upperConstantPositive,
      kernel, jointContinuous, kernelProperties⟩
  have localLower := xiContinuousKernelLocalStayLowerProperties_of_shared_semigroup system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair normalization normalizationPositive strictProperties stayProperties
  dsimp only [XiContinuousKernelLocalStayLowerProperties] at localLower
  obtain ⟨lowerDense, lowerSemigroup, _, _, _, _, _, lowerThreshold, lowerThresholdPositive,
    lowerUpperConstant, lowerUpperPositive, lowerKernel, lowerContinuous, lowerKernelProperties,
    fraction, fractionPositive, count, geometricLower⟩ := localLower
  have denseEquality : lowerDense = originalDense := Subsingleton.elim _ _
  subst lowerDense
  choose kernelSymmetric kernelPositive kernelUpper kernelMass continuousRepresentation
    lifted liftedRepresentation liftedCompatibility using kernelProperties
  have kernelEquality : lowerKernel = kernel := by
    funext time
    obtain ⟨_, _, _, _, _, lowerLift, lowerRepresentation, lowerCompatibility⟩ := lowerKernelProperties time
    exact continuousKernel_eq_of_same_closed_operator
      (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
      (xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
      (xiContinuousL2Map_injective system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
      (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time.val)
      (lowerKernel time) (kernel time)
      (lowerContinuous.comp (continuous_const.prodMk continuous_id))
      (jointContinuous.comp (continuous_const.prodMk continuous_id))
      lowerLift (lifted time) lowerRepresentation (liftedRepresentation time)
      lowerCompatibility (liftedCompatibility time)
  subst lowerKernel
  have timeRateGreaterThanOne := xiAnalyticTimeRate_gt_one system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive mass resistanceRate ratePositive resistanceVector vectorPositive
    (funext renormalizationEigenpair)
  have rateEquality := system.resistanceSpectralRadius_eq_of_positive_eigenpair
    rulesConnected distancePositive ratePositive vectorPositive (funext renormalizationEigenpair)
  have canonicalTimeIdentity :
      realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rulesConnected distancePositive = mass.rate * resistanceRate := by
    rw [XiMassParameters.rate_eq_spectralRadius system mass, rateEquality]
  let radiusScale : ℝ := 4 * ((count + 2 : ℝ) * (3 * xiRuleRadius system parameters.lengths + 1))
  have radiusScalePositive : 0 < radiusScale := by
    have radiusNonnegative := xiRuleRadius_nonnegative system
      (fun colour => (parameters.lengthsPositive colour).le)
    dsimp only [radiusScale]
    positivity
  obtain ⟨radiusConstant, radiusConstantPositive, lowerCutoff, lowerCutoffPositive, inverseLower⟩ :=
    inverse_open_ball_lower_of_geometric_closed_balls
      (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
      (mass.rate * resistanceRate) (system.distanceSpectralRadius rulesConnected)
      (2 * fraction) radiusScale (9 / 16) timeRateGreaterThanOne distanceGreaterThanOne
      (by positivity) radiusScalePositive (by norm_num)
      (fun time point => kernel time point point) (by
        intro coarse time timeBound point
        have canonicalBound : (time.val : ℝ) ≤ (2 * fraction) *
            (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
              system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse := by
          rw [canonicalTimeIdentity]
          exact timeBound
        simpa only [radiusScale, mul_assoc] using geometricLower coarse time canonicalBound point)
  dsimp only at volumeUpper
  obtain ⟨volumeConstant, volumeRadius, volumeConstantPositive, volumeRadiusPositive, localVolume⟩ := volumeUpper
  have dimensionNonnegative : 0 ≤ Real.log mass.rate /
      Real.log (system.distanceSpectralRadius rulesConnected) :=
    div_nonneg (Real.log_nonneg
      ((by norm_num : (1 : ℝ) ≤ 2).trans (mass.rate_ge_two system rulesConnected plantingNonadjacent)))
      (Real.log_pos distanceGreaterThanOne).le
  obtain ⟨globalVolumeConstant, globalVolumePositive, globalVolume⟩ :=
    ball_mass_power_upper_all_radii_of_local
      (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
      volumeConstant volumeRadius
      (Real.log mass.rate / Real.log (system.distanceSpectralRadius rulesConnected))
      volumeConstantPositive volumeRadiusPositive dimensionNonnegative localVolume
  have exponentIdentity :
      (Real.log (system.distanceSpectralRadius rulesConnected) / Real.log (mass.rate * resistanceRate)) *
        (Real.log mass.rate / Real.log (system.distanceSpectralRadius rulesConnected)) =
      Real.log mass.rate / Real.log (mass.rate * resistanceRate) := by
    field_simp [(Real.log_pos distanceGreaterThanOne).ne']
  exact diagonal_power_two_sided_of_inverse_ball_and_volume_upper
    (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
    globalVolumeConstant radiusConstant (9 / 16)
    (Real.log (system.distanceSpectralRadius rulesConnected) / Real.log (mass.rate * resistanceRate))
    (Real.log mass.rate / Real.log (system.distanceSpectralRadius rulesConnected))
    (Real.log mass.rate / Real.log (mass.rate * resistanceRate))
    lowerCutoff timeThreshold upperConstant globalVolumePositive radiusConstantPositive (by norm_num)
    lowerCutoffPositive timeThresholdPositive upperConstantPositive exponentIdentity globalVolume
    (fun time point => kernel time point point) inverseLower (fun time point => kernelUpper time point point)

end
end EIGS

#print axioms EIGS.xiSameKernelPowerHeatEstimatesProperties_of_discrete_and_volume
