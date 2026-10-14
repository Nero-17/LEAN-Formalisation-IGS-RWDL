import RequestProject.Section31.EIGSOriginalMeasuredGHPSHuntHeatOfRules
import RequestProject.Section31.EIGSFiniteBornSpectralDimensionOfRules
import RequestProject.Section31.EIGSTypicalLogarithmicHeatKernelOfRules
import RequestProject.Section31.EIGSTypicalHeatSpectralDimensionOfRules
import RequestProject.Section31.LogarithmicHeatLowerCommonAE
import RequestProject.Section31.ContinuousKernelSameClosedIdentification

/-! All heat estimates for every continuous density of the very same closed
semigroup. The existence endpoint chooses native discrete resistance and
clock data once, branches to the accepted Hunt/heat/GHPS bundle and to the
stay estimate, then identifies any exported typical kernel pointwise with
the supplied kernel. No independently chosen eigenvectors are equated.
Candidate source: no compilation is claimed. -/

namespace IGS.Sec31
open MeasureTheory Filter Topology
open scoped Classical NNReal
noncomputable section
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

def PositiveClosedKernelData (law : Measure Space)
    (embedding : C(Space, ℝ) →L[ℝ] Lp ℝ 2 law)
    (closedSemigroup : ℝ≥0 → Lp ℝ 2 law →L[ℝ] Lp ℝ 2 law)
    (exponent : ℝ) (semigroup : ℝ≥0 → C(Space, ℝ) →L[ℝ] C(Space, ℝ))
    (timeThreshold upperConstant : ℝ)
    (kernel : {time : ℝ≥0 // 0 < time} → Space → Space → ℝ) : Prop :=
  Continuous (fun point : {time : ℝ≥0 // 0 < time} × Space × Space =>
    kernel point.1 point.2.1 point.2.2) ∧
  ∀ time : {time : ℝ≥0 // 0 < time},
    (∀ first second, kernel time first second = kernel time second first) ∧
    (∀ first second, 0 < kernel time first second) ∧
    (∀ first second, kernel time first second ≤ upperConstant /
      (min ((time.val : ℝ) / 2) timeThreshold) ^ exponent) ∧
    (∀ point, (∫ other, kernel time point other ∂law) = 1) ∧
    (∀ (function : C(Space, ℝ)) point,
      semigroup time.val function point = ∫ other, kernel time point other * function other ∂law) ∧
    ∃ lifted : Lp ℝ 2 law →L[ℝ] C(Space, ℝ),
      (∀ forcing point, lifted forcing point = ∫ other, kernel time point other * forcing other ∂law) ∧
      ∀ forcing, embedding (lifted forcing) = closedSemigroup time.val forcing

def positiveKernelRealDiagonal
    (kernel : {time : ℝ≥0 // 0 < time} → Space → Space → ℝ)
    (time : ℝ) (point : Space) : ℝ :=
  if positive : 0 < time then kernel ⟨⟨time, positive.le⟩, positive⟩ point point else 0

def PositiveKernelFullHeatEstimates (law : Measure Space)
    {Vertex : ℕ → Type*} (vertices : ∀ birth, Vertex birth → Space)
    (finiteExponent typicalExponent baseLogExponent : ℝ)
    (kernel : {time : ℝ≥0 // 0 < time} → Space → Space → ℝ) : Prop :=
  (∀ birth vertex, ∃ upperConstant : ℝ, 0 < upperConstant ∧
    ∀ time : {time : ℝ≥0 // 0 < time}, (time.val : ℝ) ≤ 1 →
      kernel time (vertices birth vertex) (vertices birth vertex) ≤ upperConstant / (time.val : ℝ) ^ finiteExponent) ∧
  (∀ birth vertex, ∃ lowerConstant cutoffTime : ℝ,
    0 < lowerConstant ∧ 0 < cutoffTime ∧ cutoffTime ≤ 1 ∧
    ∀ time : {time : ℝ≥0 // 0 < time}, (time.val : ℝ) ≤ cutoffTime →
      lowerConstant / (time.val : ℝ) ^ finiteExponent ≤ kernel time (vertices birth vertex) (vertices birth vertex)) ∧
  (∀ birth vertex, Tendsto (fun time : ℝ =>
    -2 * Real.log (positiveKernelRealDiagonal kernel time (vertices birth vertex)) / Real.log time)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * finiteExponent))) ∧
  (∀ᵐ point ∂law, ∀ epsilon : ℝ, 0 < epsilon →
    ∃ lowerConstant : ℝ, 0 < lowerConstant ∧ ∃ cutoffTime : ℝ, 0 < cutoffTime ∧
    ∀ time : {time : ℝ≥0 // 0 < time}, (time.val : ℝ) ≤ cutoffTime →
      lowerConstant * (time.val : ℝ) ^ (-typicalExponent) *
        |Real.log (time.val : ℝ)| ^ (-(baseLogExponent + epsilon)) ≤ kernel time point point) ∧
  ∀ᵐ point ∂law, Tendsto (fun time : ℝ =>
    -2 * Real.log (positiveKernelRealDiagonal kernel time point) / Real.log time)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * typicalExponent))

end
end IGS.Sec31

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical NNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 12000000
variable {K : ℕ}
def XiSameKernelFullHeatEstimatesProperties (system : EIGSData K)
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
      PositiveKernelFullHeatEstimates
        (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
        parameters.vertexEmbedding
        ((Real.log mass.rate - Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system))) /
          Real.log (mass.rate * resistanceRate))
        (Real.log mass.rate / Real.log (mass.rate * resistanceRate))
        (1 / (Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) - 1)) kernel
theorem xiSameKernelFullHeatEstimatesProperties_of_discrete (system : EIGSData K)
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
    (primitiveDegree : (degreeMatrix system).IsPrimitive)
    (discreteProperties : XiNativeSupDiscreteConvergenceProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair normalization normalizationPositive) :
    XiSameKernelFullHeatEstimatesProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
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
  dsimp only [XiSameKernelFullHeatEstimatesProperties]
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
  have finiteBorn := xiFiniteBornHeatSpectralDimensionProperties_of_compactSmoothing system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair primitiveDegree allTimeCompact
  dsimp only [XiFiniteBornHeatSpectralDimensionProperties] at finiteBorn
  obtain ⟨upperProperties, lowerProperties, dimension⟩ := finiteBorn
  dsimp only [XiFiniteBornHeatUpperProperties] at upperProperties
  dsimp only [XiFiniteBornHeatLowerProperties] at lowerProperties
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
  have typical := xiTypicalLogarithmicHeatKernelProperties_of_actual_local_lower system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair primitiveDegree localLower
  dsimp only [XiTypicalLogarithmicHeatKernelProperties] at typical
  obtain ⟨typicalDense, _, _, _, _, _, _, typicalThreshold, typicalThresholdPositive,
    typicalUpper, typicalUpperPositive, typicalKernel, typicalContinuous, typicalKernelProperties, lowerFamily⟩ := typical
  have denseEquality : typicalDense = originalDense := Subsingleton.elim _ _
  subst typicalDense
  choose kernelSymmetric kernelPositive kernelUpper kernelMass continuousRepresentation
    lifted liftedRepresentation liftedCompatibility using kernelProperties
  have kernelEquality : typicalKernel = kernel := by
    funext time
    obtain ⟨_, _, _, _, _, typicalLift, typicalRepresentation, typicalCompatibility⟩ := typicalKernelProperties time
    exact continuousKernel_eq_of_same_closed_operator
      (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
      (xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
      (xiContinuousL2Map_injective system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
      (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time.val)
      (typicalKernel time) (kernel time)
      (typicalContinuous.comp (continuous_const.prodMk continuous_id))
      (jointContinuous.comp (continuous_const.prodMk continuous_id))
      typicalLift (lifted time) typicalRepresentation (liftedRepresentation time)
      typicalCompatibility (liftedCompatibility time)
  subst typicalKernel
  let extendedKernel : ℝ≥0 → parameters.LimitSpace → parameters.LimitSpace → ℝ :=
    fun time => if positive : 0 < time then kernel ⟨time, positive⟩ else fun _ _ => 0
  let extendedLift : ℝ≥0 → Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass) →L[ℝ]
      C(parameters.LimitSpace, ℝ) :=
    fun time => if positive : 0 < time then lifted ⟨time, positive⟩ else 0
  have extendedContinuous (time : ℝ≥0) (positive : 0 < time) :
      Continuous (fun points : parameters.LimitSpace × parameters.LimitSpace => extendedKernel time points.1 points.2) := by
    simpa only [extendedKernel, dif_pos positive] using
      jointContinuous.comp (continuous_const.prodMk continuous_id)
  have extendedRepresentation (time : ℝ≥0) (positive : 0 < time) (forcing) (point) :
      extendedLift time forcing point = ∫ other, extendedKernel time point other * forcing other
        ∂xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass := by
    simpa only [extendedLift, extendedKernel, dif_pos positive] using liftedRepresentation ⟨time, positive⟩ forcing point
  have extendedCompatibility (time : ℝ≥0) (positive : 0 < time) (forcing) :
      xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
        (extendedLift time forcing) =
      QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time forcing := by
    simpa only [extendedLift, dif_pos positive] using liftedCompatibility ⟨time, positive⟩ forcing
  dsimp only [PositiveKernelFullHeatEstimates]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro birth vertex
    obtain ⟨constant, constantPositive, bound⟩ := upperProperties.2 originalDense birth vertex
    refine ⟨constant, constantPositive, ?_⟩
    intro time timeSmall
    exact bound time.val time.property timeSmall (kernel time)
      (jointContinuous.comp (continuous_const.prodMk continuous_id))
      (lifted time) (liftedRepresentation time) (liftedCompatibility time)
  · intro birth vertex
    obtain ⟨constant, cutoff, constantPositive, cutoffPositive, cutoffAtMostOne, bound⟩ :=
      lowerProperties.2 originalDense birth vertex
    refine ⟨constant, cutoff, constantPositive, cutoffPositive, cutoffAtMostOne, ?_⟩
    intro time timeSmall
    exact bound time.val time.property timeSmall (kernel time)
      (jointContinuous.comp (continuous_const.prodMk continuous_id))
      (lifted time) (liftedRepresentation time) (liftedCompatibility time)
  · intro birth vertex
    have finiteDimension := dimension originalDense birth vertex extendedKernel extendedContinuous
      extendedLift extendedRepresentation extendedCompatibility
    apply finiteDimension.congr'
    filter_upwards [self_mem_nhdsWithin] with time positive
    have timePositive : 0 < time := positive
    have positiveNNReal : 0 < time.toNNReal := Real.toNNReal_pos.mpr timePositive
    have timeEquality : (⟨time.toNNReal, positiveNNReal⟩ : {time : ℝ≥0 // 0 < time}) =
        ⟨⟨time, timePositive.le⟩, timePositive⟩ := by
      apply Subtype.ext
      exact Subtype.ext (Real.coe_toNNReal time timePositive.le)
    simp only [extendedKernel, dif_pos positiveNNReal, positiveKernelRealDiagonal,
      dif_pos timePositive, timeEquality]
  · exact logarithmic_heat_lower_common_ae
      (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
      (fun time point => kernel time point point)
      (Real.log mass.rate / Real.log (mass.rate * resistanceRate))
      (1 / (Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) - 1)) lowerFamily
  · filter_upwards [lowerFamily 1 (by norm_num)] with point lower
    obtain ⟨constant, constantPositive, cutoff, cutoffPositive, bound⟩ := lower
    exact IGS.Sec31.tendsto_spectral_dimension_of_positive_kernel_bounds
      (fun time => kernel time point point)
      (Real.log mass.rate / Real.log (mass.rate * resistanceRate))
      (1 / (Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) - 1) + 1)
      constant upperConstant cutoff timeThreshold constantPositive upperConstantPositive cutoffPositive
      timeThresholdPositive bound (fun time => kernelUpper time point point)
theorem exists_xiSameNativeJointFullHeatEstimates_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (primitiveDegree : (degreeMatrix system).IsPrimitive)
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
      XiIdentifiedOriginalMeasuredGHPSHuntHeatProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive ∧
      XiSameKernelFullHeatEstimatesProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, discreteProperties⟩ :=
    exists_xiNativeSupDiscreteConvergence_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  have pathProperties := xiIdentifiedOriginalCommonPathTransportProperties_of_discrete system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair normalization normalizationPositive discreteProperties
  have globalProperties := xiIdentifiedOriginalCommonGlobalJ1Properties_of_transport system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair normalization normalizationPositive pathProperties
  have measuredProperties := xiIdentifiedOriginalMeasuredGHPSProperties_of_globalJ1 system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair normalization normalizationPositive globalProperties
  have jointProperties := xiIdentifiedOriginalMeasuredGHPSHuntHeatProperties_of_measured system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair normalization normalizationPositive measuredProperties
  exact ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, jointProperties,
    xiSameKernelFullHeatEstimatesProperties_of_discrete system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair normalization normalizationPositive primitiveDegree discreteProperties⟩

end
end EIGS

#print axioms EIGS.xiSameKernelFullHeatEstimatesProperties_of_discrete
#print axioms EIGS.exists_xiSameNativeJointFullHeatEstimates_of_rules
