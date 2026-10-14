import RequestProject.Section31.EIGSContinuousAllTimeHeatKernelDensityOfRules
import RequestProject.Section31.ContinuousKernelFixedWindow

/-! The same actual heat kernel is jointly continuous in positive time and
both spatial variables. A fixed local smoothing window identifies it with
inner(row_a(x), closedS(t-2a) row_a(y)); all operator continuity and compactness
are supplied by the already constructed actual semigroup and smoothing maps. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped BoundedContinuousFunction NNReal
noncomputable section
set_option maxHeartbeats 7000000
variable {K : ℕ}

def XiJointContinuousHeatKernelDensityProperties (system : EIGSData K)
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
          ∀ time : {time : ℝ≥0 // 0 < time},
            (∀ first second, kernel time first second = kernel time second first) ∧
            (∀ first second, 0 ≤ kernel time first second) ∧
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
                QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time.val forcing

theorem xiJointContinuousHeatKernelDensityProperties_of_compactSmoothing (system : EIGSData K)
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
    (compactSmoothingProperties : XiContinuousAllTimeCompactSmoothingProperties system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair) :
    XiJointContinuousHeatKernelDensityProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
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
  have densityProperties := xiContinuousAllTimeHeatKernelDensityProperties_of_compactSmoothing system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair compactSmoothingProperties
  dsimp only [XiContinuousAllTimeHeatKernelDensityProperties, XiJointContinuousHeatKernelDensityProperties]
    at densityProperties ⊢
  obtain ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous,
    intertwining, timeThreshold, timeThresholdPositive, upperConstant, upperConstantPositive, density⟩ := densityProperties
  dsimp only [XiContinuousAllTimeCompactSmoothingProperties] at compactSmoothingProperties
  obtain ⟨smoothingDense, _, _, _, _, _, _, _, _, _, _, allSmoothing⟩ := compactSmoothingProperties
  have densityEquality : smoothingDense = originalDense := Subsingleton.elim _ _
  subst smoothingDense
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
  have positiveDensity (time : {time : ℝ≥0 // 0 < time}) := density time.val time.prop
  choose kernel kernelContinuous kernelSymmetric kernelNonnegative kernelUpper kernelMass
    continuousRepresentation lifted liftedRepresentation liftedCompatibility using positiveDensity
  let closedSemigroup := QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense
  have closedJointContinuous : Continuous (fun point : Lp ℝ 2 measure × ℝ≥0 =>
      closedSemigroup point.2 point.1) :=
    QuadraticEnergySpace.closedSemigroup_joint_continuous originalDomain originalForm nonnegative closable originalDense
  have jointContinuous : Continuous (fun point : {time : ℝ≥0 // 0 < time} × parameters.LimitSpace × parameters.LimitSpace =>
      kernel point.1 point.2.1 point.2.2) := by
    rw [continuous_iff_continuousAt]
    intro reference
    let window : ℝ≥0 := reference.1.val / 4
    have windowPositive : 0 < window := div_pos reference.1.prop (by norm_num)
    obtain ⟨windowLifted, _, windowCompact, _, windowCompatibility⟩ := allSmoothing window windowPositive
    have rowContinuous : Continuous (continuousOperatorKernelRow windowLifted) :=
      continuousOperatorKernelRow_continuous windowLifted windowCompact
    let alternateKernel := fun point : {time : ℝ≥0 // 0 < time} × parameters.LimitSpace × parameters.LimitSpace =>
      inner ℝ (continuousOperatorKernelRow windowLifted point.2.1)
        (closedSemigroup (point.1.val - (window + window)) (continuousOperatorKernelRow windowLifted point.2.2))
    have alternateContinuous : Continuous alternateKernel := by
      apply (rowContinuous.comp (continuous_fst.comp continuous_snd)).inner
      exact closedJointContinuous.comp
        ((rowContinuous.comp (continuous_snd.comp continuous_snd)).prodMk
          ((continuous_subtype_val.comp continuous_fst).sub continuous_const))
    have kernelEquality (time : {time : ℝ≥0 // 0 < time}) (timeLarge : window + window ≤ time.val)
        (first second : parameters.LimitSpace) :
        kernel time first second = alternateKernel (time, first, second) := by
      let residual := time.val - (window + window)
      have timeDecomposition : window + (residual + window) = time.val := by
        calc
          _ = (window + window) + residual := by ring
          _ = time.val := add_tsub_cancel_of_le timeLarge
      have factorization : (closedSemigroup window).comp
          ((closedSemigroup residual).comp (closedSemigroup window)) = closedSemigroup time.val := by
        calc
          _ = (closedSemigroup window).comp (closedSemigroup (residual + window)) :=
            congrArg (fun operator => (closedSemigroup window).comp operator)
              (QuadraticEnergySpace.closedSemigroup_add originalDomain originalForm nonnegative closable originalDense residual window).symm
          _ = closedSemigroup (window + (residual + window)) :=
            (QuadraticEnergySpace.closedSemigroup_add originalDomain originalForm nonnegative closable originalDense
              window (residual + window)).symm
          _ = _ := congrArg closedSemigroup timeDecomposition
      have windowOutputEquality (forcing : Lp ℝ 2 measure) :
          lifted time forcing = windowLifted (closedSemigroup residual (closedSemigroup window forcing)) := by
        apply embeddingInjective
        rw [liftedCompatibility, windowCompatibility]
        exact (congrArg (fun operator : Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure => operator forcing) factorization).symm
      let firstRow : C(parameters.LimitSpace, ℝ) := ⟨kernel time first,
        (kernelContinuous time).comp (continuous_const.prodMk continuous_id)⟩
      let secondRow : C(parameters.LimitSpace, ℝ) :=
        ⟨fun other => inner ℝ (continuousOperatorKernelRow windowLifted first)
          (closedSemigroup residual (continuousOperatorKernelRow windowLifted other)),
          continuous_const.inner ((closedSemigroup residual).continuous.comp rowContinuous)⟩
      have rowEquality : firstRow = secondRow := by
        apply continuous_L2_kernel_row_unique measure
        intro forcing
        calc
          _ = lifted time forcing first := (liftedRepresentation time forcing first).symm
          _ = windowLifted (closedSemigroup residual (closedSemigroup window forcing)) first :=
            congrArg (fun function : C(parameters.LimitSpace, ℝ) => function first) (windowOutputEquality forcing)
          _ = _ := continuousOperator_fixed_window_integral measure embedding embeddingAE windowLifted
            (closedSemigroup window) (closedSemigroup residual)
            (QuadraticEnergySpace.closedSemigroup_selfAdjoint originalDomain originalForm nonnegative closable originalDense window)
            (QuadraticEnergySpace.closedSemigroup_selfAdjoint originalDomain originalForm nonnegative closable originalDense residual)
            windowCompatibility first forcing
      exact congrArg (fun function : C(parameters.LimitSpace, ℝ) => function second) rowEquality
    have referenceLarge : window + window < reference.1.val := by
      change (window : ℝ) + (window : ℝ) < (reference.1.val : ℝ)
      simp only [window, NNReal.coe_div, NNReal.coe_ofNat]
      have referencePositive : 0 < (reference.1.val : ℝ) := reference.1.prop
      linarith
    have eventuallyLarge : ∀ᶠ nearby in 𝓝 reference, window + window < nearby.1.val :=
      (continuous_subtype_val.comp continuous_fst).continuousAt.tendsto.eventually (gt_mem_nhds referenceLarge)
    apply alternateContinuous.continuousAt.congr_of_eventuallyEq
    filter_upwards [eventuallyLarge] with nearby nearbyLarge
    exact kernelEquality nearby.1 nearbyLarge.le nearby.2.1 nearby.2.2
  refine ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous,
    intertwining, timeThreshold, timeThresholdPositive, upperConstant, upperConstantPositive,
    kernel, jointContinuous, ?_⟩
  intro time
  exact ⟨kernelSymmetric time, kernelNonnegative time, kernelUpper time, kernelMass time,
    continuousRepresentation time, lifted time, liftedRepresentation time, liftedCompatibility time⟩

theorem exists_xiJointContinuousHeatKernelDensity_of_rules (system : EIGSData K)
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
      XiJointContinuousHeatKernelDensityProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, continuousProperties⟩ :=
    exists_xiContinuousAllTimeCompactSmoothing_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiJointContinuousHeatKernelDensityProperties_of_compactSmoothing system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair continuousProperties

end
end EIGS

#print axioms EIGS.xiJointContinuousHeatKernelDensityProperties_of_compactSmoothing
#print axioms EIGS.exists_xiJointContinuousHeatKernelDensity_of_rules