import RequestProject.Section31.EIGSContinuousSemigroupOfRules

/-! The canonical Yosida exponentials of the same actual continuous-resolvent
family converge in the supremum norm to the given continuous semigroup.
Generation first constructs a semigroup; the actual closed L² identification
and injectivity then identify it with the given one. The original-rule consumer
supplies every input internally, including approximation of the identity. -/

namespace IGS.Sec31.BanachResolventYosidaGeneration

open Filter Topology
open scoped NNReal

/-- The generated strong limit is identified with any given semigroup whose
embedded canonical approximants have the corresponding limit. The embedded
limit is weaker than the supremum-norm conclusion; strong Cauchy is proved
by generation from the resolvent inputs. -/
theorem operators_tendsto_of_injective_embedding
    {Space Target : Type*}
    [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (resolvents : ℕ → Space →L[ℝ] Space) (steps : ℕ → ℝ)
    (stepsPositive : ∀ index, 0 < steps index)
    (contraction : ∀ index, ‖resolvents index‖ ≤ 1)
    (nearIdentity : ∀ values, Tendsto (fun index => resolvents index values) atTop (𝓝 values))
    (commuting : ∀ first second, Commute (resolvents first) (resolvents second))
    (compatible : ∀ first second values,
      BoundedYosida.generator (resolvents first) (steps first) (resolvents second values) =
        resolvents first (BoundedYosida.generator (resolvents second) (steps second) values))
    (embedding : Space →L[ℝ] Target) (embeddingInjective : Function.Injective embedding)
    (givenSemigroup : ℝ≥0 → Space →L[ℝ] Space)
    (embeddedConvergence : ∀ time values,
      Tendsto (fun index => embedding (operators resolvents steps index time values))
        atTop (𝓝 (embedding (givenSemigroup time values)))) :
    ∀ time values, Tendsto (fun index => operators resolvents steps index time values)
      atTop (𝓝 (givenSemigroup time values)) := by
  obtain ⟨generated, _, _, _, _, generatedLimit⟩ :=
    exists_stronglyContinuous_contraction_semigroup resolvents steps stepsPositive contraction
      nearIdentity commuting compatible
  intro time values
  have transported := embedding.continuous.continuousAt.tendsto.comp (generatedLimit time values)
  dsimp only [Function.comp_def] at transported
  have identification : generated time values = givenSemigroup time values :=
    embeddingInjective (tendsto_nhds_unique transported (embeddedConvergence time values))
  simpa only [identification] using generatedLimit time values

end IGS.Sec31.BanachResolventYosidaGeneration

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 4000000
variable {K : ℕ}

def XiContinuousSemigroupYosidaProperties (system : EIGSData K)
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
  letI := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
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
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass))),
    ∃ resolvers : (step : ℝ) → 0 < step → step ≤ 1 →
      C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ),
    (∀ (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1),
      let closedOperator := QuadraticEnergySpace.smallStepResolvent originalDomain originalForm nonnegative closable
        originalDense step stepPositive stepAtMostOne
      ‖resolvers step stepPositive stepAtMostOne‖ ≤ 1 ∧
        ∀ function : C(parameters.LimitSpace, ℝ),
          core.embed (BoundedContinuousFunction.mkOfCompact (resolvers step stepPositive stepAtMostOne function)) =
            closedOperator (core.embed (BoundedContinuousFunction.mkOfCompact function)) ∧
          Tendsto (fun level => ‖fun vertex : XiVtx system level =>
            xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
              mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive
              (core.restrict level (BoundedContinuousFunction.mkOfCompact function)) vertex -
            resolvers step stepPositive stepAtMostOne function (parameters.vertexEmbedding level vertex)‖)
            atTop (nhds 0)) ∧
    (∀ (function : C(parameters.LimitSpace, ℝ)) (error : ℝ), 0 < error →
      ∃ thresholdStep : ℝ, 0 < thresholdStep ∧
        ∀ (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1),
          step < thresholdStep → ‖resolvers step stepPositive stepAtMostOne function - function‖ < error) ∧
    (∀ function : C(parameters.LimitSpace, ℝ),
      Tendsto (fun step : {step : ℝ // 0 < step ∧ step ≤ 1} =>
        resolvers step.1 step.2.1 step.2.2 function)
        (comap (fun step : {step : ℝ // 0 < step ∧ step ≤ 1} => step.1) (nhds (0 : ℝ)))
        (nhds function)) ∧
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
      ∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
        Tendsto (fun index => BanachResolventYosidaGeneration.operators
          (fun index => resolvers (QuadraticEnergySpace.canonicalYosidaStep index)
            (QuadraticEnergySpace.canonicalYosidaStep_positive index)
            (QuadraticEnergySpace.canonicalYosidaStep_le_one index))
          QuadraticEnergySpace.canonicalYosidaStep index time function)
          atTop (𝓝 (semigroup time function))

theorem xiContinuousSemigroupYosidaProperties_of_resolvents_and_semigroup (system : EIGSData K)
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
    (approximateProperties : XiContinuousResolventApproximateIdentityProperties system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair normalization normalizationPositive)
    (continuousProperties : XiContinuousSemigroupProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair) :
    XiContinuousSemigroupYosidaProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
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
  dsimp only [XiContinuousResolventApproximateIdentityProperties, XiContinuousSemigroupYosidaProperties]
    at approximateProperties ⊢
  obtain ⟨originalDense, resolvers, resolverProperties, approximateIdentity, fullStepLimit⟩ := approximateProperties
  dsimp only [XiContinuousSemigroupProperties] at continuousProperties
  obtain ⟨givenDense, givenSemigroup, givenNorm, givenZero, givenAdd, givenContinuous,
    givenIntertwining⟩ := continuousProperties
  have densityEquality : givenDense = originalDense := Subsingleton.elim _ _
  subst givenDense
  let embedding := xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  have embeddingInjective : Function.Injective embedding := xiContinuousL2Map_injective system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair mass
  let resolvents : ℕ → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ) := fun index =>
    resolvers (QuadraticEnergySpace.canonicalYosidaStep index)
      (QuadraticEnergySpace.canonicalYosidaStep_positive index) (QuadraticEnergySpace.canonicalYosidaStep_le_one index)
  have contraction (index : ℕ) : ‖resolvents index‖ ≤ 1 :=
    (resolverProperties _ _ _).1
  have intertwining (index : ℕ) (function : C(parameters.LimitSpace, ℝ)) :
      embedding (resolvents index function) =
        QuadraticEnergySpace.smallStepResolvent originalDomain originalForm nonnegative closable originalDense
          (QuadraticEnergySpace.canonicalYosidaStep index) (QuadraticEnergySpace.canonicalYosidaStep_positive index)
            (QuadraticEnergySpace.canonicalYosidaStep_le_one index) (embedding function) := by
    simpa only [embedding, xiContinuousL2Map] using ((resolverProperties _ _ _).2 function).1
  have nearIdentity (function : C(parameters.LimitSpace, ℝ)) :
      Tendsto (fun index => resolvents index function) atTop (𝓝 function) := by
    apply Metric.tendsto_nhds.mpr
    intro error errorPositive
    obtain ⟨threshold, thresholdPositive, afterThreshold⟩ := approximateIdentity function error errorPositive
    filter_upwards [QuadraticEnergySpace.canonicalYosidaStep_tendsto.eventually_lt_const thresholdPositive]
      with index smallStep
    simpa only [dist_eq_norm] using afterThreshold _ _ _ smallStep
  have commuting (first second : ℕ) : Commute (resolvents first) (resolvents second) :=
    QuadraticEnergySpace.lifted_smallStepResolvent_commute originalDomain originalForm nonnegative closable originalDense
      embedding.toLinearMap embeddingInjective
      (QuadraticEnergySpace.canonicalYosidaStep first) (QuadraticEnergySpace.canonicalYosidaStep second)
      (QuadraticEnergySpace.canonicalYosidaStep_positive first) (QuadraticEnergySpace.canonicalYosidaStep_le_one first)
      (QuadraticEnergySpace.canonicalYosidaStep_positive second) (QuadraticEnergySpace.canonicalYosidaStep_le_one second)
      (resolvents first) (resolvents second) (intertwining first) (intertwining second)
  have compatible (first second : ℕ) (function : C(parameters.LimitSpace, ℝ)) :
      BoundedYosida.generator (resolvents first) (QuadraticEnergySpace.canonicalYosidaStep first)
        (resolvents second function) =
      resolvents first (BoundedYosida.generator (resolvents second) (QuadraticEnergySpace.canonicalYosidaStep second) function) :=
    QuadraticEnergySpace.lifted_yosidaGenerator_resolvent_compatibility originalDomain originalForm nonnegative closable originalDense
      embedding.toLinearMap embeddingInjective
      (QuadraticEnergySpace.canonicalYosidaStep first) (QuadraticEnergySpace.canonicalYosidaStep second)
      (QuadraticEnergySpace.canonicalYosidaStep_positive first) (QuadraticEnergySpace.canonicalYosidaStep_le_one first)
      (QuadraticEnergySpace.canonicalYosidaStep_positive second) (QuadraticEnergySpace.canonicalYosidaStep_le_one second)
      (resolvents first) (resolvents second) (intertwining first) (intertwining second) function
  obtain ⟨semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, semigroupLimit⟩ :=
    BanachResolventYosidaGeneration.exists_stronglyContinuous_contraction_semigroup resolvents
      QuadraticEnergySpace.canonicalYosidaStep QuadraticEnergySpace.canonicalYosidaStep_positive
        contraction nearIdentity commuting compatible
  have generatedIntertwining (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)) :
      embedding (semigroup time function) =
        QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time
          (embedding function) := by
    have transportedLimit := embedding.continuous.continuousAt.tendsto.comp (semigroupLimit time function)
    have approximationIdentity (index : ℕ) :
        embedding (BanachResolventYosidaGeneration.operators resolvents QuadraticEnergySpace.canonicalYosidaStep
          index time function) =
        QuadraticEnergySpace.closedSemigroupApproximation originalDomain originalForm nonnegative closable
          originalDense index time (embedding function) := by
      exact BoundedYosida.semigroup_intertwining embedding (resolvents index)
        (QuadraticEnergySpace.smallStepResolvent originalDomain originalForm nonnegative closable originalDense
          (QuadraticEnergySpace.canonicalYosidaStep index) (QuadraticEnergySpace.canonicalYosidaStep_positive index)
            (QuadraticEnergySpace.canonicalYosidaStep_le_one index)) (intertwining index) _ _ function
    dsimp only [Function.comp_def] at transportedLimit
    simp only [approximationIdentity] at transportedLimit
    exact tendsto_nhds_unique transportedLimit
      (QuadraticEnergySpace.closedSemigroup_approximation_limit originalDomain originalForm nonnegative closable
        originalDense time (embedding function))
  have identified (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)) :
      semigroup time function = givenSemigroup time function := by
    apply embeddingInjective
    exact (generatedIntertwining time function).trans (givenIntertwining time function).symm
  refine ⟨originalDense, resolvers, resolverProperties, approximateIdentity, fullStepLimit,
    givenSemigroup, givenNorm, givenZero, givenAdd, givenContinuous, givenIntertwining, ?_⟩
  intro time function
  simpa only [identified] using semigroupLimit time function

theorem exists_xiContinuousSemigroupYosida_of_rules (system : EIGSData K)
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
      XiContinuousSemigroupYosidaProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, approximateProperties⟩ :=
    exists_xiContinuousResolventApproximateIdentity_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  have continuousProperties := xiContinuousSemigroupProperties_of_approximateIdentity system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair normalization normalizationPositive approximateProperties
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiContinuousSemigroupYosidaProperties_of_resolvents_and_semigroup system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair normalization normalizationPositive approximateProperties continuousProperties

end
end EIGS

#print axioms EIGS.xiContinuousSemigroupYosidaProperties_of_resolvents_and_semigroup
#print axioms EIGS.exists_xiContinuousSemigroupYosida_of_rules

#print axioms IGS.Sec31.BanachResolventYosidaGeneration.operators_tendsto_of_injective_embedding
