import RequestProject.Section31.EIGSContinuousResolventApproximateIdentity
import RequestProject.Section31.BanachResolventYosidaGeneration
import RequestProject.Section31.ClosedResolventLiftIdentities
import RequestProject.Section31.BoundedYosidaInvariantConvex

/-! A C0 contraction semigroup on the actual compact completion, constructed
from the native continuous resolvents. The original-rule consumer discharges
resolvent commutation, compatibility and approximation of the identity.
Poisson series identify the resulting continuous semigroup with the already
constructed closed-form L² semigroup. Native floor-path convergence and the
all-point Markov kernel construction are subsequent consumers. -/

namespace IGS.Sec31.BoundedYosida

open Filter Topology

variable {Space Target : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target] [CompleteSpace Target]

theorem semigroup_intertwining (embedding : Space →L[ℝ] Target)
    (resolver : Space →L[ℝ] Space) (targetResolver : Target →L[ℝ] Target)
    (intertwining : ∀ values, embedding (resolver values) = targetResolver (embedding values))
    (step time : ℝ) (values : Space) :
    embedding (semigroup resolver step time values) =
      semigroup targetResolver step time (embedding values) := by
  have powers (index : ℕ) : embedding ((resolver ^ index) values) =
      (targetResolver ^ index) (embedding values) := by
    induction index with
    | zero => simp only [pow_zero, ContinuousLinearMap.one_apply]
    | succ index induction =>
        simp only [pow_succ', ContinuousLinearMap.mul_apply, intertwining, induction]
  have transported := (semigroup_hasSum_powers resolver step time values).map embedding embedding.continuous
  dsimp only [Function.comp_def] at transported
  have transportedSum : HasSum (fun index : ℕ =>
      (Real.exp (-(time / step)) * ((index.factorial : ℝ)⁻¹ * (time / step) ^ index)) •
        (targetResolver ^ index) (embedding values))
      (embedding (semigroup resolver step time values)) := by
    simpa only [map_smul, powers] using transported
  exact transportedSum.unique (semigroup_hasSum_powers targetResolver step time (embedding values))

end IGS.Sec31.BoundedYosida

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 4000000

variable {K : ℕ}

def XiContinuousSemigroupProperties (system : EIGSData K)
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
      ∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
        xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
          (semigroup time function) =
        QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time
          (xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass function)

theorem xiContinuousSemigroupProperties_of_approximateIdentity (system : EIGSData K)
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
      renormalizationEigenpair normalization normalizationPositive) :
    XiContinuousSemigroupProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
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
  dsimp only [XiContinuousResolventApproximateIdentityProperties, XiContinuousSemigroupProperties]
    at approximateProperties ⊢
  obtain ⟨originalDense, resolvers, resolverProperties, approximateIdentity, _⟩ := approximateProperties
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
  refine ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, ?_⟩
  intro time function
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

theorem exists_xiContinuousSemigroup_of_rules (system : EIGSData K)
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
      XiContinuousSemigroupProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, approximateProperties⟩ :=
    exists_xiContinuousResolventApproximateIdentity_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiContinuousSemigroupProperties_of_approximateIdentity system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair normalization normalizationPositive approximateProperties

end
end EIGS

#print axioms IGS.Sec31.BoundedYosida.semigroup_intertwining
#print axioms EIGS.xiContinuousSemigroupProperties_of_approximateIdentity
#print axioms EIGS.exists_xiContinuousSemigroup_of_rules
