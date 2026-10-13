import RequestProject.Section31.EIGSNativeSupResolventOperator
import RequestProject.Section31.EIGSContinuousResolventContraction
import RequestProject.Section31.VaryingBanachOperatorApproximation

/-! Native fixed-step Yosida exponentials converge in supremum norm on the
actual finite vertex sets. The restriction is actual vertex evaluation and
the finite resolvent is the already constructed native L² resolvent,
transported to vertex functions. The original-rule resolvent consumers
supply the one-step uniform convergence hypothesis for the same family. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

variable {K : ℕ}

def xiContinuousVertexRestriction
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected)
    [CompactSpace parameters.LimitSpace] (level : ℕ) :
    C(parameters.LimitSpace, ℝ) →L[ℝ] (XiVtx system level → ℝ) :=
  let linear : C(parameters.LimitSpace, ℝ) →ₗ[ℝ] (XiVtx system level → ℝ) := {
    toFun := fun function vertex => function (parameters.vertexEmbedding level vertex)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  linear.mkContinuous 1 (fun function => by
    simp only [one_mul]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg function)).mpr
    intro vertex
    exact function.norm_coe_le_norm _)

theorem xiContinuousVertexRestriction_apply
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected)
    [CompactSpace parameters.LimitSpace] (level : ℕ)
    (function : C(parameters.LimitSpace, ℝ)) (vertex : XiVtx system level) :
    xiContinuousVertexRestriction system rulesConnected parameters level function vertex =
      function (parameters.vertexEmbedding level vertex) := rfl

theorem xiContinuousVertexRestriction_norm_le_one
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected)
    [CompactSpace parameters.LimitSpace] (level : ℕ) :
    ‖xiContinuousVertexRestriction system rulesConnected parameters level‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro function
  simp only [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg function)).mpr
  intro vertex
  exact function.norm_coe_le_norm _

theorem xiNativeSupYosida_uniform_limit
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (parameters : XiPathMetricData system rulesConnected) [CompactSpace parameters.LimitSpace]
    (mass : XiMassParameters system) (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (step : ℝ) (stepPositive : 0 < step)
    (resolver : C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ))
    (resolverNorm : ‖resolver‖ ≤ 1)
    (uniformConvergence : ∀ function : C(parameters.LimitSpace, ℝ),
      Tendsto (fun level => ‖fun vertex : XiVtx system level =>
        xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
          (xiFiniteSpeedL2 system mass level (fun vertex => function (parameters.vertexEmbedding level vertex))) vertex -
        resolver function (parameters.vertexEmbedding level vertex)‖) atTop (nhds 0))
    (time : ℝ) (function : C(parameters.LimitSpace, ℝ)) :
    Tendsto (fun level => ‖BoundedYosida.semigroup
      (xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive) step time
      (fun vertex => function (parameters.vertexEmbedding level vertex)) -
      (fun vertex => BoundedYosida.semigroup resolver step time function
        (parameters.vertexEmbedding level vertex))‖) atTop (nhds 0) := by
  have resolverConvergence (argument : C(parameters.LimitSpace, ℝ)) :
      Tendsto (fun level => ‖xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
        (xiContinuousVertexRestriction system rulesConnected parameters level argument) -
        xiContinuousVertexRestriction system rulesConnected parameters level (resolver argument)‖) atTop (nhds 0) := by
    change Tendsto (fun level => ‖fun vertex : XiVtx system level =>
      xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
        (xiFiniteSpeedL2 system mass level (fun vertex => argument (parameters.vertexEmbedding level vertex))) vertex -
      resolver argument (parameters.vertexEmbedding level vertex)‖) atTop (nhds 0)
    exact uniformConvergence argument
  exact VaryingBanachOperatorApproximation.yosida_exponential_apply
    (xiContinuousVertexRestriction system rulesConnected parameters)
    (xiContinuousVertexRestriction_norm_le_one system rulesConnected parameters)
    (fun level => xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive)
    resolver
    (fun level => xiNativeSupResolvent_norm_le_one system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive)
    resolverNorm resolverConvergence step stepPositive time function

def XiNativeSupYosidaConvergenceProperties (system : EIGSData K)
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
    ∀ (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1),
    let closedOperator := QuadraticEnergySpace.smallStepResolvent originalDomain originalForm nonnegative closable
      originalDense step stepPositive stepAtMostOne
    ∃ resolver : C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ), ‖resolver‖ ≤ 1 ∧
      ∀ function : C(parameters.LimitSpace, ℝ),
      let forcing := fun level => core.restrict level (BoundedContinuousFunction.mkOfCompact function)
      let solution := fun level => xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive (forcing level)
      core.embed (BoundedContinuousFunction.mkOfCompact (resolver function)) =
          closedOperator (core.embed (BoundedContinuousFunction.mkOfCompact function)) ∧
        Tendsto (fun level => ‖fun vertex : XiVtx system level =>
          solution level vertex - resolver function (parameters.vertexEmbedding level vertex)‖) atTop (nhds 0) ∧
        ∀ time : ℝ,
          Tendsto (fun level => ‖BoundedYosida.semigroup
            (xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
              mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive) step time
            (fun vertex => function (parameters.vertexEmbedding level vertex)) -
            (fun vertex => BoundedYosida.semigroup resolver step time function
              (parameters.vertexEmbedding level vertex))‖) atTop (nhds 0)

theorem xiNativeSupYosidaConvergenceProperties_of_contraction (system : EIGSData K)
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
    (contractionProperties : XiContinuousResolventContractionProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair normalization normalizationPositive) :
    XiNativeSupYosidaConvergenceProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
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
  dsimp only [XiContinuousResolventContractionProperties, XiNativeSupYosidaConvergenceProperties]
    at contractionProperties ⊢
  obtain ⟨originalDense, contractionProperties⟩ := contractionProperties
  refine ⟨originalDense, ?_⟩
  intro step stepPositive stepAtMostOne
  obtain ⟨resolver, resolverNorm, representations⟩ := contractionProperties step stepPositive stepAtMostOne
  refine ⟨resolver, resolverNorm, ?_⟩
  intro function
  refine ⟨(representations function).1, (representations function).2, ?_⟩
  intro time
  apply xiNativeSupYosida_uniform_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    parameters mass resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive
    resolver resolverNorm ?_ time function
  intro argument
  have uniform := (representations argument).2
  simpa only [core, xiSpeedL2Core_restrict_eq_finiteSpeedL2] using uniform

theorem exists_xiNativeSupYosidaConvergence_of_rules (system : EIGSData K)
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
        atTop (nhds (normalization • resistanceVector)) ∧
      XiNativeSupYosidaConvergenceProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, contractionProperties⟩ :=
    exists_xiContinuousResolventContraction_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiNativeSupYosidaConvergenceProperties_of_contraction system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair normalization normalizationPositive contractionProperties


end
end EIGS

#print axioms EIGS.xiContinuousVertexRestriction_apply
#print axioms EIGS.xiContinuousVertexRestriction_norm_le_one
#print axioms EIGS.xiNativeSupYosida_uniform_limit
#print axioms EIGS.xiNativeSupYosidaConvergenceProperties_of_contraction
#print axioms EIGS.exists_xiNativeSupYosidaConvergence_of_rules
