import RequestProject.Section31.EIGSNativeResolventUniformConvergence

/-! The actual closed resolvent acts as a linear contraction on continuous
functions. Linearity is transported through the injective actual L² map;
the sup bound comes from the finite maximum principle and genuine uniform
convergence on the nested dense vertex sets. No sup approximate identity
or continuous-space semigroup is assumed. -/

namespace IGS.Sec31

open Filter Topology
noncomputable section

theorem exists_continuousLinearMap_of_continuous_representatives
    {Space Ambient : Type*} [MetricSpace Space] [CompactSpace Space]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    (embedding : C(Space, ℝ) →L[ℝ] Ambient) (embeddingInjective : Function.Injective embedding)
    (operator : Ambient →L[ℝ] Ambient)
    (representativeExists : ∀ function : C(Space, ℝ), ∃ representative : C(Space, ℝ),
      embedding representative = operator (embedding function) ∧ ‖representative‖ ≤ ‖function‖) :
    ∃ resolver : C(Space, ℝ) →L[ℝ] C(Space, ℝ), ‖resolver‖ ≤ 1 ∧
      ∀ function, embedding (resolver function) = operator (embedding function) := by
  choose representatives representations bounds using representativeExists
  let linear : C(Space, ℝ) →ₗ[ℝ] C(Space, ℝ) := {
    toFun := representatives
    map_add' := by
      intro first second
      apply embeddingInjective
      calc
        embedding (representatives (first + second)) = operator (embedding (first + second)) :=
          representations (first + second)
        _ = operator (embedding first) + operator (embedding second) := by simp only [map_add]
        _ = embedding (representatives first) + embedding (representatives second) :=
          congrArg₂ (fun first second : Ambient => first + second)
            (representations first).symm (representations second).symm
        _ = embedding (representatives first + representatives second) := (map_add embedding _ _).symm
    map_smul' := by
      intro scalar function
      apply embeddingInjective
      calc
        embedding (representatives (scalar • function)) = operator (embedding (scalar • function)) :=
          representations (scalar • function)
        _ = scalar • operator (embedding function) := by simp only [map_smul]
        _ = scalar • embedding (representatives function) :=
          congrArg (fun value : Ambient => scalar • value) (representations function).symm
        _ = embedding (scalar • representatives function) := (map_smul embedding _ _).symm }
  let resolver := linear.mkContinuous 1 (fun function => by
    simpa only [one_mul] using bounds function)
  refine ⟨resolver, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro function
    change ‖representatives function‖ ≤ 1 * ‖function‖
    simpa only [one_mul] using bounds function
  · intro function
    exact representations function

end
end IGS.Sec31

#print axioms IGS.Sec31.exists_continuousLinearMap_of_continuous_representatives

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

variable {K : ℕ}

theorem xiContinuous_uniform_limit_norm_le
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected)
    (distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected)
    (values : (level : ℕ) → XiVtx system level → ℝ)
    (limit : C(parameters.LimitSpace, ℝ)) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (valuesBound : ∀ level vertex, |values level vertex| ≤ bound)
    (uniformConvergence : Tendsto (fun level => ‖fun vertex : XiVtx system level =>
      values level vertex - limit (parameters.vertexEmbedding level vertex)‖) atTop (nhds 0)) :
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
    letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair
    ‖limit‖ ≤ bound := by
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  apply (ContinuousMap.norm_le limit boundNonnegative).mpr
  intro point
  have dense := xiCompletionUnionEmbedding_denseRange system rulesConnected parameters.lengths
    parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair
  refine dense.induction_on (p := fun location => ‖limit location‖ ≤ bound) point
    (isClosed_le limit.continuous.norm continuous_const) ?_
  intro vertex
  obtain ⟨coarse, membership⟩ := xiVertexUnion_exhausted system vertex
  obtain ⟨finiteVertex, representation⟩ := membership
  apply le_of_forall_pos_le_add
  intro tolerance tolerancePositive
  obtain ⟨level, small, afterCoarse⟩ :=
    ((uniformConvergence.eventually_lt_const tolerancePositive).and (eventually_ge_atTop coarse)).exists
  let later := xiVertexInclusion system coarse level afterCoarse finiteVertex
  have embeddingEquality : parameters.vertexEmbedding level later =
      xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair vertex := by
    change xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair
      (xiVertexEmbedding system level later) = _
    dsimp only [later]
    rw [xiVertexEmbedding_inclusion, representation]
  have errorBound : |values level later - limit
      (xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair vertex)| ≤
      ‖fun target : XiVtx system level => values level target - limit (parameters.vertexEmbedding level target)‖ := by
    rw [← embeddingEquality]
    simpa only [Real.norm_eq_abs] using
      norm_le_pi_norm (fun target : XiVtx system level =>
        values level target - limit (parameters.vertexEmbedding level target)) later
  have triangle : |limit (xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair vertex)| ≤
      |values level later - limit (xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair vertex)| +
      |values level later| := by
    simpa only [sub_zero, abs_sub_comm] using abs_sub_le
      (limit (xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair vertex))
      (values level later) 0
  rw [Real.norm_eq_abs]
  linarith [valuesBound level later]

#print axioms EIGS.xiContinuous_uniform_limit_norm_le

def XiContinuousResolventContractionProperties (system : EIGSData K)
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
          solution level vertex - resolver function (parameters.vertexEmbedding level vertex)‖) atTop (nhds 0)

theorem xiContinuousResolventContractionProperties_of_uniform (system : EIGSData K)
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
    (uniformProperties : XiNativeUniformResolventProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive) :
    XiContinuousResolventContractionProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
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
  dsimp only [XiNativeUniformResolventProperties, XiContinuousResolventContractionProperties]
    at uniformProperties ⊢
  obtain ⟨originalDense, uniformProperties⟩ := uniformProperties
  refine ⟨originalDense, ?_⟩
  intro step stepPositive stepAtMostOne
  let operator := QuadraticEnergySpace.smallStepResolvent originalDomain originalForm nonnegative closable
    originalDense step stepPositive stepAtMostOne
  choose limits classes unique convergence using
    (fun function : C(parameters.LimitSpace, ℝ) => uniformProperties step stepPositive stepAtMostOne function)
  have limitsNorm (function : C(parameters.LimitSpace, ℝ)) : ‖limits function‖ ≤ ‖function‖ := by
    let forcing := fun level => core.restrict level (BoundedContinuousFunction.mkOfCompact function)
    let values : (level : ℕ) → XiVtx system level → ℝ := fun level vertex =>
      xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive (forcing level) vertex
    have forcingBound (level : ℕ) : ‖fun vertex : XiVtx system level => forcing level vertex‖ ≤ ‖function‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro vertex
      dsimp only [forcing]
      rw [xiSpeedL2Core_restrict_eq_finiteSpeedL2, xiFiniteSpeedL2_apply system rulesConnected]
      exact function.norm_coe_le_norm _
    have valuesBound (level : ℕ) (vertex : XiVtx system level) : |values level vertex| ≤ ‖function‖ :=
      (xiNativeFiniteResolvent_sup_bound system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive
        (forcing level) vertex).trans (forcingBound level)
    exact xiContinuous_uniform_limit_norm_le system rulesConnected parameters distanceGreaterThanOne
      values (limits function) ‖function‖ (norm_nonneg _) valuesBound (convergence function)
  have representativeWitness (function : C(parameters.LimitSpace, ℝ)) :
      ∃ representative : C(parameters.LimitSpace, ℝ),
        xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass representative =
          operator (xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass function) ∧
        ‖representative‖ ≤ ‖function‖ := by
    exact ⟨limits function, classes function, limitsNorm function⟩
  have embeddingInjective := xiContinuousL2Map_injective system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  obtain ⟨resolver, resolverNorm, representations⟩ :=
    exists_continuousLinearMap_of_continuous_representatives
      (xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
      embeddingInjective operator representativeWitness
  refine ⟨resolver, resolverNorm, ?_⟩
  intro function
  have resolverEquality : resolver function = limits function := by
    apply embeddingInjective
    exact (representations function).trans (classes function).symm
  refine ⟨representations function, ?_⟩
  exact Eq.mpr (congrArg (fun representative : C(parameters.LimitSpace, ℝ) =>
    Tendsto (fun level => ‖fun vertex : XiVtx system level =>
      xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive
        (core.restrict level (BoundedContinuousFunction.mkOfCompact function)) vertex -
      representative (parameters.vertexEmbedding level vertex)‖) atTop (nhds 0)) resolverEquality)
    (convergence function)

theorem exists_xiContinuousResolventContraction_of_rules (system : EIGSData K)
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
      XiContinuousResolventContractionProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, uniformProperties⟩ :=
    exists_xiNativeUniformResolvent_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiContinuousResolventContractionProperties_of_uniform system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair normalization normalizationPositive uniformProperties

end
end EIGS

#print axioms EIGS.xiContinuousResolventContractionProperties_of_uniform
#print axioms EIGS.exists_xiContinuousResolventContraction_of_rules
