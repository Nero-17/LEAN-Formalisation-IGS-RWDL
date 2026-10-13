import RequestProject.Section31.EIGSNativeResolventFiniteGridApproximation
import RequestProject.Section31.VaryingProjectionCompactness
import RequestProject.Section31.EIGSIncidentStarCompletionMesh
import Mathlib.Topology.UniformSpace.CompactConvergence

/-! Uniform subsequences of actual native resolvents on the changing finite
vertex sets. Bounded finite basis coordinates are extracted simultaneously;
compatibility and density of the actual vertex embeddings transfer the
comparison to the completion. Strong-limit identification is separate. -/

open MeasureTheory Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 4000000

namespace IGS.Sec31

def finiteBasisCombination {Space Index : Type*} [TopologicalSpace Space] [Fintype Index]
    (basis : Index → C(Space, ℝ)) (coordinates : Index → ℝ) : C(Space, ℝ) :=
  ∑ index, coordinates index • basis index

theorem finiteBasisCombination_apply {Space Index : Type*} [TopologicalSpace Space] [Fintype Index]
    (basis : Index → C(Space, ℝ)) (coordinates : Index → ℝ) (point : Space) :
    finiteBasisCombination basis coordinates point = ∑ index, coordinates index * basis index point := by
  simp [finiteBasisCombination, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]

theorem uniform_subsequence_of_finite_basis_approximations
    {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    {LevelVertex : ℕ → Type*} [∀ level, Fintype (LevelVertex level)]
    (embeddings : (level : ℕ) → LevelVertex level → Space)
    (nested : ∀ coarse fine, coarse ≤ fine → ∀ vertex : LevelVertex coarse,
      ∃ later : LevelVertex fine, embeddings fine later = embeddings coarse vertex)
    (dense : DenseRange (fun point : (level : ℕ) × LevelVertex level =>
      embeddings point.1 point.2))
    (values : (level : ℕ) → LevelVertex level → ℝ)
    {Coordinates : ℕ → Type*} [∀ depth, Fintype (Coordinates depth)]
    (basis : (depth : ℕ) → Coordinates depth → C(Space, ℝ))
    (coordinates : (depth : ℕ) → ℕ → Coordinates depth → ℝ)
    (bounded : ∀ depth, ∃ bound : ℝ, ∀ level, ‖coordinates depth level‖ ≤ bound)
    (errors : ℕ → ℝ) (errorsNonnegative : ∀ depth, 0 ≤ errors depth)
    (errorsConverge : Tendsto errors atTop (nhds 0))
    (approximation : ∀ depth, ∀ᶠ level in atTop, ∀ vertex : LevelVertex level,
      |values level vertex - finiteBasisCombination (basis depth) (coordinates depth level)
        (embeddings level vertex)| ≤ errors depth) :
    ∃ selection : ℕ → ℕ, StrictMono selection ∧ ∃ limit : C(Space, ℝ),
      Tendsto (fun index => ‖fun vertex : LevelVertex (selection index) =>
        values (selection index) vertex - limit (embeddings (selection index) vertex)‖)
        atTop (nhds 0) := by
  obtain ⟨coordinateLimits, selection, selectionStrict, coordinateConvergence⟩ :=
    bounded_coordinates_common_subsequence (fun depth => Coordinates depth → ℝ) coordinates bounded
  have selectionTendsto := selectionStrict.tendsto_atTop
  let combinations : ℕ → ℕ → C(Space, ℝ) := fun depth index =>
    finiteBasisCombination (basis depth) (coordinates depth (selection index))
  let limits : ℕ → C(Space, ℝ) := fun depth =>
    finiteBasisCombination (basis depth) (coordinateLimits depth)
  have combinationConvergence (depth : ℕ) :
      Tendsto (combinations depth) atTop (nhds (limits depth)) := by
    have continuousCombination : Continuous
        (fun vector : Coordinates depth → ℝ => finiteBasisCombination (basis depth) vector) := by
      unfold finiteBasisCombination
      fun_prop
    exact continuousCombination.continuousAt.tendsto.comp (coordinateConvergence depth)
  have pointConvergence (depth : ℕ) (point : Space) :
      Tendsto (fun index => combinations depth index point) atTop (nhds (limits depth point)) :=
    (continuous_eval_const point).continuousAt.tendsto.comp (combinationConvergence depth)
  have pointDifference (first second : ℕ) (point : Space) :
      |limits first point - limits second point| ≤ errors first + errors second := by
    refine dense.induction_on
      (p := fun location => |limits first location - limits second location| ≤ errors first + errors second)
      point (isClosed_le (((limits first).continuous.sub (limits second).continuous).abs) continuous_const) ?_
    intro embedded
    obtain ⟨coarse, vertex⟩ := embedded
    apply le_of_tendsto ((pointConvergence first (embeddings coarse vertex)).sub
      (pointConvergence second (embeddings coarse vertex))).abs
    filter_upwards [selectionTendsto.eventually (approximation first),
      selectionTendsto.eventually (approximation second),
      selectionTendsto.eventually (eventually_ge_atTop coarse)]
      with index firstApproximation secondApproximation afterCoarse
    obtain ⟨later, embeddingEquality⟩ := nested coarse (selection index) afterCoarse vertex
    have firstBound := firstApproximation later
    have secondBound := secondApproximation later
    change |values (selection index) later - combinations first index
      (embeddings (selection index) later)| ≤ _ at firstBound
    change |values (selection index) later - combinations second index
      (embeddings (selection index) later)| ≤ _ at secondBound
    rw [embeddingEquality] at firstBound secondBound
    have triangle := abs_sub_le (combinations first index (embeddings coarse vertex))
      (values (selection index) later) (combinations second index (embeddings coarse vertex))
    rw [abs_sub_comm (combinations first index (embeddings coarse vertex))
      (values (selection index) later)] at triangle
    exact triangle.trans (add_le_add firstBound secondBound)
  have normDifference (first second : ℕ) :
      ‖limits first - limits second‖ ≤ errors first + errors second := by
    apply (ContinuousMap.norm_le _ (add_nonneg (errorsNonnegative first) (errorsNonnegative second))).mpr
    intro point
    simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs] using pointDifference first second point
  have limitsCauchy : CauchySeq limits := by
    apply Metric.cauchySeq_iff.mpr
    intro tolerance tolerancePositive
    obtain ⟨threshold, errorSmall⟩ := eventually_atTop.1
      (errorsConverge.eventually (gt_mem_nhds (show 0 < tolerance / 2 by positivity)))
    refine ⟨threshold, ?_⟩
    intro first afterFirst second afterSecond
    rw [dist_eq_norm]
    exact (normDifference first second).trans_lt
      (by linarith [errorSmall first afterFirst, errorSmall second afterSecond])
  obtain ⟨limit, limitConvergence⟩ := cauchySeq_tendsto_of_complete limitsCauchy
  have limitError (depth : ℕ) : ‖limits depth - limit‖ ≤ errors depth := by
    have leftConvergence : Tendsto (fun index => ‖limits depth - limits index‖)
        atTop (nhds ‖limits depth - limit‖) :=
      (tendsto_const_nhds.sub limitConvergence).norm
    have rightConvergence : Tendsto (fun index => errors depth + errors index)
        atTop (nhds (errors depth)) := by simpa using tendsto_const_nhds.add errorsConverge
    exact le_of_tendsto_of_tendsto leftConvergence rightConvergence
      (Eventually.of_forall (normDifference depth))
  refine ⟨selection, selectionStrict, limit, ?_⟩
  apply Metric.tendsto_atTop.mpr
  intro tolerance tolerancePositive
  obtain ⟨depth, depthSmall⟩ :=
    (errorsConverge.eventually (gt_mem_nhds (show 0 < tolerance / 3 by positivity))).exists
  have combinationErrorConverges : Tendsto (fun index => ‖combinations depth index - limits depth‖)
      atTop (nhds 0) := by
    simpa only [sub_self, norm_zero] using
      ((combinationConvergence depth).sub (tendsto_const_nhds (x := limits depth))).norm
  obtain ⟨threshold, estimates⟩ := eventually_atTop.1
    ((selectionTendsto.eventually (approximation depth)).and
      (combinationErrorConverges.eventually (gt_mem_nhds (show 0 < tolerance / 3 by positivity))))
  refine ⟨threshold, ?_⟩
  intro index afterThreshold
  obtain ⟨nativeApproximation, combinationSmall⟩ := estimates index afterThreshold
  have uniformBound : ‖fun vertex : LevelVertex (selection index) =>
      values (selection index) vertex - limit (embeddings (selection index) vertex)‖ ≤
      errors depth + ‖combinations depth index - limits depth‖ + ‖limits depth - limit‖ := by
    apply (pi_norm_le_iff_of_nonneg
      (add_nonneg (add_nonneg (errorsNonnegative depth) (norm_nonneg _)) (norm_nonneg _))).mpr
    intro vertex
    rw [Real.norm_eq_abs]
    have nativeBound := nativeApproximation vertex
    change |values (selection index) vertex - combinations depth index
      (embeddings (selection index) vertex)| ≤ _ at nativeBound
    have middleBound : |combinations depth index (embeddings (selection index) vertex) -
        limits depth (embeddings (selection index) vertex)| ≤ ‖combinations depth index - limits depth‖ := by
      simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs] using
        (combinations depth index - limits depth).norm_coe_le_norm (embeddings (selection index) vertex)
    have lastBound : |limits depth (embeddings (selection index) vertex) -
        limit (embeddings (selection index) vertex)| ≤ ‖limits depth - limit‖ := by
      simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs] using
        (limits depth - limit).norm_coe_le_norm (embeddings (selection index) vertex)
    have firstTriangle := abs_sub_le (values (selection index) vertex)
      (combinations depth index (embeddings (selection index) vertex)) (limit (embeddings (selection index) vertex))
    have secondTriangle := abs_sub_le (combinations depth index (embeddings (selection index) vertex))
      (limits depth (embeddings (selection index) vertex)) (limit (embeddings (selection index) vertex))
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  exact uniformBound.trans_lt (by linarith [limitError depth])

end IGS.Sec31

namespace EIGS

variable {K : ℕ}

theorem xiNativeFiniteResolvent_exists_uniform_subsequence
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (mass : XiMassParameters system) (normalization : ℝ)
    (normalizationPositive : 0 < normalization) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    ∀ (step : ℝ) (stepPositive : 0 < step)
      (forcing : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
      (bound : ℝ), 0 ≤ bound →
      (∀ level, ‖fun vertex : XiVtx system level => forcing level vertex‖ ≤ bound) →
      ∃ selection : ℕ → ℕ, StrictMono selection ∧ ∃ limit : C(parameters.LimitSpace, ℝ),
        Tendsto (fun index => ‖fun vertex : XiVtx system (selection index) =>
          xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
            mass (selection index) (system.resistanceSpectralRadius rulesConnected distancePositive)
            normalization
            (system.resistanceSpectralRadius_positive_eigenpair rulesConnected distancePositive).1.le
            normalizationPositive.le step stepPositive (forcing (selection index)) vertex -
          limit (parameters.vertexEmbedding (selection index) vertex)‖) atTop (nhds 0) := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  dsimp only
  have distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI : CompactSpace parameters.LimitSpace :=
    xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
  have resistancePositive := (system.resistanceSpectralRadius_positive_eigenpair
    rulesConnected distancePositive).1
  intro step stepPositive forcing bound boundNonnegative forcingBound
  let values : (level : ℕ) → XiVtx system level → ℝ := fun level vertex =>
    xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level (system.resistanceSpectralRadius rulesConnected distancePositive) normalization
      resistancePositive.le normalizationPositive.le step stepPositive (forcing level) vertex
  have valuesBound (level : ℕ) (vertex : XiVtx system level) : |values level vertex| ≤ bound :=
    (xiNativeFiniteResolvent_sup_bound system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level _ normalization resistancePositive.le normalizationPositive.le step stepPositive
        (forcing level) vertex).trans (forcingBound level)
  let accuracy : ℕ → ℝ := fun depth => 1 / ((depth : ℝ) + 1)
  have accuracyPositive (depth : ℕ) : 0 < accuracy depth := by dsimp [accuracy]; positivity
  choose coarse basis threshold approximation using
    (fun depth => xiNativeFiniteResolvent_finite_continuous_approximation system rulesConnected
      rulesLoopless rulesUnique plantingNonadjacent distancePositive mass normalization normalizationPositive
        step stepPositive (accuracy depth) (accuracyPositive depth))
  let coordinates : (depth : ℕ) → ℕ → XiVtx system (coarse depth) → ℝ := fun depth level =>
    if ordered : coarse depth ≤ level then
      fun vertex => values level (xiVertexInclusion system (coarse depth) level ordered vertex)
    else 0
  have coordinatesBound (depth : ℕ) : ∃ upper : ℝ, ∀ level, ‖coordinates depth level‖ ≤ upper := by
    refine ⟨bound, ?_⟩
    intro level
    dsimp only [coordinates]
    split_ifs with ordered
    · apply (pi_norm_le_iff_of_nonneg boundNonnegative).mpr
      intro vertex
      simpa only [Real.norm_eq_abs] using
        valuesBound level (xiVertexInclusion system (coarse depth) level ordered vertex)
    · simpa using boundNonnegative
  have embeddingsNested : ∀ first second, first ≤ second → ∀ vertex : XiVtx system first,
      ∃ later : XiVtx system second,
        parameters.vertexEmbedding second later = parameters.vertexEmbedding first vertex := by
    intro first second ordered vertex
    refine ⟨xiVertexInclusion system first second ordered vertex, ?_⟩
    simp only [XiPathMetricData.vertexEmbedding, xiCompletionEmbedding, Function.comp_apply,
      xiVertexEmbedding_inclusion]
  have embeddingsDense : DenseRange (fun point : (level : ℕ) × XiVtx system level =>
      parameters.vertexEmbedding point.1 point.2) := by
    change Dense (Set.range (fun point : (level : ℕ) × XiVtx system level =>
      parameters.vertexEmbedding point.1 point.2))
    have rangeEquality : Set.range (fun point : (level : ℕ) × XiVtx system level =>
        parameters.vertexEmbedding point.1 point.2) =
      Set.range (xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair) := by
      ext point
      constructor
      · rintro ⟨⟨level, vertex⟩, rfl⟩
        exact ⟨xiVertexEmbedding system level vertex, rfl⟩
      · rintro ⟨vertex, rfl⟩
        obtain ⟨level, membership⟩ := xiVertexUnion_exhausted system vertex
        obtain ⟨finiteVertex, representation⟩ := membership
        refine ⟨⟨level, finiteVertex⟩, ?_⟩
        change xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair
          (xiVertexEmbedding system level finiteVertex) = _
        rw [representation]
    rw [rangeEquality]
    exact xiCompletionUnionEmbedding_denseRange system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair
  have errorsConverge : Tendsto (fun depth => accuracy depth * bound) atTop (nhds 0) := by
    simpa only [accuracy, zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const bound
  have basisError (depth : ℕ) : ∀ᶠ level in atTop, ∀ vertex : XiVtx system level,
      |values level vertex - IGS.Sec31.finiteBasisCombination (basis depth) (coordinates depth level)
        (parameters.vertexEmbedding level vertex)| ≤ accuracy depth * bound := by
    apply eventually_atTop.mpr
    refine ⟨max (coarse depth) (threshold depth), ?_⟩
    intro level afterThreshold vertex
    have ordered : coarse depth ≤ level := (le_max_left _ _).trans afterThreshold
    have afterFine : threshold depth ≤ level := (le_max_right _ _).trans afterThreshold
    obtain ⟨steps, rfl⟩ := Nat.exists_eq_add_of_le ordered
    have coordinateEquality : coordinates depth (coarse depth + steps) =
        (fun boundary => values (coarse depth + steps) (xiForward system (coarse depth) steps boundary)) := by
      funext boundary
      dsimp only [coordinates]
      rw [dif_pos (Nat.le_add_right _ _), xiVertexInclusion_eq_forward]
    rw [coordinateEquality, IGS.Sec31.finiteBasisCombination_apply]
    have actualApproximation := approximation depth steps afterFine (forcing (coarse depth + steps)) vertex
    dsimp only at actualApproximation
    apply actualApproximation.trans
    exact mul_le_mul_of_nonneg_left (forcingBound (coarse depth + steps)) (accuracyPositive depth).le
  have result := IGS.Sec31.uniform_subsequence_of_finite_basis_approximations
    parameters.vertexEmbedding embeddingsNested embeddingsDense values basis coordinates coordinatesBound
    (fun depth => accuracy depth * bound)
    (fun depth => mul_nonneg (accuracyPositive depth).le boundNonnegative) errorsConverge basisError
  exact result

end EIGS

#print axioms IGS.Sec31.finiteBasisCombination_apply
#print axioms IGS.Sec31.uniform_subsequence_of_finite_basis_approximations
#print axioms EIGS.xiNativeFiniteResolvent_exists_uniform_subsequence
