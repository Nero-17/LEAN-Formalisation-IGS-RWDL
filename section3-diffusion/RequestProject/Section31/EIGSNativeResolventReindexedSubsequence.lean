import RequestProject.Section31.FiniteBasisReindexedCompactness

/-! Every strictly increasing selection of actual graph levels admits a
further subsequence of native resolvents converging uniformly on all of its
vertices to a continuous function. The finite-basis approximation and all
geometric inputs are filled from the actual rules. Identification of this
limit, and therefore convergence of the full sequence, are separate. -/

open MeasureTheory Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 4000000

namespace EIGS

variable {K : ℕ}

theorem xiNativeFiniteResolvent_exists_uniform_subsequence_along
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
      ∀ (levels : ℕ → ℕ), StrictMono levels →
      ∃ selection : ℕ → ℕ, StrictMono selection ∧ ∃ limit : C(parameters.LimitSpace, ℝ),
        Tendsto (fun index => ‖fun vertex : XiVtx system (levels (selection index)) =>
          xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
            mass (levels (selection index)) (system.resistanceSpectralRadius rulesConnected distancePositive)
            normalization
            (system.resistanceSpectralRadius_positive_eigenpair rulesConnected distancePositive).1.le
            normalizationPositive.le step stepPositive (forcing (levels (selection index))) vertex -
          limit (parameters.vertexEmbedding (levels (selection index)) vertex)‖) atTop (nhds 0) := by
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
  intro step stepPositive forcing bound boundNonnegative forcingBound levels levelsStrict
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
  have result := IGS.Sec31.uniform_subsequence_of_reindexed_finite_basis_approximations
    parameters.vertexEmbedding embeddingsNested embeddingsDense values basis coordinates coordinatesBound
    (fun depth => accuracy depth * bound)
    (fun depth => mul_nonneg (accuracyPositive depth).le boundNonnegative) errorsConverge basisError levels levelsStrict
  exact result

end EIGS

#print axioms EIGS.xiNativeFiniteResolvent_exists_uniform_subsequence_along
