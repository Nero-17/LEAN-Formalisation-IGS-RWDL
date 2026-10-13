import RequestProject.Section2MetricGeometry
import RequestProject.Section31.EIGSTraceEnergy
import Mathlib.Topology.MetricSpace.Completion

/-! The actual Xi vertex union, with the distance induced by the positive path
eigenvector. Every finite-level embedding is isometric for the prescribed
rescaling. The common metric and its completion are constructed here; their
compactness is a further geometric theorem, not an assumption in this file. -/

namespace EIGS

variable {K : ℕ}

def xiLiftVertices (system : EIGSData K) (initialLevel : ℕ) :
    (offset : ℕ) → XiVtx system initialLevel → XiVtx system (initialLevel + offset)
  | 0, vertex => vertex
  | offset + 1, vertex => Sum.inl (xiLiftVertices system initialLevel offset vertex)

@[simp] theorem xiVertexEmbedding_lift (system : EIGSData K) (initialLevel offset : ℕ)
    (vertex : XiVtx system initialLevel) :
    xiVertexEmbedding system (initialLevel + offset) (xiLiftVertices system initialLevel offset vertex) =
      xiVertexEmbedding system initialLevel vertex := by
  induction offset with
  | zero => rfl
  | succ offset induction_hypothesis =>
    simpa only [Nat.add_succ, xiLiftVertices, xiVertexEmbedding_old] using induction_hypothesis

theorem xiLevelVertices_mono (system : EIGSData K) {initialLevel finalLevel : ℕ}
    (levelsOrdered : initialLevel ≤ finalLevel) :
    xiLevelVertices system initialLevel ⊆ xiLevelVertices system finalLevel := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le levelsOrdered
  rintro vertex ⟨finiteVertex, rfl⟩
  exact ⟨xiLiftVertices system initialLevel offset finiteVertex,
    xiVertexEmbedding_lift system initialLevel offset finiteVertex⟩

theorem xiUnionBirth_mem (system : EIGSData K) (vertex : XiVertexUnion system) :
    vertex ∈ xiLevelVertices system (xiUnionBirth system vertex) := by
  cases vertex with
  | inl originalVertex => exact ⟨originalVertex, rfl⟩
  | inr privateVertex =>
    obtain ⟨level, newVertex⟩ := privateVertex
    exact ⟨Sum.inr newVertex, rfl⟩

theorem xiVertexUnion_mem_level (system : EIGSData K) (vertex : XiVertexUnion system)
    (level : ℕ) (birthBound : xiUnionBirth system vertex ≤ level) :
    vertex ∈ xiLevelVertices system level :=
  xiLevelVertices_mono system birthBound (xiUnionBirth_mem system vertex)

noncomputable def xiVertexAtLevel (system : EIGSData K) (vertex : XiVertexUnion system)
    (level : ℕ) (birthBound : xiUnionBirth system vertex ≤ level) : XiVtx system level :=
  Classical.choose (xiVertexUnion_mem_level system vertex level birthBound)

@[simp] theorem xiVertexEmbedding_atLevel (system : EIGSData K) (vertex : XiVertexUnion system)
    (level : ℕ) (birthBound : xiUnionBirth system vertex ≤ level) :
    xiVertexEmbedding system level (xiVertexAtLevel system vertex level birthBound) = vertex :=
  Classical.choose_spec (xiVertexUnion_mem_level system vertex level birthBound)

section MetricEigenpair

variable (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (ratePositive : 0 < rate)
    (eigenpair : (system.ruleFamily ruleConnected).metricLengths lengths = rate • lengths)

include ruleConnected lengthsPositive ratePositive eigenpair

theorem xiScaledWeightedDistance_lift (initialLevel offset : ℕ)
    (source sink : XiVtx system initialLevel) :
    xiScaledWeightedDistance system lengths rate (initialLevel + offset)
        (xiLiftVertices system initialLevel offset source)
        (xiLiftVertices system initialLevel offset sink) =
      xiScaledWeightedDistance system lengths rate initialLevel source sink := by
  induction offset with
  | zero => rfl
  | succ offset induction_hypothesis =>
    simpa only [Nat.add_succ, xiLiftVertices,
      xiScaledWeightedDistance_old system ruleConnected (fun colour => (lengthsPositive colour).le)
        ratePositive eigenpair] using induction_hypothesis

theorem xiScaledWeightedDistance_coherent {initialLevel finalLevel : ℕ}
    (levelsOrdered : initialLevel ≤ finalLevel)
    (source sink : XiVtx system initialLevel) (finalSource finalSink : XiVtx system finalLevel)
    (sourceEquality : xiVertexEmbedding system initialLevel source =
      xiVertexEmbedding system finalLevel finalSource)
    (sinkEquality : xiVertexEmbedding system initialLevel sink =
      xiVertexEmbedding system finalLevel finalSink) :
    xiScaledWeightedDistance system lengths rate finalLevel finalSource finalSink =
      xiScaledWeightedDistance system lengths rate initialLevel source sink := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le levelsOrdered
  have sourceLift : finalSource = xiLiftVertices system initialLevel offset source :=
    xiVertexEmbedding_injective system _ (sourceEquality.symm.trans
      (xiVertexEmbedding_lift system initialLevel offset source).symm)
  have sinkLift : finalSink = xiLiftVertices system initialLevel offset sink :=
    xiVertexEmbedding_injective system _ (sinkEquality.symm.trans
      (xiVertexEmbedding_lift system initialLevel offset sink).symm)
  rw [sourceLift, sinkLift]
  exact xiScaledWeightedDistance_lift system ruleConnected lengths lengthsPositive rate ratePositive
    eigenpair initialLevel offset source sink

noncomputable def xiUnionDistance (source sink : XiVertexUnion system) : ℝ :=
  xiScaledWeightedDistance system lengths rate
    (max (xiUnionBirth system source) (xiUnionBirth system sink))
    (xiVertexAtLevel system source _ (le_max_left _ _))
    (xiVertexAtLevel system sink _ (le_max_right _ _))

theorem xiUnionDistance_eq_atLevel (source sink : XiVertexUnion system) (level : ℕ)
    (sourceBirth : xiUnionBirth system source ≤ level)
    (sinkBirth : xiUnionBirth system sink ≤ level) :
    xiUnionDistance system lengths rate source sink =
      xiScaledWeightedDistance system lengths rate level
        (xiVertexAtLevel system source level sourceBirth)
        (xiVertexAtLevel system sink level sinkBirth) := by
  unfold xiUnionDistance
  apply Eq.symm
  apply xiScaledWeightedDistance_coherent system ruleConnected lengths lengthsPositive rate
    ratePositive eigenpair (max_le sourceBirth sinkBirth)
  · simp only [xiVertexEmbedding_atLevel]
  · simp only [xiVertexEmbedding_atLevel]

theorem xiUnionDistance_embedding (level : ℕ) (source sink : XiVtx system level) :
    xiUnionDistance system lengths rate (xiVertexEmbedding system level source)
        (xiVertexEmbedding system level sink) =
      xiScaledWeightedDistance system lengths rate level source sink := by
  rw [xiUnionDistance_eq_atLevel system ruleConnected lengths lengthsPositive rate ratePositive eigenpair
    _ _ level (xiUnionBirth_embedding_le system level source) (xiUnionBirth_embedding_le system level sink)]
  congr 1
  · exact xiVertexEmbedding_injective system level (xiVertexEmbedding_atLevel system _ _ _)
  · exact xiVertexEmbedding_injective system level (xiVertexEmbedding_atLevel system _ _ _)

theorem xiUnionDistance_self (vertex : XiVertexUnion system) :
    xiUnionDistance system lengths rate vertex vertex = 0 := by
  rw [xiUnionDistance_eq_atLevel system ruleConnected lengths lengthsPositive rate ratePositive eigenpair
    vertex vertex (xiUnionBirth system vertex) le_rfl le_rfl]
  simp [xiScaledWeightedDistance,
    Network.weightedDistance_self _ (fun colour => (lengthsPositive colour).le)]

theorem xiUnionDistance_symm (source sink : XiVertexUnion system) :
    xiUnionDistance system lengths rate source sink = xiUnionDistance system lengths rate sink source := by
  let level := max (xiUnionBirth system source) (xiUnionBirth system sink)
  have sourceBirth : xiUnionBirth system source ≤ level := le_max_left _ _
  have sinkBirth : xiUnionBirth system sink ≤ level := le_max_right _ _
  rw [xiUnionDistance_eq_atLevel system ruleConnected lengths lengthsPositive rate ratePositive eigenpair
      source sink level sourceBirth sinkBirth,
    xiUnionDistance_eq_atLevel system ruleConnected lengths lengthsPositive rate ratePositive eigenpair
      sink source level sinkBirth sourceBirth]
  unfold xiScaledWeightedDistance
  rw [Network.weightedDistance_symm (XiNetwork system level) (xiSimpleGraph_connected system ruleConnected level)
    (fun colour => (lengthsPositive colour).le)]

theorem xiUnionDistance_triangle (source middle sink : XiVertexUnion system) :
    xiUnionDistance system lengths rate source sink ≤
      xiUnionDistance system lengths rate source middle + xiUnionDistance system lengths rate middle sink := by
  let level := max (xiUnionBirth system source)
    (max (xiUnionBirth system middle) (xiUnionBirth system sink))
  have sourceBirth : xiUnionBirth system source ≤ level := le_max_left _ _
  have middleBirth : xiUnionBirth system middle ≤ level := (le_max_left _ _).trans (le_max_right _ _)
  have sinkBirth : xiUnionBirth system sink ≤ level := (le_max_right _ _).trans (le_max_right _ _)
  rw [xiUnionDistance_eq_atLevel system ruleConnected lengths lengthsPositive rate ratePositive eigenpair
      source sink level sourceBirth sinkBirth,
    xiUnionDistance_eq_atLevel system ruleConnected lengths lengthsPositive rate ratePositive eigenpair
      source middle level sourceBirth middleBirth,
    xiUnionDistance_eq_atLevel system ruleConnected lengths lengthsPositive rate ratePositive eigenpair
      middle sink level middleBirth sinkBirth]
  unfold xiScaledWeightedDistance
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left
    ((XiNetwork system level).weightedDistance_triangle (xiSimpleGraph_connected system ruleConnected level)
      (fun colour => (lengthsPositive colour).le) _ _ _) (pow_nonneg (inv_nonneg.mpr ratePositive.le) _)

theorem xiUnionDistance_pos (source sink : XiVertexUnion system) (distinct : source ≠ sink) :
    0 < xiUnionDistance system lengths rate source sink := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  let level := max (xiUnionBirth system source) (xiUnionBirth system sink)
  have sourceBirth : xiUnionBirth system source ≤ level := le_max_left _ _
  have sinkBirth : xiUnionBirth system sink ≤ level := le_max_right _ _
  rw [xiUnionDistance_eq_atLevel system ruleConnected lengths lengthsPositive rate ratePositive eigenpair
    source sink level sourceBirth sinkBirth]
  apply mul_pos (pow_pos (inv_pos.mpr ratePositive) _)
  apply Network.weightedDistance_pos (XiNetwork system level) (xiSimpleGraph_connected system ruleConnected level) lengthsPositive
  intro equality
  apply distinct
  simpa only [xiVertexEmbedding_atLevel] using congrArg (xiVertexEmbedding system level) equality

/-- The concrete common metric, with no requested conclusion among its premises. -/
noncomputable def xiUnionMetricSpace : MetricSpace (XiVertexUnion system) where
  dist := xiUnionDistance system lengths rate
  dist_self := xiUnionDistance_self system ruleConnected lengths lengthsPositive rate ratePositive eigenpair
  dist_comm := xiUnionDistance_symm system ruleConnected lengths lengthsPositive rate ratePositive eigenpair
  dist_triangle := xiUnionDistance_triangle system ruleConnected lengths lengthsPositive rate ratePositive eigenpair
  eq_of_dist_eq_zero := by
    intro source sink equality
    by_contra distinct
    exact (ne_of_gt (xiUnionDistance_pos system ruleConnected lengths lengthsPositive rate ratePositive
      eigenpair source sink distinct)) equality

/-- The actual finite-level scaled weighted metric. -/
noncomputable def xiLevelMetricSpace (level : ℕ) : MetricSpace (XiVtx system level) where
  dist := xiScaledWeightedDistance system lengths rate level
  dist_self := by
    intro vertex
    simp [xiScaledWeightedDistance,
      Network.weightedDistance_self _ (fun colour => (lengthsPositive colour).le)]
  dist_comm := by
    intro source sink
    unfold xiScaledWeightedDistance
    rw [Network.weightedDistance_symm (XiNetwork system level) (xiSimpleGraph_connected system ruleConnected level)
      (fun colour => (lengthsPositive colour).le)]
  dist_triangle := by
    intro source middle sink
    unfold xiScaledWeightedDistance
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left
      ((XiNetwork system level).weightedDistance_triangle (xiSimpleGraph_connected system ruleConnected level)
        (fun colour => (lengthsPositive colour).le) _ _ _) (pow_nonneg (inv_nonneg.mpr ratePositive.le) _)
  eq_of_dist_eq_zero := by
    letI : Nonempty (Fin K) := ⟨system.initCol⟩
    intro source sink equality
    by_contra distinct
    exact (ne_of_gt (mul_pos (pow_pos (inv_pos.mpr ratePositive) level)
      ((XiNetwork system level).weightedDistance_pos (xiSimpleGraph_connected system ruleConnected level)
        lengthsPositive source sink distinct))) equality

theorem xiVertexEmbedding_isometry (level : ℕ) :
    letI := xiLevelMetricSpace system ruleConnected lengths lengthsPositive rate ratePositive level
    letI := xiUnionMetricSpace system ruleConnected lengths lengthsPositive rate ratePositive eigenpair
    Isometry (xiVertexEmbedding system level) := by
  letI := xiLevelMetricSpace system ruleConnected lengths lengthsPositive rate ratePositive level
  letI := xiUnionMetricSpace system ruleConnected lengths lengthsPositive rate ratePositive eigenpair
  exact Isometry.of_dist_eq (xiUnionDistance_embedding system ruleConnected lengths lengthsPositive
    rate ratePositive eigenpair level)

noncomputable def XiMetricCompletion : Type := by
  letI := xiUnionMetricSpace system ruleConnected lengths lengthsPositive rate ratePositive eigenpair
  exact UniformSpace.Completion (XiVertexUnion system)

noncomputable instance xiCompletionMetricSpace :
    MetricSpace (XiMetricCompletion system ruleConnected lengths lengthsPositive rate ratePositive eigenpair) := by
  letI := xiUnionMetricSpace system ruleConnected lengths lengthsPositive rate ratePositive eigenpair
  change MetricSpace (UniformSpace.Completion (XiVertexUnion system))
  infer_instance

instance xiCompletionCompleteSpace :
    CompleteSpace (XiMetricCompletion system ruleConnected lengths lengthsPositive rate ratePositive eigenpair) := by
  letI := xiUnionMetricSpace system ruleConnected lengths lengthsPositive rate ratePositive eigenpair
  change CompleteSpace (UniformSpace.Completion (XiVertexUnion system))
  infer_instance

noncomputable def xiCompletionUnionEmbedding : XiVertexUnion system →
    XiMetricCompletion system ruleConnected lengths lengthsPositive rate ratePositive eigenpair := by
  letI := xiUnionMetricSpace system ruleConnected lengths lengthsPositive rate ratePositive eigenpair
  exact fun vertex => (vertex : UniformSpace.Completion (XiVertexUnion system))

theorem xiCompletionUnionEmbedding_isometry :
    letI := xiUnionMetricSpace system ruleConnected lengths lengthsPositive rate ratePositive eigenpair
    Isometry (xiCompletionUnionEmbedding system ruleConnected lengths lengthsPositive rate ratePositive eigenpair) := by
  letI := xiUnionMetricSpace system ruleConnected lengths lengthsPositive rate ratePositive eigenpair
  exact UniformSpace.Completion.coe_isometry

theorem xiCompletionUnionEmbedding_denseRange :
    DenseRange (xiCompletionUnionEmbedding system ruleConnected lengths lengthsPositive rate ratePositive eigenpair) := by
  letI := xiUnionMetricSpace system ruleConnected lengths lengthsPositive rate ratePositive eigenpair
  exact UniformSpace.Completion.denseRange_coe

noncomputable def xiCompletionEmbedding (level : ℕ) : XiVtx system level →
    XiMetricCompletion system ruleConnected lengths lengthsPositive rate ratePositive eigenpair :=
  xiCompletionUnionEmbedding system ruleConnected lengths lengthsPositive rate ratePositive eigenpair ∘
    xiVertexEmbedding system level

theorem xiCompletionEmbedding_isometry (level : ℕ) :
    letI := xiLevelMetricSpace system ruleConnected lengths lengthsPositive rate ratePositive level
    Isometry (xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate ratePositive eigenpair level) := by
  letI := xiLevelMetricSpace system ruleConnected lengths lengthsPositive rate ratePositive level
  letI := xiUnionMetricSpace system ruleConnected lengths lengthsPositive rate ratePositive eigenpair
  exact (xiCompletionUnionEmbedding_isometry system ruleConnected lengths lengthsPositive rate ratePositive eigenpair).comp
    (xiVertexEmbedding_isometry system ruleConnected lengths lengthsPositive rate ratePositive eigenpair level)

end MetricEigenpair

end EIGS

#print axioms EIGS.xiScaledWeightedDistance_coherent
#print axioms EIGS.xiUnionDistance_embedding
#print axioms EIGS.xiUnionMetricSpace
#print axioms EIGS.xiVertexEmbedding_isometry
#print axioms EIGS.xiCompletionEmbedding_isometry
#print axioms EIGS.xiCompletionUnionEmbedding_denseRange
