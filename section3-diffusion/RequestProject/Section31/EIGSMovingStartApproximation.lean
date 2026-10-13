import RequestProject.Section31.EIGSMetricOfRules
import RequestProject.Section31.EIGSVertexInclusion
import Mathlib.Data.Finset.Max

/-! Every point of the actual metric completion can be approached by a
vertex at every level. This supplies moving starts for each limiting point,
rather than merely assuming that such a sequence has been given. -/

open Filter Topology

namespace IGS.Sec31

theorem exists_level_points_tendsto_of_nested_dense
    {Space : Type*} [MetricSpace Space]
    {Vertex : ℕ → Type*} [∀ level, Fintype (Vertex level)] [∀ level, Nonempty (Vertex level)]
    (embedding : ∀ level, Vertex level → Space)
    (nested : ∀ first second, first ≤ second → ∀ vertex : Vertex first,
      ∃ later : Vertex second, embedding second later = embedding first vertex)
    (dense : DenseRange (fun point : (level : ℕ) × Vertex level => embedding point.1 point.2))
    (point : Space) :
    ∃ starts : ∀ level, Vertex level,
      Tendsto (fun level => embedding level (starts level)) atTop (𝓝 point) := by
  classical
  have nearest : ∀ level, ∃ vertex : Vertex level,
      ∀ other : Vertex level, dist (embedding level vertex) point ≤ dist (embedding level other) point := by
    intro level
    obtain ⟨vertex, _, minimal⟩ := Finset.exists_min_image Finset.univ
      (fun vertex : Vertex level => dist (embedding level vertex) point) Finset.univ_nonempty
    exact ⟨vertex, fun other => minimal other (Finset.mem_univ other)⟩
  choose starts nearestBound using nearest
  refine ⟨starts, Metric.tendsto_atTop.mpr ?_⟩
  intro error errorPositive
  obtain ⟨⟨coarseLevel, vertex⟩, near⟩ := dense.exists_dist_lt point errorPositive
  refine ⟨coarseLevel, ?_⟩
  intro level ordered
  obtain ⟨later, equality⟩ := nested coarseLevel level ordered vertex
  apply (nearestBound level later).trans_lt
  rw [equality, dist_comm]
  exact near

end IGS.Sec31

namespace EIGS.XiPathMetricData

variable {K : ℕ} {system : EIGSData K}
variable {rulesConnected : ∀ colour, (ruleSG system colour).Connected}

theorem exists_moving_starts (parameters : XiPathMetricData system rulesConnected)
    (point : parameters.LimitSpace) :
    ∃ starts : ∀ level, XiVtx system level,
      Tendsto (fun level => parameters.vertexEmbedding level (starts level)) atTop (𝓝 point) := by
  letI : ∀ level, Nonempty (XiVtx system level) := fun level =>
    ⟨by simpa only [Nat.zero_add] using xiLiftVertices system 0 level true⟩
  apply IGS.Sec31.exists_level_points_tendsto_of_nested_dense parameters.vertexEmbedding
  · intro first second ordered vertex
    refine ⟨xiVertexInclusion system first second ordered vertex, ?_⟩
    simp only [vertexEmbedding, xiCompletionEmbedding, Function.comp_apply, xiVertexEmbedding_inclusion]
  · change Dense (Set.range (fun point : (level : ℕ) × XiVtx system level =>
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

end EIGS.XiPathMetricData

#print axioms IGS.Sec31.exists_level_points_tendsto_of_nested_dense
#print axioms EIGS.XiPathMetricData.exists_moving_starts
