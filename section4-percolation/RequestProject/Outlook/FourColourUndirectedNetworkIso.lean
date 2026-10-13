import RequestProject.Outlook.FourColourClusterIsomorphism

namespace Cluster.TTN

/-- A genuine edge and vertex bijection, preserving both terminals and each
unordered endpoint pair. Individual edge orientations may differ. -/
structure UndirectedIso (firstNetwork secondNetwork : TTN) where
  vertices : firstNetwork.V ≃ secondNetwork.V
  edges : firstNetwork.E ≃ secondNetwork.E
  ends : ∀ edge,
    (vertices (firstNetwork.tail edge)=secondNetwork.tail (edges edge) ∧
      vertices (firstNetwork.head edge)=secondNetwork.head (edges edge)) ∨
    (vertices (firstNetwork.tail edge)=secondNetwork.head (edges edge) ∧
      vertices (firstNetwork.head edge)=secondNetwork.tail (edges edge))
  source : vertices firstNetwork.a=secondNetwork.a
  target : vertices firstNetwork.b=secondNetwork.b

namespace UndirectedIso

def refl (network : TTN) : UndirectedIso network network where
  vertices := Equiv.refl _
  edges := Equiv.refl _
  ends := fun _ => Or.inl ⟨rfl,rfl⟩
  source := rfl
  target := rfl

def symm {firstNetwork secondNetwork : TTN} (isomorphism : UndirectedIso firstNetwork secondNetwork) :
    UndirectedIso secondNetwork firstNetwork where
  vertices := isomorphism.vertices.symm
  edges := isomorphism.edges.symm
  ends := by
    intro edge
    rcases isomorphism.ends (isomorphism.edges.symm edge) with forward | backward
    · refine Or.inl ⟨?_,?_⟩
      · apply isomorphism.vertices.injective
        simpa only [Equiv.apply_symm_apply] using forward.1.symm
      · apply isomorphism.vertices.injective
        simpa only [Equiv.apply_symm_apply] using forward.2.symm
    · refine Or.inr ⟨?_,?_⟩
      · apply isomorphism.vertices.injective
        simpa only [Equiv.apply_symm_apply] using backward.2.symm
      · apply isomorphism.vertices.injective
        simpa only [Equiv.apply_symm_apply] using backward.1.symm
  source := by apply isomorphism.vertices.injective; simp only [Equiv.apply_symm_apply, isomorphism.source]
  target := by apply isomorphism.vertices.injective; simp only [Equiv.apply_symm_apply, isomorphism.target]

theorem vertex_eq_source_iff {firstNetwork secondNetwork : TTN}
    (isomorphism : UndirectedIso firstNetwork secondNetwork) (vertex : firstNetwork.V) :
    isomorphism.vertices vertex=secondNetwork.a ↔ vertex=firstNetwork.a := by
  rw [← isomorphism.source]
  exact isomorphism.vertices.injective.eq_iff

theorem vertex_eq_target_iff {firstNetwork secondNetwork : TTN}
    (isomorphism : UndirectedIso firstNetwork secondNetwork) (vertex : firstNetwork.V) :
    isomorphism.vertices vertex=secondNetwork.b ↔ vertex=firstNetwork.b := by
  rw [← isomorphism.target]
  exact isomorphism.vertices.injective.eq_iff

def exceptSource {firstNetwork secondNetwork : TTN} (isomorphism : UndirectedIso firstNetwork secondNetwork) :
    {vertex : firstNetwork.V // vertex≠firstNetwork.a} ≃ {vertex : secondNetwork.V // vertex≠secondNetwork.a} :=
  isomorphism.vertices.subtypeEquiv (fun vertex => not_congr (isomorphism.vertex_eq_source_iff vertex).symm)

def interior {firstNetwork secondNetwork : TTN} (isomorphism : UndirectedIso firstNetwork secondNetwork) :
    {vertex : firstNetwork.V // vertex≠firstNetwork.a ∧ vertex≠firstNetwork.b} ≃
      {vertex : secondNetwork.V // vertex≠secondNetwork.a ∧ vertex≠secondNetwork.b} :=
  isomorphism.vertices.subtypeEquiv (fun vertex => and_congr
    (not_congr (isomorphism.vertex_eq_source_iff vertex).symm)
    (not_congr (isomorphism.vertex_eq_target_iff vertex).symm))

def seriesVertices {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstIso : UndirectedIso firstNetwork firstImage) (secondIso : UndirectedIso secondNetwork secondImage) :
    (seriesTTN firstNetwork secondNetwork).V ≃ (seriesTTN firstImage secondImage).V :=
  Equiv.sumCongr firstIso.vertices secondIso.exceptSource

theorem seriesVertices_right {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstIso : UndirectedIso firstNetwork firstImage) (secondIso : UndirectedIso secondNetwork secondImage)
    (vertex : secondNetwork.V) :
    seriesVertices firstIso secondIso (seriesEmb firstNetwork secondNetwork vertex) =
      seriesEmb firstImage secondImage (secondIso.vertices vertex) := by
  by_cases source : vertex=secondNetwork.a
  · subst vertex
    simp [seriesVertices, seriesEmb, secondIso.source, Equiv.sumCongr]
    change Sum.inl (firstIso.vertices firstNetwork.b) = Sum.inl firstImage.b
    rw [firstIso.target]
  · have imageNotSource : secondIso.vertices vertex≠secondImage.a :=
      fun equal => source ((secondIso.vertex_eq_source_iff vertex).mp equal)
    simp [seriesVertices, seriesEmb, source, imageNotSource, exceptSource, Equiv.sumCongr]
    rfl

def series {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstIso : UndirectedIso firstNetwork firstImage) (secondIso : UndirectedIso secondNetwork secondImage) :
    UndirectedIso (seriesTTN firstNetwork secondNetwork) (seriesTTN firstImage secondImage) where
  vertices := seriesVertices firstIso secondIso
  edges := Equiv.sumCongr firstIso.edges secondIso.edges
  ends := by
    rintro (edge | edge)
    · rcases firstIso.ends edge with forward | backward
      · exact Or.inl ⟨congrArg Sum.inl forward.1, congrArg Sum.inl forward.2⟩
      · exact Or.inr ⟨congrArg Sum.inl backward.1, congrArg Sum.inl backward.2⟩
    · change
        (seriesVertices firstIso secondIso (seriesEmb firstNetwork secondNetwork (secondNetwork.tail edge)) =
            seriesEmb firstImage secondImage (secondImage.tail (secondIso.edges edge)) ∧
          seriesVertices firstIso secondIso (seriesEmb firstNetwork secondNetwork (secondNetwork.head edge)) =
            seriesEmb firstImage secondImage (secondImage.head (secondIso.edges edge))) ∨
        (seriesVertices firstIso secondIso (seriesEmb firstNetwork secondNetwork (secondNetwork.tail edge)) =
            seriesEmb firstImage secondImage (secondImage.head (secondIso.edges edge)) ∧
          seriesVertices firstIso secondIso (seriesEmb firstNetwork secondNetwork (secondNetwork.head edge)) =
            seriesEmb firstImage secondImage (secondImage.tail (secondIso.edges edge)))
      simp only [seriesVertices_right]
      rcases secondIso.ends edge with forward | backward
      · exact Or.inl ⟨congrArg (seriesEmb firstImage secondImage) forward.1,
          congrArg (seriesEmb firstImage secondImage) forward.2⟩
      · exact Or.inr ⟨congrArg (seriesEmb firstImage secondImage) backward.1,
          congrArg (seriesEmb firstImage secondImage) backward.2⟩
  source := by change Sum.inl (firstIso.vertices firstNetwork.a)=Sum.inl firstImage.a; rw [firstIso.source]
  target := by
    change seriesVertices firstIso secondIso (seriesEmb firstNetwork secondNetwork secondNetwork.b) =
      seriesEmb firstImage secondImage secondImage.b
    rw [seriesVertices_right, secondIso.target]

def parallelVertices {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstIso : UndirectedIso firstNetwork firstImage) (secondIso : UndirectedIso secondNetwork secondImage) :
    (parTTN firstNetwork secondNetwork).V ≃ (parTTN firstImage secondImage).V :=
  Equiv.sumCongr firstIso.vertices secondIso.interior

theorem parallelVertices_right {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstIso : UndirectedIso firstNetwork firstImage) (secondIso : UndirectedIso secondNetwork secondImage)
    (vertex : secondNetwork.V) :
    parallelVertices firstIso secondIso (parEmb firstNetwork secondNetwork vertex) =
      parEmb firstImage secondImage (secondIso.vertices vertex) := by
  by_cases source : vertex=secondNetwork.a
  · subst vertex
    simp [parallelVertices, parEmb, secondIso.source, Equiv.sumCongr]
    change Sum.inl (firstIso.vertices firstNetwork.a)=Sum.inl firstImage.a
    rw [firstIso.source]
  · by_cases target : vertex=secondNetwork.b
    · subst vertex
      simp [parallelVertices, parEmb, source, secondIso.target, Ne.symm secondImage.hab, Equiv.sumCongr]
      change Sum.inl (firstIso.vertices firstNetwork.b)=Sum.inl firstImage.b
      rw [firstIso.target]
    · have imageNotSource : secondIso.vertices vertex≠secondImage.a :=
        fun equal => source ((secondIso.vertex_eq_source_iff vertex).mp equal)
      have imageNotTarget : secondIso.vertices vertex≠secondImage.b :=
        fun equal => target ((secondIso.vertex_eq_target_iff vertex).mp equal)
      simp [parallelVertices, parEmb, source, target, imageNotSource, imageNotTarget, interior, Equiv.sumCongr]
      rfl

def parallel {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstIso : UndirectedIso firstNetwork firstImage) (secondIso : UndirectedIso secondNetwork secondImage) :
    UndirectedIso (parTTN firstNetwork secondNetwork) (parTTN firstImage secondImage) where
  vertices := parallelVertices firstIso secondIso
  edges := Equiv.sumCongr firstIso.edges secondIso.edges
  ends := by
    rintro (edge | edge)
    · rcases firstIso.ends edge with forward | backward
      · exact Or.inl ⟨congrArg Sum.inl forward.1, congrArg Sum.inl forward.2⟩
      · exact Or.inr ⟨congrArg Sum.inl backward.1, congrArg Sum.inl backward.2⟩
    · change
        (parallelVertices firstIso secondIso (parEmb firstNetwork secondNetwork (secondNetwork.tail edge)) =
            parEmb firstImage secondImage (secondImage.tail (secondIso.edges edge)) ∧
          parallelVertices firstIso secondIso (parEmb firstNetwork secondNetwork (secondNetwork.head edge)) =
            parEmb firstImage secondImage (secondImage.head (secondIso.edges edge))) ∨
        (parallelVertices firstIso secondIso (parEmb firstNetwork secondNetwork (secondNetwork.tail edge)) =
            parEmb firstImage secondImage (secondImage.head (secondIso.edges edge)) ∧
          parallelVertices firstIso secondIso (parEmb firstNetwork secondNetwork (secondNetwork.head edge)) =
            parEmb firstImage secondImage (secondImage.tail (secondIso.edges edge)))
      simp only [parallelVertices_right]
      rcases secondIso.ends edge with forward | backward
      · exact Or.inl ⟨congrArg (parEmb firstImage secondImage) forward.1,
          congrArg (parEmb firstImage secondImage) forward.2⟩
      · exact Or.inr ⟨congrArg (parEmb firstImage secondImage) backward.1,
          congrArg (parEmb firstImage secondImage) backward.2⟩
  source := by change Sum.inl (firstIso.vertices firstNetwork.a)=Sum.inl firstImage.a; rw [firstIso.source]
  target := by change Sum.inl (firstIso.vertices firstNetwork.b)=Sum.inl firstImage.b; rw [firstIso.target]

theorem edgePath_forward {firstNetwork secondNetwork : TTN}
    (isomorphism : UndirectedIso firstNetwork secondNetwork) {firstVertex secondVertex : firstNetwork.V}
    (path : firstNetwork.EdgePath firstVertex secondVertex) :
    secondNetwork.EdgePath (isomorphism.vertices firstVertex) (isomorphism.vertices secondVertex) := by
  apply edgePath_map firstNetwork secondNetwork isomorphism.vertices _ path
  intro edge
  rcases isomorphism.ends edge with forward | backward
  · rw [forward.1, forward.2]
    exact edgePath_edge secondNetwork (isomorphism.edges edge)
  · rw [backward.1, backward.2]
    exact edgePath_symm (edgePath_edge secondNetwork (isomorphism.edges edge))

theorem edgePath_iff {firstNetwork secondNetwork : TTN}
    (isomorphism : UndirectedIso firstNetwork secondNetwork) (firstVertex secondVertex : firstNetwork.V) :
    firstNetwork.EdgePath firstVertex secondVertex ↔
      secondNetwork.EdgePath (isomorphism.vertices firstVertex) (isomorphism.vertices secondVertex) := by
  constructor
  · exact isomorphism.edgePath_forward
  · intro path
    simpa only [symm, Equiv.symm_apply_apply] using isomorphism.symm.edgePath_forward path

theorem adjacent_forward {firstNetwork secondNetwork : TTN}
    (isomorphism : UndirectedIso firstNetwork secondNetwork) {firstVertex secondVertex : firstNetwork.V}
    (adjacent : firstNetwork.underlyingGraph.Adj firstVertex secondVertex) :
    secondNetwork.underlyingGraph.Adj (isomorphism.vertices firstVertex) (isomorphism.vertices secondVertex) := by
  rcases adjacent with ⟨distinct, forward | backward⟩
  · rcases forward with ⟨edge,rfl,rfl⟩
    refine ⟨fun equal => distinct (isomorphism.vertices.injective equal),?_⟩
    rcases isomorphism.ends edge with forward | backward
    · exact Or.inl ⟨isomorphism.edges edge, forward.1.symm, forward.2.symm⟩
    · exact Or.inr ⟨isomorphism.edges edge, backward.2.symm, backward.1.symm⟩
  · rcases backward with ⟨edge,rfl,rfl⟩
    refine ⟨fun equal => distinct (isomorphism.vertices.injective equal),?_⟩
    rcases isomorphism.ends edge with forward | backward
    · exact Or.inr ⟨isomorphism.edges edge, forward.1.symm, forward.2.symm⟩
    · exact Or.inl ⟨isomorphism.edges edge, backward.2.symm, backward.1.symm⟩

theorem adjacent_iff {firstNetwork secondNetwork : TTN}
    (isomorphism : UndirectedIso firstNetwork secondNetwork) (firstVertex secondVertex : firstNetwork.V) :
    secondNetwork.underlyingGraph.Adj (isomorphism.vertices firstVertex) (isomorphism.vertices secondVertex) ↔
      firstNetwork.underlyingGraph.Adj firstVertex secondVertex := by
  constructor
  · intro adjacent
    simpa only [symm, Equiv.symm_apply_apply] using isomorphism.symm.adjacent_forward adjacent
  · exact isomorphism.adjacent_forward

def sourceClusterIso {firstNetwork secondNetwork : TTN}
    (isomorphism : UndirectedIso firstNetwork secondNetwork) :
    sourceClusterGraph firstNetwork ≃g sourceClusterGraph secondNetwork where
  toEquiv := isomorphism.vertices.subtypeEquiv (fun vertex => by
    simpa only [isomorphism.source] using isomorphism.edgePath_iff firstNetwork.a vertex)
  map_rel_iff' := by intro firstVertex secondVertex; exact isomorphism.adjacent_iff firstVertex.1 secondVertex.1

end UndirectedIso
end Cluster.TTN

#print axioms Cluster.TTN.UndirectedIso.series
#print axioms Cluster.TTN.UndirectedIso.parallel
#print axioms Cluster.TTN.UndirectedIso.sourceClusterIso
