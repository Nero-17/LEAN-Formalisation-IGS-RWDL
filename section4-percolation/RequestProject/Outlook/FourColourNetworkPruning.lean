import RequestProject.Outlook.FourColourRetainedGraph

/-! Incidence-preserving network isomorphisms and actual edge pruning.
The ambient vertex set is retained only as an intermediate coordinate device;
the final cluster graph is the active-vertex induced graph defined separately. -/
namespace Cluster.TTN

structure IncidenceIso (firstNetwork secondNetwork : TTN) where
  vertices : firstNetwork.V ≃ secondNetwork.V
  edges : firstNetwork.E ≃ secondNetwork.E
  tail : ∀ edge, vertices (firstNetwork.tail edge) = secondNetwork.tail (edges edge)
  head : ∀ edge, vertices (firstNetwork.head edge) = secondNetwork.head (edges edge)
  source : vertices firstNetwork.a = secondNetwork.a
  target : vertices firstNetwork.b = secondNetwork.b

namespace IncidenceIso

def refl (network : TTN) : IncidenceIso network network where
  vertices := Equiv.refl _
  edges := Equiv.refl _
  tail := fun _ => rfl
  head := fun _ => rfl
  source := rfl
  target := rfl

def trans {firstNetwork secondNetwork thirdNetwork : TTN}
    (firstIso : IncidenceIso firstNetwork secondNetwork) (secondIso : IncidenceIso secondNetwork thirdNetwork) :
    IncidenceIso firstNetwork thirdNetwork where
  vertices := firstIso.vertices.trans secondIso.vertices
  edges := firstIso.edges.trans secondIso.edges
  tail := by intro edge; change secondIso.vertices (firstIso.vertices (firstNetwork.tail edge)) = _; rw [firstIso.tail, secondIso.tail]; rfl
  head := by intro edge; change secondIso.vertices (firstIso.vertices (firstNetwork.head edge)) = _; rw [firstIso.head, secondIso.head]; rfl
  source := by change secondIso.vertices (firstIso.vertices firstNetwork.a) = _; rw [firstIso.source, secondIso.source]
  target := by change secondIso.vertices (firstIso.vertices firstNetwork.b) = _; rw [firstIso.target, secondIso.target]

def symm {firstNetwork secondNetwork : TTN} (isomorphism : IncidenceIso firstNetwork secondNetwork) :
    IncidenceIso secondNetwork firstNetwork where
  vertices := isomorphism.vertices.symm
  edges := isomorphism.edges.symm
  tail := by intro edge; apply isomorphism.vertices.injective; simp only [Equiv.apply_symm_apply, isomorphism.tail]
  head := by intro edge; apply isomorphism.vertices.injective; simp only [Equiv.apply_symm_apply, isomorphism.head]
  source := by apply isomorphism.vertices.injective; simp only [Equiv.apply_symm_apply, isomorphism.source]
  target := by apply isomorphism.vertices.injective; simp only [Equiv.apply_symm_apply, isomorphism.target]

def reverse {firstNetwork secondNetwork : TTN} (isomorphism : IncidenceIso firstNetwork secondNetwork) :
    IncidenceIso (reverseNetwork firstNetwork) (reverseNetwork secondNetwork) where
  vertices := isomorphism.vertices
  edges := isomorphism.edges
  tail := isomorphism.head
  head := isomorphism.tail
  source := isomorphism.target
  target := isomorphism.source

def fromReflection {firstNetwork secondNetwork : TTN} (reflection : Reflection firstNetwork secondNetwork) :
    IncidenceIso (reverseNetwork firstNetwork) secondNetwork where
  vertices := reflection.vertices
  edges := reflection.edges
  tail := reflection.head
  head := reflection.tail
  source := reflection.target
  target := reflection.source

theorem vertex_eq_source_iff {firstNetwork secondNetwork : TTN}
    (isomorphism : IncidenceIso firstNetwork secondNetwork) (vertex : firstNetwork.V) :
    isomorphism.vertices vertex = secondNetwork.a ↔ vertex=firstNetwork.a := by
  rw [← isomorphism.source]
  exact isomorphism.vertices.injective.eq_iff

theorem vertex_eq_target_iff {firstNetwork secondNetwork : TTN}
    (isomorphism : IncidenceIso firstNetwork secondNetwork) (vertex : firstNetwork.V) :
    isomorphism.vertices vertex = secondNetwork.b ↔ vertex=firstNetwork.b := by
  rw [← isomorphism.target]
  exact isomorphism.vertices.injective.eq_iff

def exceptSource {firstNetwork secondNetwork : TTN} (isomorphism : IncidenceIso firstNetwork secondNetwork) :
    {vertex : firstNetwork.V // vertex ≠ firstNetwork.a} ≃ {vertex : secondNetwork.V // vertex ≠ secondNetwork.a} :=
  isomorphism.vertices.subtypeEquiv (fun vertex => not_congr (isomorphism.vertex_eq_source_iff vertex).symm)

def interior {firstNetwork secondNetwork : TTN} (isomorphism : IncidenceIso firstNetwork secondNetwork) :
    {vertex : firstNetwork.V // vertex ≠ firstNetwork.a ∧ vertex ≠ firstNetwork.b} ≃
      {vertex : secondNetwork.V // vertex ≠ secondNetwork.a ∧ vertex ≠ secondNetwork.b} :=
  isomorphism.vertices.subtypeEquiv (fun vertex => and_congr
    (not_congr (isomorphism.vertex_eq_source_iff vertex).symm)
    (not_congr (isomorphism.vertex_eq_target_iff vertex).symm))

def seriesVertices {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstIso : IncidenceIso firstNetwork firstImage) (secondIso : IncidenceIso secondNetwork secondImage) :
    (seriesTTN firstNetwork secondNetwork).V ≃ (seriesTTN firstImage secondImage).V :=
  Equiv.sumCongr firstIso.vertices secondIso.exceptSource

theorem seriesVertices_right {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstIso : IncidenceIso firstNetwork firstImage) (secondIso : IncidenceIso secondNetwork secondImage)
    (vertex : secondNetwork.V) :
    seriesVertices firstIso secondIso (seriesEmb firstNetwork secondNetwork vertex) =
      seriesEmb firstImage secondImage (secondIso.vertices vertex) := by
  by_cases source : vertex=secondNetwork.a
  · subst vertex
    simp [seriesVertices, seriesEmb, secondIso.source, Equiv.sumCongr]
    change Sum.inl (firstIso.vertices firstNetwork.b) = Sum.inl firstImage.b
    rw [firstIso.target]
  · have imageNotSource : secondIso.vertices vertex ≠ secondImage.a :=
      fun equal => source ((secondIso.vertex_eq_source_iff vertex).mp equal)
    simp [seriesVertices, seriesEmb, source, imageNotSource, exceptSource, Equiv.sumCongr]
    rfl

def series {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstIso : IncidenceIso firstNetwork firstImage) (secondIso : IncidenceIso secondNetwork secondImage) :
    IncidenceIso (seriesTTN firstNetwork secondNetwork) (seriesTTN firstImage secondImage) where
  vertices := seriesVertices firstIso secondIso
  edges := Equiv.sumCongr firstIso.edges secondIso.edges
  tail := by
    rintro (edge | edge)
    · change Sum.inl (firstIso.vertices (firstNetwork.tail edge)) = Sum.inl (firstImage.tail (firstIso.edges edge)); rw [firstIso.tail]
    · change seriesVertices firstIso secondIso (seriesEmb firstNetwork secondNetwork (secondNetwork.tail edge)) =
        seriesEmb firstImage secondImage (secondImage.tail (secondIso.edges edge))
      rw [seriesVertices_right, secondIso.tail]
  head := by
    rintro (edge | edge)
    · change Sum.inl (firstIso.vertices (firstNetwork.head edge)) = Sum.inl (firstImage.head (firstIso.edges edge)); rw [firstIso.head]
    · change seriesVertices firstIso secondIso (seriesEmb firstNetwork secondNetwork (secondNetwork.head edge)) =
        seriesEmb firstImage secondImage (secondImage.head (secondIso.edges edge))
      rw [seriesVertices_right, secondIso.head]
  source := by change Sum.inl (firstIso.vertices firstNetwork.a) = Sum.inl firstImage.a; rw [firstIso.source]
  target := by
    change seriesVertices firstIso secondIso (seriesEmb firstNetwork secondNetwork secondNetwork.b) = seriesEmb firstImage secondImage secondImage.b
    rw [seriesVertices_right, secondIso.target]

def parallelVertices {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstIso : IncidenceIso firstNetwork firstImage) (secondIso : IncidenceIso secondNetwork secondImage) :
    (parTTN firstNetwork secondNetwork).V ≃ (parTTN firstImage secondImage).V :=
  Equiv.sumCongr firstIso.vertices secondIso.interior

theorem parallelVertices_right {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstIso : IncidenceIso firstNetwork firstImage) (secondIso : IncidenceIso secondNetwork secondImage)
    (vertex : secondNetwork.V) :
    parallelVertices firstIso secondIso (parEmb firstNetwork secondNetwork vertex) =
      parEmb firstImage secondImage (secondIso.vertices vertex) := by
  by_cases source : vertex=secondNetwork.a
  · subst vertex
    simp [parallelVertices, parEmb, secondIso.source, Equiv.sumCongr]
    change Sum.inl (firstIso.vertices firstNetwork.a) = Sum.inl firstImage.a
    rw [firstIso.source]
  · by_cases target : vertex=secondNetwork.b
    · subst vertex
      simp [parallelVertices, parEmb, source, secondIso.target, Ne.symm secondImage.hab, Equiv.sumCongr]
      change Sum.inl (firstIso.vertices firstNetwork.b) = Sum.inl firstImage.b
      rw [firstIso.target]
    · have imageNotSource : secondIso.vertices vertex ≠ secondImage.a :=
        fun equal => source ((secondIso.vertex_eq_source_iff vertex).mp equal)
      have imageNotTarget : secondIso.vertices vertex ≠ secondImage.b :=
        fun equal => target ((secondIso.vertex_eq_target_iff vertex).mp equal)
      simp [parallelVertices, parEmb, source, target, imageNotSource, imageNotTarget, interior, Equiv.sumCongr]
      rfl

def parallel {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstIso : IncidenceIso firstNetwork firstImage) (secondIso : IncidenceIso secondNetwork secondImage) :
    IncidenceIso (parTTN firstNetwork secondNetwork) (parTTN firstImage secondImage) where
  vertices := parallelVertices firstIso secondIso
  edges := Equiv.sumCongr firstIso.edges secondIso.edges
  tail := by
    rintro (edge | edge)
    · change Sum.inl (firstIso.vertices (firstNetwork.tail edge)) = Sum.inl (firstImage.tail (firstIso.edges edge))
      rw [firstIso.tail]
    · change parallelVertices firstIso secondIso (parEmb firstNetwork secondNetwork (secondNetwork.tail edge)) =
        parEmb firstImage secondImage (secondImage.tail (secondIso.edges edge))
      rw [parallelVertices_right, secondIso.tail]
  head := by
    rintro (edge | edge)
    · change Sum.inl (firstIso.vertices (firstNetwork.head edge)) = Sum.inl (firstImage.head (firstIso.edges edge))
      rw [firstIso.head]
    · change parallelVertices firstIso secondIso (parEmb firstNetwork secondNetwork (secondNetwork.head edge)) =
        parEmb firstImage secondImage (secondImage.head (secondIso.edges edge))
      rw [parallelVertices_right, secondIso.head]
  source := by change Sum.inl (firstIso.vertices firstNetwork.a) = Sum.inl firstImage.a; rw [firstIso.source]
  target := by change Sum.inl (firstIso.vertices firstNetwork.b) = Sum.inl firstImage.b; rw [firstIso.target]

theorem edgePath_forward {firstNetwork secondNetwork : TTN}
    (isomorphism : IncidenceIso firstNetwork secondNetwork) {firstVertex secondVertex : firstNetwork.V}
    (path : firstNetwork.EdgePath firstVertex secondVertex) :
    secondNetwork.EdgePath (isomorphism.vertices firstVertex) (isomorphism.vertices secondVertex) := by
  exact edgePath_map firstNetwork secondNetwork isomorphism.vertices
    (fun edge => by rw [isomorphism.tail, isomorphism.head]; exact edgePath_edge secondNetwork (isomorphism.edges edge)) path

theorem edgePath_iff {firstNetwork secondNetwork : TTN}
    (isomorphism : IncidenceIso firstNetwork secondNetwork) (firstVertex secondVertex : firstNetwork.V) :
    firstNetwork.EdgePath firstVertex secondVertex ↔
      secondNetwork.EdgePath (isomorphism.vertices firstVertex) (isomorphism.vertices secondVertex) := by
  constructor
  · exact isomorphism.edgePath_forward
  · intro path
    simpa only [symm, Equiv.symm_apply_apply] using isomorphism.symm.edgePath_forward path

end IncidenceIso

noncomputable def retainedNetwork (network : TTN) (parent : Fin 4) (reversed : Bool) : TTN := by
  classical
  exact {
    V := network.V
    E := {edge : network.E // retainedEdge network parent reversed edge}
    fintypeV := network.fintypeV
    decEqV := network.decEqV
    fintypeE := inferInstance
    tail := fun edge => network.tail edge.1
    head := fun edge => network.head edge.1
    a := network.a
    b := network.b
    hab := network.hab }

noncomputable def retainedNetworkReflection {firstNetwork secondNetwork : TTN}
    (reflection : Reflection firstNetwork secondNetwork) (parent : Fin 4) (reversed : Bool) :
    Reflection (retainedNetwork firstNetwork parent reversed) (retainedNetwork secondNetwork parent (!reversed)) where
  vertices := reflection.vertices
  edges := reflection.edges.subtypeEquiv (retainedEdge_reflection reflection parent reversed)
  tail := fun edge => reflection.tail edge.1
  head := fun edge => reflection.head edge.1
  source := reflection.source
  target := reflection.target

theorem activeComponent_path (network : TTN) (parent : Fin 4) (reversed : Bool)
    {firstVertex secondVertex : network.V} (path : network.EdgePath firstVertex secondVertex) :
    activeComponent network parent reversed firstVertex ↔
      activeComponent network parent reversed secondVertex := by
  exact Iff.of_eq (edgePath_invariant network (activeComponent network parent reversed)
    (fun edge => propext (activeComponent_edge network parent reversed edge)) path)

theorem retainedNetwork_path_to_original (network : TTN) (parent : Fin 4) (reversed : Bool)
    {firstVertex secondVertex : network.V}
    (path : (retainedNetwork network parent reversed).EdgePath firstVertex secondVertex) :
    network.EdgePath firstVertex secondVertex := by
  exact edgePath_map (retainedNetwork network parent reversed) network id
    (fun edge => edgePath_edge network edge.1) path

theorem original_path_to_retainedNetwork (network : TTN) (parent : Fin 4) (reversed : Bool)
    {firstVertex secondVertex : network.V} (path : network.EdgePath firstVertex secondVertex)
    (active : activeComponent network parent reversed firstVertex) :
    (retainedNetwork network parent reversed).EdgePath firstVertex secondVertex := by
  revert active
  induction path with
  | rel firstVertex secondVertex witness =>
      intro active
      rcases witness with ⟨edge, rfl, rfl⟩
      exact edgePath_edge (retainedNetwork network parent reversed) ⟨edge, active⟩
  | refl vertex => exact fun _ => edgePath_self _ _
  | symm firstVertex secondVertex path induction =>
      intro active
      exact edgePath_symm (induction ((activeComponent_path network parent reversed path).mpr active))
  | trans firstVertex secondVertex thirdVertex firstPath secondPath firstInduction secondInduction =>
      intro active
      exact edgePath_trans (firstInduction active)
        (secondInduction ((activeComponent_path network parent reversed firstPath).mp active))

theorem retainedNetwork_path_iff (network : TTN) (parent : Fin 4) (reversed : Bool)
    {firstVertex secondVertex : network.V}
    (active : activeComponent network parent reversed firstVertex) :
    (retainedNetwork network parent reversed).EdgePath firstVertex secondVertex ↔
      network.EdgePath firstVertex secondVertex :=
  ⟨retainedNetwork_path_to_original network parent reversed,
    fun path => original_path_to_retainedNetwork network parent reversed path active⟩

end Cluster.TTN

#print axioms Cluster.TTN.IncidenceIso.series
#print axioms Cluster.TTN.IncidenceIso.parallel
#print axioms Cluster.TTN.IncidenceIso.edgePath_iff
#print axioms Cluster.TTN.retainedNetworkReflection
#print axioms Cluster.TTN.retainedNetwork_path_iff
