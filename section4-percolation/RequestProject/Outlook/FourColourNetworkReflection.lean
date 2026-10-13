import RequestProject.Outlook.FourColourGraphConnectivity
import Mathlib.Logic.Equiv.Bool

/-! Explicit vertex-coordinate changes for reflection of the existing TTN
networks. The series junction is moved between its two actual representatives;
no graph-law identity is postulated. -/
namespace Cluster.TTN

def reverseNetwork (network : TTN) : TTN where
  V := network.V
  E := network.E
  fintypeV := network.fintypeV
  decEqV := network.decEqV
  fintypeE := network.fintypeE
  tail := network.head
  head := network.tail
  a := network.b
  b := network.a
  hab := Ne.symm network.hab

theorem underlyingGraph_reverseNetwork (network : TTN) :
    (reverseNetwork network).underlyingGraph = network.underlyingGraph := by
  ext first second
  change (first ≠ second ∧
    ((∃ edge, network.head edge=first ∧ network.tail edge=second) ∨
     (∃ edge, network.head edge=second ∧ network.tail edge=first))) ↔
    (first ≠ second ∧
    ((∃ edge, network.tail edge=first ∧ network.head edge=second) ∨
     (∃ edge, network.tail edge=second ∧ network.head edge=first)))
  simp only [and_comm]
  exact and_congr Iff.rfl or_comm

def seriesRebaseTo (firstNetwork secondNetwork : TTN) :
    seriesV firstNetwork secondNetwork → {vertex : firstNetwork.V // vertex ≠ firstNetwork.b} ⊕ secondNetwork.V
  | Sum.inl vertex => if junction : vertex=firstNetwork.b then Sum.inr secondNetwork.a
      else Sum.inl ⟨vertex, junction⟩
  | Sum.inr vertex => Sum.inr vertex.1

def seriesRebaseFrom (firstNetwork secondNetwork : TTN) :
    {vertex : firstNetwork.V // vertex ≠ firstNetwork.b} ⊕ secondNetwork.V → seriesV firstNetwork secondNetwork
  | Sum.inl vertex => Sum.inl vertex.1
  | Sum.inr vertex => if junction : vertex=secondNetwork.a then Sum.inl firstNetwork.b
      else Sum.inr ⟨vertex, junction⟩

def seriesRebase (firstNetwork secondNetwork : TTN) :
    seriesV firstNetwork secondNetwork ≃ {vertex : firstNetwork.V // vertex ≠ firstNetwork.b} ⊕ secondNetwork.V where
  toFun := seriesRebaseTo firstNetwork secondNetwork
  invFun := seriesRebaseFrom firstNetwork secondNetwork
  left_inv := by
    rintro (vertex | vertex)
    · by_cases junction : vertex=firstNetwork.b
      · subst vertex
        simp [seriesRebaseTo, seriesRebaseFrom]
      · simp [seriesRebaseTo, seriesRebaseFrom, junction]
    · simp [seriesRebaseTo, seriesRebaseFrom, vertex.2]
  right_inv := by
    rintro (vertex | vertex)
    · simp [seriesRebaseTo, seriesRebaseFrom, vertex.2]
    · by_cases junction : vertex=secondNetwork.a
      · subst vertex
        simp [seriesRebaseTo, seriesRebaseFrom]
      · simp [seriesRebaseTo, seriesRebaseFrom, junction]

theorem seriesRebase_right (firstNetwork secondNetwork : TTN) (vertex : secondNetwork.V) :
    seriesRebase firstNetwork secondNetwork (seriesEmb firstNetwork secondNetwork vertex) = Sum.inr vertex := by
  by_cases junction : vertex=secondNetwork.a
  · subst vertex
    simp [seriesRebase, seriesRebaseTo, seriesEmb]
  · simp [seriesRebase, seriesRebaseTo, seriesEmb, junction]

structure Reflection (firstNetwork secondNetwork : TTN) where
  vertices : firstNetwork.V ≃ secondNetwork.V
  edges : firstNetwork.E ≃ secondNetwork.E
  tail : ∀ edge, vertices (firstNetwork.tail edge) = secondNetwork.head (edges edge)
  head : ∀ edge, vertices (firstNetwork.head edge) = secondNetwork.tail (edges edge)
  source : vertices firstNetwork.a = secondNetwork.b
  target : vertices firstNetwork.b = secondNetwork.a

namespace Reflection

def symm {firstNetwork secondNetwork : TTN} (reflection : Reflection firstNetwork secondNetwork) :
    Reflection secondNetwork firstNetwork where
  vertices := reflection.vertices.symm
  edges := reflection.edges.symm
  tail := by
    intro edge
    apply reflection.vertices.injective
    simp only [Equiv.apply_symm_apply, reflection.head]
  head := by
    intro edge
    apply reflection.vertices.injective
    simp only [Equiv.apply_symm_apply, reflection.tail]
  source := by
    apply reflection.vertices.injective
    simp only [Equiv.apply_symm_apply, reflection.target]
  target := by
    apply reflection.vertices.injective
    simp only [Equiv.apply_symm_apply, reflection.source]

theorem edgePath_forward {firstNetwork secondNetwork : TTN}
    (reflection : Reflection firstNetwork secondNetwork) {first second : firstNetwork.V}
    (path : firstNetwork.EdgePath first second) :
    secondNetwork.EdgePath (reflection.vertices first) (reflection.vertices second) := by
  apply edgePath_map firstNetwork secondNetwork reflection.vertices _ path
  intro edge
  rw [reflection.tail, reflection.head]
  exact edgePath_symm (edgePath_edge secondNetwork (reflection.edges edge))

theorem edgePath_iff {firstNetwork secondNetwork : TTN}
    (reflection : Reflection firstNetwork secondNetwork) (first second : firstNetwork.V) :
    firstNetwork.EdgePath first second ↔
      secondNetwork.EdgePath (reflection.vertices first) (reflection.vertices second) := by
  constructor
  · exact reflection.edgePath_forward
  · intro path
    simpa only [symm, Equiv.symm_apply_apply] using reflection.symm.edgePath_forward path

theorem vertex_eq_source_iff {firstNetwork secondNetwork : TTN}
    (reflection : Reflection firstNetwork secondNetwork) (vertex : firstNetwork.V) :
    reflection.vertices vertex = secondNetwork.a ↔ vertex=firstNetwork.b := by
  rw [← reflection.target]
  exact reflection.vertices.injective.eq_iff

theorem vertex_eq_target_iff {firstNetwork secondNetwork : TTN}
    (reflection : Reflection firstNetwork secondNetwork) (vertex : firstNetwork.V) :
    reflection.vertices vertex = secondNetwork.b ↔ vertex=firstNetwork.a := by
  rw [← reflection.source]
  exact reflection.vertices.injective.eq_iff

def exceptTarget {firstNetwork secondNetwork : TTN} (reflection : Reflection firstNetwork secondNetwork) :
    {vertex : firstNetwork.V // vertex ≠ firstNetwork.b} ≃
      {vertex : secondNetwork.V // vertex ≠ secondNetwork.a} :=
  reflection.vertices.subtypeEquiv (fun vertex => not_congr (reflection.vertex_eq_source_iff vertex).symm)

def interior {firstNetwork secondNetwork : TTN} (reflection : Reflection firstNetwork secondNetwork) :
    {vertex : firstNetwork.V // vertex ≠ firstNetwork.a ∧ vertex ≠ firstNetwork.b} ≃
      {vertex : secondNetwork.V // vertex ≠ secondNetwork.a ∧ vertex ≠ secondNetwork.b} :=
  reflection.vertices.subtypeEquiv (fun vertex => by
    simp only [ne_eq, reflection.vertex_eq_source_iff, reflection.vertex_eq_target_iff]
    exact and_comm)

def seriesVertices {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstReflection : Reflection firstNetwork firstImage) (secondReflection : Reflection secondNetwork secondImage) :
    (seriesTTN firstNetwork secondNetwork).V ≃ (seriesTTN secondImage firstImage).V :=
  (seriesRebase firstNetwork secondNetwork).trans
    ((Equiv.sumCongr firstReflection.exceptTarget secondReflection.vertices).trans (Equiv.sumComm _ _))

theorem seriesVertices_left {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstReflection : Reflection firstNetwork firstImage) (secondReflection : Reflection secondNetwork secondImage)
    (vertex : firstNetwork.V) :
    seriesVertices firstReflection secondReflection (Sum.inl vertex) =
      seriesEmb secondImage firstImage (firstReflection.vertices vertex) := by
  by_cases junction : vertex=firstNetwork.b
  · subst vertex
    simp [seriesVertices, seriesRebase, seriesRebaseTo, seriesEmb, firstReflection.target, secondReflection.source,
      Equiv.sumComm, Equiv.sumCongr]
    rfl
  · have imageNotSource : firstReflection.vertices vertex ≠ firstImage.a := by
      exact fun equal => junction ((firstReflection.vertex_eq_source_iff vertex).mp equal)
    simp [seriesVertices, seriesRebase, seriesRebaseTo, seriesEmb, junction, imageNotSource, exceptTarget,
      Equiv.sumComm, Equiv.sumCongr]
    rfl

theorem seriesVertices_right {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstReflection : Reflection firstNetwork firstImage) (secondReflection : Reflection secondNetwork secondImage)
    (vertex : secondNetwork.V) :
    seriesVertices firstReflection secondReflection (seriesEmb firstNetwork secondNetwork vertex) =
      Sum.inl (secondReflection.vertices vertex) := by
  change Equiv.sumComm _ _ (Equiv.sumCongr firstReflection.exceptTarget secondReflection.vertices
    (seriesRebase firstNetwork secondNetwork (seriesEmb firstNetwork secondNetwork vertex))) = _
  rw [seriesRebase_right]
  rfl

def series {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstReflection : Reflection firstNetwork firstImage) (secondReflection : Reflection secondNetwork secondImage) :
    Reflection (seriesTTN firstNetwork secondNetwork) (seriesTTN secondImage firstImage) where
  vertices := seriesVertices firstReflection secondReflection
  edges := (Equiv.sumCongr firstReflection.edges secondReflection.edges).trans (Equiv.sumComm _ _)
  tail := by
    rintro (edge | edge)
    · change seriesVertices firstReflection secondReflection (Sum.inl (firstNetwork.tail edge)) =
        seriesEmb secondImage firstImage (firstImage.head (firstReflection.edges edge))
      rw [seriesVertices_left, firstReflection.tail]
    · change seriesVertices firstReflection secondReflection (seriesEmb firstNetwork secondNetwork (secondNetwork.tail edge)) =
        Sum.inl (secondImage.head (secondReflection.edges edge))
      rw [seriesVertices_right, secondReflection.tail]
  head := by
    rintro (edge | edge)
    · change seriesVertices firstReflection secondReflection (Sum.inl (firstNetwork.head edge)) =
        seriesEmb secondImage firstImage (firstImage.tail (firstReflection.edges edge))
      rw [seriesVertices_left, firstReflection.head]
    · change seriesVertices firstReflection secondReflection (seriesEmb firstNetwork secondNetwork (secondNetwork.head edge)) =
        Sum.inl (secondImage.tail (secondReflection.edges edge))
      rw [seriesVertices_right, secondReflection.head]
  source := by
    change seriesVertices firstReflection secondReflection (Sum.inl firstNetwork.a) = seriesEmb secondImage firstImage firstImage.b
    rw [seriesVertices_left, firstReflection.source]
  target := by
    change seriesVertices firstReflection secondReflection (seriesEmb firstNetwork secondNetwork secondNetwork.b) = Sum.inl secondImage.a
    rw [seriesVertices_right, secondReflection.target]

def parallelVertices {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstReflection : Reflection firstNetwork firstImage) (secondReflection : Reflection secondNetwork secondImage) :
    (parTTN firstNetwork secondNetwork).V ≃ (parTTN firstImage secondImage).V :=
  Equiv.sumCongr firstReflection.vertices secondReflection.interior

theorem parallelVertices_right {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstReflection : Reflection firstNetwork firstImage) (secondReflection : Reflection secondNetwork secondImage)
    (vertex : secondNetwork.V) :
    parallelVertices firstReflection secondReflection (parEmb firstNetwork secondNetwork vertex) =
      parEmb firstImage secondImage (secondReflection.vertices vertex) := by
  by_cases source : vertex=secondNetwork.a
  · subst vertex
    simp [parallelVertices, parEmb, firstReflection.source, secondReflection.source, Ne.symm secondImage.hab,
      Equiv.sumCongr]
    change Sum.inl (firstReflection.vertices firstNetwork.a) = Sum.inl firstImage.b
    rw [firstReflection.source]
  · by_cases target : vertex=secondNetwork.b
    · subst vertex
      simp [parallelVertices, parEmb, source, firstReflection.target, secondReflection.target, Equiv.sumCongr]
      change Sum.inl (firstReflection.vertices firstNetwork.b) = Sum.inl firstImage.a
      rw [firstReflection.target]
    · have imageNotSource : secondReflection.vertices vertex ≠ secondImage.a := by
        exact fun equal => target ((secondReflection.vertex_eq_source_iff vertex).mp equal)
      have imageNotTarget : secondReflection.vertices vertex ≠ secondImage.b := by
        exact fun equal => source ((secondReflection.vertex_eq_target_iff vertex).mp equal)
      simp [parallelVertices, parEmb, source, target, imageNotSource, imageNotTarget, interior, Equiv.sumCongr]
      rfl

def parallel {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstReflection : Reflection firstNetwork firstImage) (secondReflection : Reflection secondNetwork secondImage) :
    Reflection (parTTN firstNetwork secondNetwork) (parTTN firstImage secondImage) where
  vertices := parallelVertices firstReflection secondReflection
  edges := Equiv.sumCongr firstReflection.edges secondReflection.edges
  tail := by
    rintro (edge | edge)
    · change Sum.inl (firstReflection.vertices (firstNetwork.tail edge)) = Sum.inl (firstImage.head (firstReflection.edges edge))
      rw [firstReflection.tail]
    · change parallelVertices firstReflection secondReflection (parEmb firstNetwork secondNetwork (secondNetwork.tail edge)) =
        parEmb firstImage secondImage (secondImage.head (secondReflection.edges edge))
      rw [parallelVertices_right, secondReflection.tail]
  head := by
    rintro (edge | edge)
    · change Sum.inl (firstReflection.vertices (firstNetwork.head edge)) = Sum.inl (firstImage.tail (firstReflection.edges edge))
      rw [firstReflection.head]
    · change parallelVertices firstReflection secondReflection (parEmb firstNetwork secondNetwork (secondNetwork.head edge)) =
        parEmb firstImage secondImage (secondImage.tail (secondReflection.edges edge))
      rw [parallelVertices_right, secondReflection.head]
  source := by
    change Sum.inl (firstReflection.vertices firstNetwork.a) = Sum.inl firstImage.b
    rw [firstReflection.source]
  target := by
    change Sum.inl (firstReflection.vertices firstNetwork.b) = Sum.inl firstImage.a
    rw [firstReflection.target]

end Reflection

def edgeReflection : Reflection edgeTTN edgeTTN where
  vertices := Equiv.boolNot
  edges := Equiv.refl Unit
  tail := fun _ => rfl
  head := fun _ => rfl
  source := rfl
  target := rfl

def gapReflection : Reflection gapTTN gapTTN where
  vertices := Equiv.boolNot
  edges := Equiv.refl Empty
  tail := fun edge => nomatch edge
  head := fun edge => nomatch edge
  source := rfl
  target := rfl

end Cluster.TTN

namespace Cluster

def actualNetworkReflection : (depth : ℕ) → (configuration : Conf depth) →
    TTN.Reflection (net depth configuration) (net depth (reverseConfiguration depth configuration))
  | 0, configuration => by
      cases configuration
      · exact TTN.gapReflection
      · exact TTN.edgeReflection
  | depth+1, configuration =>
      (TTN.Reflection.series (actualNetworkReflection depth configuration.1)
        (actualNetworkReflection depth configuration.2.1)).parallel
      (TTN.Reflection.series (actualNetworkReflection depth configuration.2.2.1)
        (actualNetworkReflection depth configuration.2.2.2))

theorem actual_reflection_reachable_iff (depth : ℕ) (configuration : Conf depth)
    (first second : (net depth configuration).V) :
    (net depth configuration).underlyingGraph.Reachable first second ↔
      (net depth (reverseConfiguration depth configuration)).underlyingGraph.Reachable
        ((actualNetworkReflection depth configuration).vertices first)
        ((actualNetworkReflection depth configuration).vertices second) := by
  rw [← TTN.edgePath_iff_reachable, ← TTN.edgePath_iff_reachable]
  exact (actualNetworkReflection depth configuration).edgePath_iff first second

end Cluster

#print axioms Cluster.TTN.underlyingGraph_reverseNetwork
#print axioms Cluster.TTN.seriesRebase
#print axioms Cluster.TTN.seriesRebase_right
#print axioms Cluster.TTN.Reflection.series
#print axioms Cluster.TTN.Reflection.parallel
#print axioms Cluster.actualNetworkReflection
#print axioms Cluster.actual_reflection_reachable_iff
