import RequestProject.Outlook.FourColourInfiniteGraphLaw

/-! Actual coarse-to-fine vertex injections and explicit two-edge lifts.
All constructions use the original Conf/net and TTN vertex identifications.
The reverse path compression and metric equality are separate next targets. -/
namespace Cluster.TTN

structure TerminalEmbedding (firstNetwork secondNetwork : TTN) where
  vertices : firstNetwork.V ↪ secondNetwork.V
  source : vertices firstNetwork.a=secondNetwork.a
  target : vertices firstNetwork.b=secondNetwork.b

namespace TerminalEmbedding

theorem vertex_eq_source_iff {firstNetwork secondNetwork : TTN}
    (embedding : TerminalEmbedding firstNetwork secondNetwork) (vertex : firstNetwork.V) :
    embedding.vertices vertex=secondNetwork.a ↔ vertex=firstNetwork.a := by
  rw [← embedding.source]
  exact embedding.vertices.injective.eq_iff

theorem vertex_eq_target_iff {firstNetwork secondNetwork : TTN}
    (embedding : TerminalEmbedding firstNetwork secondNetwork) (vertex : firstNetwork.V) :
    embedding.vertices vertex=secondNetwork.b ↔ vertex=firstNetwork.b := by
  rw [← embedding.target]
  exact embedding.vertices.injective.eq_iff

def exceptSource {firstNetwork secondNetwork : TTN} (embedding : TerminalEmbedding firstNetwork secondNetwork) :
    {vertex : firstNetwork.V // vertex≠firstNetwork.a} ↪ {vertex : secondNetwork.V // vertex≠secondNetwork.a} :=
  embedding.vertices.subtypeMap (fun {_} distinct equal => distinct ((embedding.vertex_eq_source_iff _).mp equal))

def interior {firstNetwork secondNetwork : TTN} (embedding : TerminalEmbedding firstNetwork secondNetwork) :
    {vertex : firstNetwork.V // vertex≠firstNetwork.a ∧ vertex≠firstNetwork.b} ↪
      {vertex : secondNetwork.V // vertex≠secondNetwork.a ∧ vertex≠secondNetwork.b} :=
  embedding.vertices.subtypeMap (fun {_} distinct =>
    ⟨fun equal => distinct.1 ((embedding.vertex_eq_source_iff _).mp equal),
      fun equal => distinct.2 ((embedding.vertex_eq_target_iff _).mp equal)⟩)

def seriesVertices {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstEmbedding : TerminalEmbedding firstNetwork firstImage)
    (secondEmbedding : TerminalEmbedding secondNetwork secondImage) :
    (seriesTTN firstNetwork secondNetwork).V ↪ (seriesTTN firstImage secondImage).V :=
  Function.Embedding.sumMap firstEmbedding.vertices secondEmbedding.exceptSource

theorem seriesVertices_right {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstEmbedding : TerminalEmbedding firstNetwork firstImage)
    (secondEmbedding : TerminalEmbedding secondNetwork secondImage) (vertex : secondNetwork.V) :
    seriesVertices firstEmbedding secondEmbedding (seriesEmb firstNetwork secondNetwork vertex) =
      seriesEmb firstImage secondImage (secondEmbedding.vertices vertex) := by
  by_cases source : vertex=secondNetwork.a
  · subst vertex
    simp only [seriesEmb, dif_pos rfl, secondEmbedding.source]
    change Sum.inl (firstEmbedding.vertices firstNetwork.b) = Sum.inl firstImage.b
    rw [firstEmbedding.target]
  · have imageNotSource : secondEmbedding.vertices vertex≠secondImage.a :=
      fun equal => source ((secondEmbedding.vertex_eq_source_iff vertex).mp equal)
    simp only [seriesEmb, dif_neg source, dif_neg imageNotSource]
    rfl

def series {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstEmbedding : TerminalEmbedding firstNetwork firstImage)
    (secondEmbedding : TerminalEmbedding secondNetwork secondImage) :
    TerminalEmbedding (seriesTTN firstNetwork secondNetwork) (seriesTTN firstImage secondImage) where
  vertices := seriesVertices firstEmbedding secondEmbedding
  source := by change Sum.inl (firstEmbedding.vertices firstNetwork.a)=Sum.inl firstImage.a; rw [firstEmbedding.source]
  target := by
    change seriesVertices firstEmbedding secondEmbedding (seriesEmb firstNetwork secondNetwork secondNetwork.b) =
      seriesEmb firstImage secondImage secondImage.b
    rw [seriesVertices_right, secondEmbedding.target]

def parallelVertices {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstEmbedding : TerminalEmbedding firstNetwork firstImage)
    (secondEmbedding : TerminalEmbedding secondNetwork secondImage) :
    (parTTN firstNetwork secondNetwork).V ↪ (parTTN firstImage secondImage).V :=
  Function.Embedding.sumMap firstEmbedding.vertices secondEmbedding.interior

theorem parallelVertices_right {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstEmbedding : TerminalEmbedding firstNetwork firstImage)
    (secondEmbedding : TerminalEmbedding secondNetwork secondImage) (vertex : secondNetwork.V) :
    parallelVertices firstEmbedding secondEmbedding (parEmb firstNetwork secondNetwork vertex) =
      parEmb firstImage secondImage (secondEmbedding.vertices vertex) := by
  by_cases source : vertex=secondNetwork.a
  · subst vertex
    simp only [parEmb, dif_pos rfl, secondEmbedding.source]
    change Sum.inl (firstEmbedding.vertices firstNetwork.a) = Sum.inl firstImage.a
    rw [firstEmbedding.source]
  · by_cases target : vertex=secondNetwork.b
    · subst vertex
      simp only [parEmb, dif_neg source, dif_pos rfl, secondEmbedding.target,
        dif_neg (Ne.symm secondImage.hab)]
      change Sum.inl (firstEmbedding.vertices firstNetwork.b) = Sum.inl firstImage.b
      rw [firstEmbedding.target]
    · have imageNotSource : secondEmbedding.vertices vertex≠secondImage.a :=
        fun equal => source ((secondEmbedding.vertex_eq_source_iff vertex).mp equal)
      have imageNotTarget : secondEmbedding.vertices vertex≠secondImage.b :=
        fun equal => target ((secondEmbedding.vertex_eq_target_iff vertex).mp equal)
      simp only [parEmb, dif_neg source, dif_neg target, dif_neg imageNotSource, dif_neg imageNotTarget]
      rfl

def parallel {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstEmbedding : TerminalEmbedding firstNetwork firstImage)
    (secondEmbedding : TerminalEmbedding secondNetwork secondImage) :
    TerminalEmbedding (parTTN firstNetwork secondNetwork) (parTTN firstImage secondImage) where
  vertices := parallelVertices firstEmbedding secondEmbedding
  source := by change Sum.inl (firstEmbedding.vertices firstNetwork.a)=Sum.inl firstImage.a; rw [firstEmbedding.source]
  target := by change Sum.inl (firstEmbedding.vertices firstNetwork.b)=Sum.inl firstImage.b; rw [firstEmbedding.target]

def terminalVertices (network : TTN) : Bool ↪ network.V where
  toFun := fun vertex => if vertex then network.b else network.a
  inj' := by
    intro first second equality
    cases first <;> cases second <;> simp_all [network.hab, Ne.symm network.hab]

end TerminalEmbedding

/-- Explicit incidence witnesses for two consecutive actual open edges. -/
def TwoEdgePath (network : TTN) (first last : network.V) : Prop :=
  ∃ firstEdge secondEdge : network.E,
    network.tail firstEdge=first ∧ network.head firstEdge=network.tail secondEdge ∧ network.head secondEdge=last

theorem TwoEdgePath.edgePath {network : TTN} {first last : network.V}
    (path : TwoEdgePath network first last) : network.EdgePath first last := by
  rcases path with ⟨firstEdge,secondEdge,firstEqual,middleEqual,lastEqual⟩
  rw [← firstEqual, ← lastEqual]
  exact edgePath_trans (edgePath_edge network firstEdge)
    (middleEqual.symm ▸ edgePath_edge network secondEdge)

structure TwoStepEmbedding (firstNetwork secondNetwork : TTN)
    extends TerminalEmbedding firstNetwork secondNetwork where
  edge_steps : ∀ edge, TwoEdgePath secondNetwork (vertices (firstNetwork.tail edge))
    (vertices (firstNetwork.head edge))

namespace TwoStepEmbedding

def series {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstEmbedding : TwoStepEmbedding firstNetwork firstImage)
    (secondEmbedding : TwoStepEmbedding secondNetwork secondImage) :
    TwoStepEmbedding (seriesTTN firstNetwork secondNetwork) (seriesTTN firstImage secondImage) where
  toTerminalEmbedding := firstEmbedding.toTerminalEmbedding.series secondEmbedding.toTerminalEmbedding
  edge_steps := by
    rintro (edge | edge)
    · rcases firstEmbedding.edge_steps edge with ⟨firstEdge,secondEdge,firstEqual,middleEqual,lastEqual⟩
      exact ⟨Sum.inl firstEdge,Sum.inl secondEdge,congrArg Sum.inl firstEqual,
        congrArg Sum.inl middleEqual,congrArg Sum.inl lastEqual⟩
    · rcases secondEmbedding.edge_steps edge with ⟨firstEdge,secondEdge,firstEqual,middleEqual,lastEqual⟩
      refine ⟨Sum.inr firstEdge,Sum.inr secondEdge,?_,?_,?_⟩
      · change seriesEmb firstImage secondImage (secondImage.tail firstEdge) =
          TerminalEmbedding.seriesVertices _ _ (seriesEmb firstNetwork secondNetwork (secondNetwork.tail edge))
        rw [TerminalEmbedding.seriesVertices_right,firstEqual]
      · exact congrArg (seriesEmb firstImage secondImage) middleEqual
      · change seriesEmb firstImage secondImage (secondImage.head secondEdge) =
          TerminalEmbedding.seriesVertices _ _ (seriesEmb firstNetwork secondNetwork (secondNetwork.head edge))
        rw [TerminalEmbedding.seriesVertices_right,lastEqual]

def parallel {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstEmbedding : TwoStepEmbedding firstNetwork firstImage)
    (secondEmbedding : TwoStepEmbedding secondNetwork secondImage) :
    TwoStepEmbedding (parTTN firstNetwork secondNetwork) (parTTN firstImage secondImage) where
  toTerminalEmbedding := firstEmbedding.toTerminalEmbedding.parallel secondEmbedding.toTerminalEmbedding
  edge_steps := by
    rintro (edge | edge)
    · rcases firstEmbedding.edge_steps edge with ⟨firstEdge,secondEdge,firstEqual,middleEqual,lastEqual⟩
      exact ⟨Sum.inl firstEdge,Sum.inl secondEdge,congrArg Sum.inl firstEqual,
        congrArg Sum.inl middleEqual,congrArg Sum.inl lastEqual⟩
    · rcases secondEmbedding.edge_steps edge with ⟨firstEdge,secondEdge,firstEqual,middleEqual,lastEqual⟩
      refine ⟨Sum.inr firstEdge,Sum.inr secondEdge,?_,?_,?_⟩
      · change parEmb firstImage secondImage (secondImage.tail firstEdge) =
          TerminalEmbedding.parallelVertices _ _ (parEmb firstNetwork secondNetwork (secondNetwork.tail edge))
        rw [TerminalEmbedding.parallelVertices_right,firstEqual]
      · exact congrArg (parEmb firstImage secondImage) middleEqual
      · change parEmb firstImage secondImage (secondImage.head secondEdge) =
          TerminalEmbedding.parallelVertices _ _ (parEmb firstNetwork secondNetwork (secondNetwork.head edge))
        rw [TerminalEmbedding.parallelVertices_right,lastEqual]

def fromOpen (network : TTN) (connected : TwoEdgePath network network.a network.b) :
    TwoStepEmbedding edgeTTN network where
  vertices := TerminalEmbedding.terminalVertices network
  source := rfl
  target := rfl
  edge_steps := fun _ => connected

def fromClosed (network : TTN) : TwoStepEmbedding gapTTN network where
  vertices := TerminalEmbedding.terminalVertices network
  source := rfl
  target := rfl
  edge_steps := fun edge => nomatch edge

theorem edgePath_forward {firstNetwork secondNetwork : TTN}
    (embedding : TwoStepEmbedding firstNetwork secondNetwork) {first last : firstNetwork.V}
    (path : firstNetwork.EdgePath first last) :
    secondNetwork.EdgePath (embedding.vertices first) (embedding.vertices last) :=
  edgePath_map firstNetwork secondNetwork embedding.vertices
    (fun edge => (embedding.edge_steps edge).edgePath) path

end TwoStepEmbedding
end Cluster.TTN

namespace Outlook.FourColourActualCoarseEmbedding
open Cluster

theorem open_diamond_two_edges (configuration : Conf 1) (connected : conn 1 configuration=true) :
    TTN.TwoEdgePath (net 1 configuration) (net 1 configuration).a (net 1 configuration).b := by
  rcases configuration with ⟨first,second,third,fourth⟩
  change (first && second || third && fourth)=true at connected
  simp only [Bool.or_eq_true, Bool.and_eq_true] at connected
  rcases connected with ⟨firstOpen, secondOpen⟩ | ⟨thirdOpen, fourthOpen⟩
  ·
    subst first; subst second
    refine ⟨Sum.inl (Sum.inl ()),Sum.inl (Sum.inr ()),?_,?_,?_⟩
    all_goals simp [net, TTN.parTTN, TTN.seriesTTN, TTN.edgeTTN, TTN.seriesEmb]
  · subst third; subst fourth
    refine ⟨Sum.inr (Sum.inl ()),Sum.inr (Sum.inr ()),?_,?_,?_⟩
    all_goals simp [net, TTN.parTTN, TTN.seriesTTN, TTN.edgeTTN, TTN.seriesEmb, TTN.parEmb]

/-- Each actual coarse vertex is planted into the next actual generation.
Every actual coarse open edge carries its two explicit fine open edges. -/
def actualOldEmbedding : (depth : ℕ) → (configuration : Conf (depth+1)) →
    TTN.TwoStepEmbedding (net depth (coarse depth configuration)) (net (depth+1) configuration)
  | 0, configuration => by
      change TTN.TwoStepEmbedding (if conn 1 configuration = true then TTN.edgeTTN else TTN.gapTTN)
        (net 1 configuration)
      split
      · next connected =>
          exact TTN.TwoStepEmbedding.fromOpen _ (open_diamond_two_edges configuration connected)
      · exact TTN.TwoStepEmbedding.fromClosed _
  | depth+1, configuration =>
      TTN.TwoStepEmbedding.parallel
        (TTN.TwoStepEmbedding.series (actualOldEmbedding depth configuration.1)
          (actualOldEmbedding depth configuration.2.1))
        (TTN.TwoStepEmbedding.series (actualOldEmbedding depth configuration.2.2.1)
          (actualOldEmbedding depth configuration.2.2.2))

theorem actual_old_vertices_injective (depth : ℕ) (configuration : Conf (depth+1)) :
    Function.Injective (actualOldEmbedding depth configuration).vertices :=
  (actualOldEmbedding depth configuration).vertices.injective

theorem actual_coarse_open_edge_two_steps (depth : ℕ) (configuration : Conf (depth+1))
    (edge : (net depth (coarse depth configuration)).E) :
    TTN.TwoEdgePath (net (depth+1) configuration)
      ((actualOldEmbedding depth configuration).vertices ((net depth (coarse depth configuration)).tail edge))
      ((actualOldEmbedding depth configuration).vertices ((net depth (coarse depth configuration)).head edge)) :=
  (actualOldEmbedding depth configuration).edge_steps edge

theorem actual_source_membership_forward (depth : ℕ) (configuration : Conf (depth+1))
    (vertex : (net depth (coarse depth configuration)).V)
    (active : (net depth (coarse depth configuration)).EdgePath (net depth (coarse depth configuration)).a vertex) :
    (net (depth+1) configuration).EdgePath (net (depth+1) configuration).a
      ((actualOldEmbedding depth configuration).vertices vertex) := by
  have lifted := (actualOldEmbedding depth configuration).edgePath_forward active
  rw [(actualOldEmbedding depth configuration).source] at lifted
  exact lifted

end Outlook.FourColourActualCoarseEmbedding

#print axioms Outlook.FourColourActualCoarseEmbedding.open_diamond_two_edges
#print axioms Outlook.FourColourActualCoarseEmbedding.actualOldEmbedding
#print axioms Outlook.FourColourActualCoarseEmbedding.actual_old_vertices_injective
#print axioms Outlook.FourColourActualCoarseEmbedding.actual_coarse_open_edge_two_steps
#print axioms Outlook.FourColourActualCoarseEmbedding.actual_source_membership_forward
