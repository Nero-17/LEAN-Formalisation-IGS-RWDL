import RequestProject.Outlook.FourColourActualCoarseEmbedding

/-! Actual fine-to-coarse path retractions. These reflect connectivity of the
specific old-vertex injection and do not assert length control or isometry. -/
namespace Cluster.TTN

structure TerminalPathMap (firstNetwork secondNetwork : TTN) where
  mapping : firstNetwork.V → secondNetwork.V
  source : mapping firstNetwork.a = secondNetwork.a
  target : mapping firstNetwork.b = secondNetwork.b
  edge_paths : ∀ edge, secondNetwork.EdgePath (mapping (firstNetwork.tail edge))
    (mapping (firstNetwork.head edge))

namespace TerminalPathMap

def seriesMapping {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstMap : TerminalPathMap firstNetwork firstImage)
    (secondMap : TerminalPathMap secondNetwork secondImage) :
    (seriesTTN firstNetwork secondNetwork).V → (seriesTTN firstImage secondImage).V :=
  Sum.elim (fun vertex => Sum.inl (firstMap.mapping vertex))
    (fun vertex => seriesEmb firstImage secondImage (secondMap.mapping vertex.1))

theorem seriesMapping_right {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstMap : TerminalPathMap firstNetwork firstImage)
    (secondMap : TerminalPathMap secondNetwork secondImage) (vertex : secondNetwork.V) :
    seriesMapping firstMap secondMap (seriesEmb firstNetwork secondNetwork vertex) =
      seriesEmb firstImage secondImage (secondMap.mapping vertex) := by
  by_cases source : vertex = secondNetwork.a
  · subst vertex
    simp [seriesMapping, seriesEmb, secondMap.source, firstMap.target]
  · simp [seriesMapping, seriesEmb, source]

def series {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstMap : TerminalPathMap firstNetwork firstImage)
    (secondMap : TerminalPathMap secondNetwork secondImage) :
    TerminalPathMap (seriesTTN firstNetwork secondNetwork) (seriesTTN firstImage secondImage) where
  mapping := seriesMapping firstMap secondMap
  source := by change Sum.inl (firstMap.mapping firstNetwork.a) = Sum.inl firstImage.a; rw [firstMap.source]
  target := by
    change seriesMapping firstMap secondMap (seriesEmb firstNetwork secondNetwork secondNetwork.b) = _
    rw [seriesMapping_right, secondMap.target]
    rfl
  edge_paths := by
    rintro (edge | edge)
    · exact series_left_path firstImage secondImage (firstMap.edge_paths edge)
    · change (seriesTTN firstImage secondImage).EdgePath
        (seriesMapping firstMap secondMap (seriesEmb firstNetwork secondNetwork (secondNetwork.tail edge)))
        (seriesMapping firstMap secondMap (seriesEmb firstNetwork secondNetwork (secondNetwork.head edge)))
      rw [seriesMapping_right, seriesMapping_right]
      exact series_right_path firstImage secondImage (secondMap.edge_paths edge)

def parallelMapping {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstMap : TerminalPathMap firstNetwork firstImage)
    (secondMap : TerminalPathMap secondNetwork secondImage) :
    (parTTN firstNetwork secondNetwork).V → (parTTN firstImage secondImage).V :=
  Sum.elim (fun vertex => Sum.inl (firstMap.mapping vertex))
    (fun vertex => parEmb firstImage secondImage (secondMap.mapping vertex.1))

theorem parallelMapping_right {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstMap : TerminalPathMap firstNetwork firstImage)
    (secondMap : TerminalPathMap secondNetwork secondImage) (vertex : secondNetwork.V) :
    parallelMapping firstMap secondMap (parEmb firstNetwork secondNetwork vertex) =
      parEmb firstImage secondImage (secondMap.mapping vertex) := by
  by_cases source : vertex = secondNetwork.a
  · subst vertex
    simp [parallelMapping, parEmb, secondMap.source, firstMap.source]
  · by_cases target : vertex = secondNetwork.b
    · subst vertex
      simp [parallelMapping, parEmb, source, secondMap.target, firstMap.target, Ne.symm secondImage.hab]
    · simp [parallelMapping, parEmb, source, target]

def parallel {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstMap : TerminalPathMap firstNetwork firstImage)
    (secondMap : TerminalPathMap secondNetwork secondImage) :
    TerminalPathMap (parTTN firstNetwork secondNetwork) (parTTN firstImage secondImage) where
  mapping := parallelMapping firstMap secondMap
  source := by change Sum.inl (firstMap.mapping firstNetwork.a) = Sum.inl firstImage.a; rw [firstMap.source]
  target := by change Sum.inl (firstMap.mapping firstNetwork.b) = Sum.inl firstImage.b; rw [firstMap.target]
  edge_paths := by
    rintro (edge | edge)
    · exact parallel_left_path firstImage secondImage (firstMap.edge_paths edge)
    · change (parTTN firstImage secondImage).EdgePath
        (parallelMapping firstMap secondMap (parEmb firstNetwork secondNetwork (secondNetwork.tail edge)))
        (parallelMapping firstMap secondMap (parEmb firstNetwork secondNetwork (secondNetwork.head edge)))
      rw [parallelMapping_right, parallelMapping_right]
      exact parallel_right_path firstImage secondImage (secondMap.edge_paths edge)

theorem edgePath_forward {firstNetwork secondNetwork : TTN}
    (mapping : TerminalPathMap firstNetwork secondNetwork) {first last : firstNetwork.V}
    (path : firstNetwork.EdgePath first last) :
    secondNetwork.EdgePath (mapping.mapping first) (mapping.mapping last) :=
  edgePath_map firstNetwork secondNetwork mapping.mapping mapping.edge_paths path

end TerminalPathMap

structure PathRetraction {firstNetwork secondNetwork : TTN}
    (embedding : TerminalEmbedding firstNetwork secondNetwork)
    extends TerminalPathMap secondNetwork firstNetwork where
  left_inverse : Function.LeftInverse mapping embedding.vertices

namespace PathRetraction

def series {firstNetwork secondNetwork firstImage secondImage : TTN}
    {firstEmbedding : TerminalEmbedding firstNetwork firstImage}
    {secondEmbedding : TerminalEmbedding secondNetwork secondImage}
    (firstRetraction : PathRetraction firstEmbedding)
    (secondRetraction : PathRetraction secondEmbedding) :
    PathRetraction (firstEmbedding.series secondEmbedding) where
  toTerminalPathMap := firstRetraction.toTerminalPathMap.series secondRetraction.toTerminalPathMap
  left_inverse := by
    rintro (vertex | vertex)
    · change Sum.inl (firstRetraction.mapping (firstEmbedding.vertices vertex)) = Sum.inl vertex
      rw [firstRetraction.left_inverse]
    · change seriesEmb firstNetwork secondNetwork
        (secondRetraction.mapping (secondEmbedding.vertices vertex.1)) = Sum.inr vertex
      rw [secondRetraction.left_inverse]
      simp [seriesEmb, vertex.2]

def parallel {firstNetwork secondNetwork firstImage secondImage : TTN}
    {firstEmbedding : TerminalEmbedding firstNetwork firstImage}
    {secondEmbedding : TerminalEmbedding secondNetwork secondImage}
    (firstRetraction : PathRetraction firstEmbedding)
    (secondRetraction : PathRetraction secondEmbedding) :
    PathRetraction (firstEmbedding.parallel secondEmbedding) where
  toTerminalPathMap := firstRetraction.toTerminalPathMap.parallel secondRetraction.toTerminalPathMap
  left_inverse := by
    rintro (vertex | vertex)
    · change Sum.inl (firstRetraction.mapping (firstEmbedding.vertices vertex)) = Sum.inl vertex
      rw [firstRetraction.left_inverse]
    · change parEmb firstNetwork secondNetwork
        (secondRetraction.mapping (secondEmbedding.vertices vertex.1)) = Sum.inr vertex
      rw [secondRetraction.left_inverse]
      simp [parEmb, vertex.2.1, vertex.2.2]

theorem edgePath_reflect {firstNetwork secondNetwork : TTN}
    {embedding : TerminalEmbedding firstNetwork secondNetwork}
    (retraction : PathRetraction embedding) {first last : firstNetwork.V}
    (path : secondNetwork.EdgePath (embedding.vertices first) (embedding.vertices last)) :
    firstNetwork.EdgePath first last := by
  have projected := retraction.toTerminalPathMap.edgePath_forward path
  have firstEqual : retraction.mapping (embedding.vertices first) = first := retraction.left_inverse first
  have lastEqual : retraction.mapping (embedding.vertices last) = last := retraction.left_inverse last
  rw [firstEqual, lastEqual] at projected
  exact projected

end PathRetraction
end Cluster.TTN

namespace Outlook.FourColourActualCoarseRetraction
open Cluster Outlook.FourColourActualCoarseEmbedding

/-- The two midpoint labels are determined by the actual open left bonds. -/
def diamondCollapse (first third : Bool) :
    (TTN.parTTN (TTN.seriesTTN TTN.edgeTTN TTN.edgeTTN)
      (TTN.seriesTTN TTN.edgeTTN TTN.edgeTTN)).V → Bool :=
  Sum.elim
    (Sum.elim (fun vertex => if vertex = true then !first else false) (fun _ => true))
    (fun vertex => Sum.elim (fun endpoint => if endpoint = true then !third else false)
      (fun _ => true) vertex.1)

/-- Base retraction for each of the sixteen actual configurations. -/
def diamondRetraction (configuration : Conf 1) :
    TTN.PathRetraction (actualOldEmbedding 0 configuration).toTerminalEmbedding := by
  rcases configuration with ⟨first, second, third, fourth⟩
  let collapse := diamondCollapse first third
  cases first <;> cases second <;> cases third <;> cases fourth
  all_goals
    refine {
      mapping := collapse
      source := by rfl
      target := by rfl
      left_inverse := ?_
      edge_paths := ?_
    }
  all_goals
    first
    | (solve | intro vertex; cases vertex <;> rfl)
    | (rintro ((edge | edge) | (edge | edge))
       all_goals
         first
         | (exact Empty.elim edge)
         | (exact TTN.edgePath_self _ _)
         | (exact TTN.edgePath_edge TTN.edgeTTN ())
         | (exact TTN.edgePath_symm (TTN.edgePath_edge TTN.edgeTTN ())))

def actualRetraction : (depth : ℕ) → (configuration : Conf (depth + 1)) →
    TTN.PathRetraction (actualOldEmbedding depth configuration).toTerminalEmbedding
  | 0, configuration => diamondRetraction configuration
  | depth + 1, configuration =>
      TTN.PathRetraction.parallel
        (TTN.PathRetraction.series (actualRetraction depth configuration.1)
          (actualRetraction depth configuration.2.1))
        (TTN.PathRetraction.series (actualRetraction depth configuration.2.2.1)
          (actualRetraction depth configuration.2.2.2))

theorem actual_old_edgePath_iff (depth : ℕ) (configuration : Conf (depth + 1))
    (first last : (net depth (coarse depth configuration)).V) :
    (net (depth + 1) configuration).EdgePath
      ((actualOldEmbedding depth configuration).vertices first)
      ((actualOldEmbedding depth configuration).vertices last) ↔
        (net depth (coarse depth configuration)).EdgePath first last :=
  ⟨(actualRetraction depth configuration).edgePath_reflect,
    (actualOldEmbedding depth configuration).edgePath_forward⟩

theorem actual_source_membership_iff (depth : ℕ) (configuration : Conf (depth + 1))
    (vertex : (net depth (coarse depth configuration)).V) :
    (net (depth + 1) configuration).EdgePath (net (depth + 1) configuration).a
      ((actualOldEmbedding depth configuration).vertices vertex) ↔
        (net depth (coarse depth configuration)).EdgePath (net depth (coarse depth configuration)).a vertex := by
  rw [← (actualOldEmbedding depth configuration).source]
  exact actual_old_edgePath_iff depth configuration _ vertex

theorem actual_old_reachable_iff (depth : ℕ) (configuration : Conf (depth + 1))
    (first last : (net depth (coarse depth configuration)).V) :
    (net (depth + 1) configuration).underlyingGraph.Reachable
      ((actualOldEmbedding depth configuration).vertices first)
      ((actualOldEmbedding depth configuration).vertices last) ↔
        (net depth (coarse depth configuration)).underlyingGraph.Reachable first last := by
  rw [← TTN.edgePath_iff_reachable, ← TTN.edgePath_iff_reachable]
  exact actual_old_edgePath_iff depth configuration first last

end Outlook.FourColourActualCoarseRetraction

#print axioms Outlook.FourColourActualCoarseRetraction.diamondRetraction
#print axioms Outlook.FourColourActualCoarseRetraction.actualRetraction
#print axioms Outlook.FourColourActualCoarseRetraction.actual_old_edgePath_iff
#print axioms Outlook.FourColourActualCoarseRetraction.actual_source_membership_iff
#print axioms Outlook.FourColourActualCoarseRetraction.actual_old_reachable_iff
