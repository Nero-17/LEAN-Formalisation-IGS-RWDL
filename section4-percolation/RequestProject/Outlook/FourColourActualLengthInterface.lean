import RequestProject.Outlook.FourColourActualCoarseRetraction
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! Actual old/new vertex alternation and length-two walk lifting.
The reverse length inequality additionally needs common-new-neighbor compression;
it is not a premise of any actual result below. -/
namespace Cluster.TTN

/-- Actual right-child planting in series is injective. -/
theorem seriesEmb_injective (firstNetwork secondNetwork : TTN) :
    Function.Injective (seriesEmb firstNetwork secondNetwork) := by
  intro first last equality
  have projected := congrArg (seriesRightRetraction firstNetwork secondNetwork) equality
  simpa only [seriesRightRetraction_emb] using projected

/-- Actual right-child planting in parallel is injective, including both terminals. -/
theorem parEmb_injective (firstNetwork secondNetwork : TTN) :
    Function.Injective (parEmb firstNetwork secondNetwork) := by
  intro first last equality
  by_cases source : first = secondNetwork.a
  · subst first
    have boundary := (parEmb_eq_inl firstNetwork secondNetwork last firstNetwork.a).mp
      (by simpa only [parEmb, dif_pos rfl] using equality.symm)
    rcases boundary with source | target
    · exact source.1.symm
    · exact (firstNetwork.hab target.2.symm).elim
  · by_cases target : first = secondNetwork.b
    · subst first
      have boundary := (parEmb_eq_inl firstNetwork secondNetwork last firstNetwork.b).mp
        (by simpa only [parEmb, dif_neg source, dif_pos rfl] using equality.symm)
      rcases boundary with source | target
      · exact (firstNetwork.hab source.2).elim
      · exact target.1.symm
    · have interior := (parEmb_eq_inr firstNetwork secondNetwork last ⟨first, source, target⟩).mp
        (by simpa only [parEmb, dif_neg source, dif_neg target] using equality.symm)
      exact interior.symm

/-- Incidence-preserving injections carry genuine adjacency to genuine adjacency. -/
theorem adjacent_map_incidence {firstNetwork secondNetwork : TTN}
    (vertices : firstNetwork.V → secondNetwork.V) (injective : Function.Injective vertices)
    (edges : firstNetwork.E → secondNetwork.E)
    (tail : ∀ edge, secondNetwork.tail (edges edge) = vertices (firstNetwork.tail edge))
    (head : ∀ edge, secondNetwork.head (edges edge) = vertices (firstNetwork.head edge))
    {first last : firstNetwork.V} (adjacent : firstNetwork.underlyingGraph.Adj first last) :
    secondNetwork.underlyingGraph.Adj (vertices first) (vertices last) := by
  refine ⟨fun equality => adjacent.1 (injective equality), ?_⟩
  rcases adjacent.2 with ⟨edge, firstEqual, lastEqual⟩ | ⟨edge, lastEqual, firstEqual⟩
  · exact Or.inl ⟨edges edge, by rw [tail, firstEqual], by rw [head, lastEqual]⟩
  · exact Or.inr ⟨edges edge, by rw [tail, lastEqual], by rw [head, firstEqual]⟩

theorem series_left_adjacent (firstNetwork secondNetwork : TTN)
    {first last : firstNetwork.V} (adjacent : firstNetwork.underlyingGraph.Adj first last) :
    (seriesTTN firstNetwork secondNetwork).underlyingGraph.Adj (Sum.inl first) (Sum.inl last) :=
  adjacent_map_incidence (firstNetwork := firstNetwork) (secondNetwork := seriesTTN firstNetwork secondNetwork)
    Sum.inl (fun _ _ equality => Sum.inl.inj equality) Sum.inl (fun _ => rfl) (fun _ => rfl) adjacent

theorem series_right_adjacent (firstNetwork secondNetwork : TTN)
    {first last : secondNetwork.V} (adjacent : secondNetwork.underlyingGraph.Adj first last) :
    (seriesTTN firstNetwork secondNetwork).underlyingGraph.Adj
      (seriesEmb firstNetwork secondNetwork first) (seriesEmb firstNetwork secondNetwork last) :=
  adjacent_map_incidence (firstNetwork := secondNetwork) (secondNetwork := seriesTTN firstNetwork secondNetwork)
    (seriesEmb firstNetwork secondNetwork) (seriesEmb_injective _ _) Sum.inr
    (fun _ => rfl) (fun _ => rfl) adjacent

theorem parallel_left_adjacent (firstNetwork secondNetwork : TTN)
    {first last : firstNetwork.V} (adjacent : firstNetwork.underlyingGraph.Adj first last) :
    (parTTN firstNetwork secondNetwork).underlyingGraph.Adj (Sum.inl first) (Sum.inl last) :=
  adjacent_map_incidence (firstNetwork := firstNetwork) (secondNetwork := parTTN firstNetwork secondNetwork)
    Sum.inl (fun _ _ equality => Sum.inl.inj equality) Sum.inl (fun _ => rfl) (fun _ => rfl) adjacent

theorem parallel_right_adjacent (firstNetwork secondNetwork : TTN)
    {first last : secondNetwork.V} (adjacent : secondNetwork.underlyingGraph.Adj first last) :
    (parTTN firstNetwork secondNetwork).underlyingGraph.Adj
      (parEmb firstNetwork secondNetwork first) (parEmb firstNetwork secondNetwork last) :=
  adjacent_map_incidence (firstNetwork := secondNetwork) (secondNetwork := parTTN firstNetwork secondNetwork)
    (parEmb firstNetwork secondNetwork) (parEmb_injective _ _) Sum.inr
    (fun _ => rfl) (fun _ => rfl) adjacent

namespace TerminalEmbedding

theorem series_left_pullback {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstEmbedding : TerminalEmbedding firstNetwork firstImage)
    (secondEmbedding : TerminalEmbedding secondNetwork secondImage)
    (original : (seriesTTN firstNetwork secondNetwork).V) (leftFine : firstImage.V)
    (equality : seriesVertices firstEmbedding secondEmbedding original = Sum.inl leftFine) :
    ∃ leftCoarse, original = Sum.inl leftCoarse ∧ firstEmbedding.vertices leftCoarse = leftFine := by
  cases original with
  | inl original => exact ⟨original, rfl, Sum.inl.inj equality⟩
  | inr original => cases equality

theorem parallel_left_pullback {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstEmbedding : TerminalEmbedding firstNetwork firstImage)
    (secondEmbedding : TerminalEmbedding secondNetwork secondImage)
    (original : (parTTN firstNetwork secondNetwork).V) (leftFine : firstImage.V)
    (equality : parallelVertices firstEmbedding secondEmbedding original = Sum.inl leftFine) :
    ∃ leftCoarse, original = Sum.inl leftCoarse ∧ firstEmbedding.vertices leftCoarse = leftFine := by
  cases original with
  | inl original => exact ⟨original, rfl, Sum.inl.inj equality⟩
  | inr original => cases equality

theorem series_right_pullback {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstEmbedding : TerminalEmbedding firstNetwork firstImage)
    (secondEmbedding : TerminalEmbedding secondNetwork secondImage)
    (original : (seriesTTN firstNetwork secondNetwork).V) (rightFine : secondImage.V)
    (equality : seriesVertices firstEmbedding secondEmbedding original =
      seriesEmb firstImage secondImage rightFine) :
    ∃ rightCoarse, original = seriesEmb firstNetwork secondNetwork rightCoarse ∧
      secondEmbedding.vertices rightCoarse = rightFine := by
  cases original with
  | inl original =>
      change Sum.inl (firstEmbedding.vertices original) = seriesEmb firstImage secondImage rightFine at equality
      have boundary := (seriesEmb_eq_inl firstImage secondImage rightFine (firstEmbedding.vertices original)).mp equality.symm
      have originalTarget : original = firstNetwork.b :=
        (firstEmbedding.vertex_eq_target_iff original).mp boundary.2.symm
      refine ⟨secondNetwork.a, ?_, ?_⟩
      · simp [seriesEmb, originalTarget]
      · rw [secondEmbedding.source, boundary.1]
  | inr original =>
      change Sum.inr (secondEmbedding.exceptSource original) = seriesEmb firstImage secondImage rightFine at equality
      have interior := (seriesEmb_eq_inr firstImage secondImage rightFine (secondEmbedding.exceptSource original)).mp equality.symm
      refine ⟨original.1, ?_, interior.symm⟩
      simp [seriesEmb, original.2]

theorem parallel_right_pullback {firstNetwork secondNetwork firstImage secondImage : TTN}
    (firstEmbedding : TerminalEmbedding firstNetwork firstImage)
    (secondEmbedding : TerminalEmbedding secondNetwork secondImage)
    (original : (parTTN firstNetwork secondNetwork).V) (rightFine : secondImage.V)
    (equality : parallelVertices firstEmbedding secondEmbedding original =
      parEmb firstImage secondImage rightFine) :
    ∃ rightCoarse, original = parEmb firstNetwork secondNetwork rightCoarse ∧
      secondEmbedding.vertices rightCoarse = rightFine := by
  cases original with
  | inl original =>
      change Sum.inl (firstEmbedding.vertices original) = parEmb firstImage secondImage rightFine at equality
      have boundary := (parEmb_eq_inl firstImage secondImage rightFine (firstEmbedding.vertices original)).mp equality.symm
      rcases boundary with source | target
      · have originalSource : original = firstNetwork.a :=
          (firstEmbedding.vertex_eq_source_iff original).mp source.2.symm
        refine ⟨secondNetwork.a, ?_, ?_⟩
        · simp [parEmb, originalSource]
        · rw [secondEmbedding.source, source.1]
      · have originalTarget : original = firstNetwork.b :=
          (firstEmbedding.vertex_eq_target_iff original).mp target.2.symm
        refine ⟨secondNetwork.b, ?_, ?_⟩
        · simp [parEmb, originalTarget, Ne.symm secondNetwork.hab]
        · rw [secondEmbedding.target, target.1]
  | inr original =>
      change Sum.inr (secondEmbedding.interior original) = parEmb firstImage secondImage rightFine at equality
      have interior := (parEmb_eq_inr firstImage secondImage rightFine (secondEmbedding.interior original)).mp equality.symm
      refine ⟨original.1, ?_, interior.symm⟩
      simp [parEmb, original.2.1, original.2.2]

end TerminalEmbedding

/-- A genuine colouring of the fine vertices, identifying precisely the old image. -/
structure OldNewPartition {coarseNetwork fineNetwork : TTN}
    (embedding : TerminalEmbedding coarseNetwork fineNetwork) where
  old : fineNetwork.V → Bool
  source : old fineNetwork.a = true
  target : old fineNetwork.b = true
  old_iff : ∀ vertex, old vertex = true ↔ ∃ original, embedding.vertices original = vertex
  edge_alternates : ∀ edge, old (fineNetwork.tail edge) ≠ old (fineNetwork.head edge)

/-- Finite actual incidence decides the underlying graph adjacency relation. -/
instance underlyingGraphAdjDecidable (network : TTN) : DecidableRel network.underlyingGraph.Adj :=
  fun first last => by
    change Decidable (first ≠ last ∧
      ((∃ edge : network.E, network.tail edge = first ∧ network.head edge = last) ∨
       (∃ edge : network.E, network.tail edge = last ∧ network.head edge = first)))
    infer_instance

namespace OldNewPartition

/-- A genuinely new left vertex cannot be a shared series junction. -/
theorem new_inl_ne_series_right {coarseNetwork firstImage : TTN}
    {embedding : TerminalEmbedding coarseNetwork firstImage}
    (partition : OldNewPartition embedding) (secondImage : TTN)
    (middle : firstImage.V) (newVertex : partition.old middle = false)
    (rightVertex : secondImage.V) :
    (Sum.inl middle : (seriesTTN firstImage secondImage).V) ≠
      seriesEmb firstImage secondImage rightVertex := by
  intro equality
  have junction := (seriesEmb_eq_inl firstImage secondImage rightVertex middle).mp equality.symm
  have oldVertex : partition.old middle = true := by
    rw [← junction.2]
    exact partition.target
  rw [newVertex] at oldVertex
  cases oldVertex

/-- A genuinely new left vertex cannot be either shared parallel terminal. -/
theorem new_inl_ne_parallel_right {coarseNetwork firstImage : TTN}
    {embedding : TerminalEmbedding coarseNetwork firstImage}
    (partition : OldNewPartition embedding) (secondImage : TTN)
    (middle : firstImage.V) (newVertex : partition.old middle = false)
    (rightVertex : secondImage.V) :
    (Sum.inl middle : (parTTN firstImage secondImage).V) ≠
      parEmb firstImage secondImage rightVertex := by
  intro equality
  have boundary := (parEmb_eq_inl firstImage secondImage rightVertex middle).mp equality.symm
  have oldVertex : partition.old middle = true := by
    rcases boundary with source | target
    · rw [← source.2]
      exact partition.source
    · rw [← target.2]
      exact partition.target
  rw [newVertex] at oldVertex
  cases oldVertex

def seriesColour {firstNetwork secondNetwork firstImage secondImage : TTN}
    {firstEmbedding : TerminalEmbedding firstNetwork firstImage}
    {secondEmbedding : TerminalEmbedding secondNetwork secondImage}
    (firstPartition : OldNewPartition firstEmbedding)
    (secondPartition : OldNewPartition secondEmbedding) :
    (seriesTTN firstImage secondImage).V → Bool :=
  Sum.elim firstPartition.old (fun vertex => secondPartition.old vertex.1)

theorem seriesColour_right {firstNetwork secondNetwork firstImage secondImage : TTN}
    {firstEmbedding : TerminalEmbedding firstNetwork firstImage}
    {secondEmbedding : TerminalEmbedding secondNetwork secondImage}
    (firstPartition : OldNewPartition firstEmbedding)
    (secondPartition : OldNewPartition secondEmbedding) (vertex : secondImage.V) :
    seriesColour firstPartition secondPartition (seriesEmb firstImage secondImage vertex) =
      secondPartition.old vertex := by
  by_cases source : vertex = secondImage.a
  · subst vertex
    simp [seriesEmb, seriesColour, firstPartition.target, secondPartition.source]
  · simp [seriesEmb, seriesColour, source]

def series {firstNetwork secondNetwork firstImage secondImage : TTN}
    {firstEmbedding : TerminalEmbedding firstNetwork firstImage}
    {secondEmbedding : TerminalEmbedding secondNetwork secondImage}
    (firstPartition : OldNewPartition firstEmbedding)
    (secondPartition : OldNewPartition secondEmbedding) :
    OldNewPartition (firstEmbedding.series secondEmbedding) where
  old := seriesColour firstPartition secondPartition
  source := firstPartition.source
  target := by
    change seriesColour firstPartition secondPartition (seriesEmb firstImage secondImage secondImage.b) = true
    rw [seriesColour_right, secondPartition.target]
  old_iff := by
    rintro (vertex | vertex)
    · change firstPartition.old vertex = true ↔ _
      rw [firstPartition.old_iff]
      constructor
      · rintro ⟨original, equality⟩
        exact ⟨Sum.inl original, congrArg Sum.inl equality⟩
      · rintro ⟨original | original, equality⟩
        · exact ⟨original, Sum.inl.inj equality⟩
        · cases equality
    · change secondPartition.old vertex.1 = true ↔ _
      rw [secondPartition.old_iff]
      constructor
      · rintro ⟨original, equality⟩
        have distinct : original ≠ secondNetwork.a := by
          intro source
          apply vertex.2
          rw [← equality, source, secondEmbedding.source]
        refine ⟨Sum.inr ⟨original, distinct⟩, ?_⟩
        change Sum.inr (secondEmbedding.exceptSource ⟨original, distinct⟩) = Sum.inr vertex
        exact congrArg Sum.inr (Subtype.ext equality)
      · rintro ⟨original | original, equality⟩
        · cases equality
        · change Sum.inr (secondEmbedding.exceptSource original) = Sum.inr vertex at equality
          exact ⟨original.1, congrArg Subtype.val (Sum.inr.inj equality)⟩
  edge_alternates := by
    rintro (edge | edge)
    · exact firstPartition.edge_alternates edge
    · change seriesColour firstPartition secondPartition (seriesEmb firstImage secondImage (secondImage.tail edge)) ≠
        seriesColour firstPartition secondPartition (seriesEmb firstImage secondImage (secondImage.head edge))
      rw [seriesColour_right, seriesColour_right]
      exact secondPartition.edge_alternates edge

def parallelColour {firstNetwork secondNetwork firstImage secondImage : TTN}
    {firstEmbedding : TerminalEmbedding firstNetwork firstImage}
    {secondEmbedding : TerminalEmbedding secondNetwork secondImage}
    (firstPartition : OldNewPartition firstEmbedding)
    (secondPartition : OldNewPartition secondEmbedding) :
    (parTTN firstImage secondImage).V → Bool :=
  Sum.elim firstPartition.old (fun vertex => secondPartition.old vertex.1)

theorem parallelColour_right {firstNetwork secondNetwork firstImage secondImage : TTN}
    {firstEmbedding : TerminalEmbedding firstNetwork firstImage}
    {secondEmbedding : TerminalEmbedding secondNetwork secondImage}
    (firstPartition : OldNewPartition firstEmbedding)
    (secondPartition : OldNewPartition secondEmbedding) (vertex : secondImage.V) :
    parallelColour firstPartition secondPartition (parEmb firstImage secondImage vertex) =
      secondPartition.old vertex := by
  by_cases source : vertex = secondImage.a
  · subst vertex
    simp [parEmb, parallelColour, firstPartition.source, secondPartition.source]
  · by_cases target : vertex = secondImage.b
    · subst vertex
      simp [parEmb, parallelColour, source, firstPartition.target, secondPartition.target]
    · simp [parEmb, parallelColour, source, target]

def parallel {firstNetwork secondNetwork firstImage secondImage : TTN}
    {firstEmbedding : TerminalEmbedding firstNetwork firstImage}
    {secondEmbedding : TerminalEmbedding secondNetwork secondImage}
    (firstPartition : OldNewPartition firstEmbedding)
    (secondPartition : OldNewPartition secondEmbedding) :
    OldNewPartition (firstEmbedding.parallel secondEmbedding) where
  old := parallelColour firstPartition secondPartition
  source := firstPartition.source
  target := firstPartition.target
  old_iff := by
    rintro (vertex | vertex)
    · change firstPartition.old vertex = true ↔ _
      rw [firstPartition.old_iff]
      constructor
      · rintro ⟨original, equality⟩
        exact ⟨Sum.inl original, congrArg Sum.inl equality⟩
      · rintro ⟨original | original, equality⟩
        · exact ⟨original, Sum.inl.inj equality⟩
        · cases equality
    · change secondPartition.old vertex.1 = true ↔ _
      rw [secondPartition.old_iff]
      constructor
      · rintro ⟨original, equality⟩
        have distinctSource : original ≠ secondNetwork.a := by
          intro source
          apply vertex.2.1
          rw [← equality, source, secondEmbedding.source]
        have distinctTarget : original ≠ secondNetwork.b := by
          intro target
          apply vertex.2.2
          rw [← equality, target, secondEmbedding.target]
        refine ⟨Sum.inr ⟨original, distinctSource, distinctTarget⟩, ?_⟩
        change Sum.inr (secondEmbedding.interior ⟨original, distinctSource, distinctTarget⟩) = Sum.inr vertex
        exact congrArg Sum.inr (Subtype.ext equality)
      · rintro ⟨original | original, equality⟩
        · cases equality
        · change Sum.inr (secondEmbedding.interior original) = Sum.inr vertex at equality
          exact ⟨original.1, congrArg Subtype.val (Sum.inr.inj equality)⟩
  edge_alternates := by
    rintro (edge | edge)
    · exact firstPartition.edge_alternates edge
    · change parallelColour firstPartition secondPartition (parEmb firstImage secondImage (secondImage.tail edge)) ≠
        parallelColour firstPartition secondPartition (parEmb firstImage secondImage (secondImage.head edge))
      rw [parallelColour_right, parallelColour_right]
      exact secondPartition.edge_alternates edge

theorem loopless {coarseNetwork fineNetwork : TTN}
    {embedding : TerminalEmbedding coarseNetwork fineNetwork}
    (partition : OldNewPartition embedding) (edge : fineNetwork.E) :
    fineNetwork.tail edge ≠ fineNetwork.head edge := by
  intro equality
  exact partition.edge_alternates edge (congrArg partition.old equality)

theorem adjacent_alternates {coarseNetwork fineNetwork : TTN}
    {embedding : TerminalEmbedding coarseNetwork fineNetwork}
    (partition : OldNewPartition embedding) {first last : fineNetwork.V}
    (adjacent : fineNetwork.underlyingGraph.Adj first last) :
    partition.old first ≠ partition.old last := by
  rcases adjacent.2 with ⟨edge, rfl, rfl⟩ | ⟨edge, rfl, rfl⟩
  · exact partition.edge_alternates edge
  · exact Ne.symm (partition.edge_alternates edge)

/-- A neighbor of a new left vertex must come from the actual left child. -/
theorem series_left_neighbor_pullback {firstNetwork secondNetwork firstImage secondImage : TTN}
    {firstEmbedding : TerminalEmbedding firstNetwork firstImage}
    {secondEmbedding : TerminalEmbedding secondNetwork secondImage}
    (firstPartition : OldNewPartition firstEmbedding)
    (secondPartition : OldNewPartition secondEmbedding)
    (original : (seriesTTN firstNetwork secondNetwork).V)
    (middle : firstImage.V) (newVertex : firstPartition.old middle = false)
    (adjacent : (seriesTTN firstImage secondImage).underlyingGraph.Adj
      (TerminalEmbedding.seriesVertices firstEmbedding secondEmbedding original) (Sum.inl middle)) :
    ∃ leftCoarse, original = Sum.inl leftCoarse ∧
      firstImage.underlyingGraph.Adj (firstEmbedding.vertices leftCoarse) middle := by
  rcases adjacent.2 with ⟨edge | edge, tail, head⟩ | ⟨edge | edge, tail, head⟩
  · obtain ⟨leftCoarse, originalEqual, imageEqual⟩ :=
      firstEmbedding.series_left_pullback secondEmbedding original (firstImage.tail edge) tail.symm
    have middleEqual : firstImage.head edge = middle := Sum.inl.inj head
    refine ⟨leftCoarse, originalEqual, ?_⟩
    exact ⟨by rw [imageEqual, ← middleEqual]; exact firstPartition.loopless edge,
      Or.inl ⟨edge, imageEqual.symm, middleEqual⟩⟩
  · exact (firstPartition.new_inl_ne_series_right secondImage middle newVertex (secondImage.head edge) head.symm).elim
  · obtain ⟨leftCoarse, originalEqual, imageEqual⟩ :=
      firstEmbedding.series_left_pullback secondEmbedding original (firstImage.head edge) head.symm
    have middleEqual : firstImage.tail edge = middle := Sum.inl.inj tail
    refine ⟨leftCoarse, originalEqual, ?_⟩
    exact ⟨by rw [imageEqual, ← middleEqual]; exact Ne.symm (firstPartition.loopless edge),
      Or.inr ⟨edge, middleEqual, imageEqual.symm⟩⟩
  · exact (firstPartition.new_inl_ne_series_right secondImage middle newVertex (secondImage.tail edge) tail.symm).elim

/-- At a right interior midpoint, both the incident edge and old endpoint pull back. -/
theorem series_right_neighbor_pullback {firstNetwork secondNetwork firstImage secondImage : TTN}
    {firstEmbedding : TerminalEmbedding firstNetwork firstImage}
    {secondEmbedding : TerminalEmbedding secondNetwork secondImage}
    (firstPartition : OldNewPartition firstEmbedding)
    (secondPartition : OldNewPartition secondEmbedding)
    (original : (seriesTTN firstNetwork secondNetwork).V)
    (middle : {vertex : secondImage.V // vertex ≠ secondImage.a})
    (adjacent : (seriesTTN firstImage secondImage).underlyingGraph.Adj
      (TerminalEmbedding.seriesVertices firstEmbedding secondEmbedding original) (Sum.inr middle)) :
    ∃ rightCoarse, original = seriesEmb firstNetwork secondNetwork rightCoarse ∧
      secondImage.underlyingGraph.Adj (secondEmbedding.vertices rightCoarse) middle.1 := by
  rcases adjacent.2 with ⟨edge | edge, tail, head⟩ | ⟨edge | edge, tail, head⟩
  · cases head
  · obtain ⟨rightCoarse, originalEqual, imageEqual⟩ :=
      firstEmbedding.series_right_pullback secondEmbedding original (secondImage.tail edge) tail.symm
    have middleEqual : secondImage.head edge = middle.1 :=
      (seriesEmb_eq_inr firstImage secondImage (secondImage.head edge) middle).mp head
    refine ⟨rightCoarse, originalEqual, ?_⟩
    exact ⟨by rw [imageEqual, ← middleEqual]; exact secondPartition.loopless edge,
      Or.inl ⟨edge, imageEqual.symm, middleEqual⟩⟩
  · cases tail
  · obtain ⟨rightCoarse, originalEqual, imageEqual⟩ :=
      firstEmbedding.series_right_pullback secondEmbedding original (secondImage.head edge) head.symm
    have middleEqual : secondImage.tail edge = middle.1 :=
      (seriesEmb_eq_inr firstImage secondImage (secondImage.tail edge) middle).mp tail
    refine ⟨rightCoarse, originalEqual, ?_⟩
    exact ⟨by rw [imageEqual, ← middleEqual]; exact Ne.symm (secondPartition.loopless edge),
      Or.inr ⟨edge, middleEqual, imageEqual.symm⟩⟩

/-- A neighbor of a new left vertex must come from the actual left child. -/
theorem parallel_left_neighbor_pullback {firstNetwork secondNetwork firstImage secondImage : TTN}
    {firstEmbedding : TerminalEmbedding firstNetwork firstImage}
    {secondEmbedding : TerminalEmbedding secondNetwork secondImage}
    (firstPartition : OldNewPartition firstEmbedding)
    (secondPartition : OldNewPartition secondEmbedding)
    (original : (parTTN firstNetwork secondNetwork).V)
    (middle : firstImage.V) (newVertex : firstPartition.old middle = false)
    (adjacent : (parTTN firstImage secondImage).underlyingGraph.Adj
      (TerminalEmbedding.parallelVertices firstEmbedding secondEmbedding original) (Sum.inl middle)) :
    ∃ leftCoarse, original = Sum.inl leftCoarse ∧
      firstImage.underlyingGraph.Adj (firstEmbedding.vertices leftCoarse) middle := by
  rcases adjacent.2 with ⟨edge | edge, tail, head⟩ | ⟨edge | edge, tail, head⟩
  · obtain ⟨leftCoarse, originalEqual, imageEqual⟩ :=
      firstEmbedding.parallel_left_pullback secondEmbedding original (firstImage.tail edge) tail.symm
    have middleEqual : firstImage.head edge = middle := Sum.inl.inj head
    refine ⟨leftCoarse, originalEqual, ?_⟩
    exact ⟨by rw [imageEqual, ← middleEqual]; exact firstPartition.loopless edge,
      Or.inl ⟨edge, imageEqual.symm, middleEqual⟩⟩
  · exact (firstPartition.new_inl_ne_parallel_right secondImage middle newVertex (secondImage.head edge) head.symm).elim
  · obtain ⟨leftCoarse, originalEqual, imageEqual⟩ :=
      firstEmbedding.parallel_left_pullback secondEmbedding original (firstImage.head edge) head.symm
    have middleEqual : firstImage.tail edge = middle := Sum.inl.inj tail
    refine ⟨leftCoarse, originalEqual, ?_⟩
    exact ⟨by rw [imageEqual, ← middleEqual]; exact Ne.symm (firstPartition.loopless edge),
      Or.inr ⟨edge, middleEqual, imageEqual.symm⟩⟩
  · exact (firstPartition.new_inl_ne_parallel_right secondImage middle newVertex (secondImage.tail edge) tail.symm).elim

/-- At a right interior midpoint, both the incident edge and old endpoint pull back. -/
theorem parallel_right_neighbor_pullback {firstNetwork secondNetwork firstImage secondImage : TTN}
    {firstEmbedding : TerminalEmbedding firstNetwork firstImage}
    {secondEmbedding : TerminalEmbedding secondNetwork secondImage}
    (firstPartition : OldNewPartition firstEmbedding)
    (secondPartition : OldNewPartition secondEmbedding)
    (original : (parTTN firstNetwork secondNetwork).V)
    (middle : {vertex : secondImage.V // vertex ≠ secondImage.a ∧ vertex ≠ secondImage.b})
    (adjacent : (parTTN firstImage secondImage).underlyingGraph.Adj
      (TerminalEmbedding.parallelVertices firstEmbedding secondEmbedding original) (Sum.inr middle)) :
    ∃ rightCoarse, original = parEmb firstNetwork secondNetwork rightCoarse ∧
      secondImage.underlyingGraph.Adj (secondEmbedding.vertices rightCoarse) middle.1 := by
  rcases adjacent.2 with ⟨edge | edge, tail, head⟩ | ⟨edge | edge, tail, head⟩
  · cases head
  · obtain ⟨rightCoarse, originalEqual, imageEqual⟩ :=
      firstEmbedding.parallel_right_pullback secondEmbedding original (secondImage.tail edge) tail.symm
    have middleEqual : secondImage.head edge = middle.1 :=
      (parEmb_eq_inr firstImage secondImage (secondImage.head edge) middle).mp head
    refine ⟨rightCoarse, originalEqual, ?_⟩
    exact ⟨by rw [imageEqual, ← middleEqual]; exact secondPartition.loopless edge,
      Or.inl ⟨edge, imageEqual.symm, middleEqual⟩⟩
  · cases tail
  · obtain ⟨rightCoarse, originalEqual, imageEqual⟩ :=
      firstEmbedding.parallel_right_pullback secondEmbedding original (secondImage.head edge) head.symm
    have middleEqual : secondImage.tail edge = middle.1 :=
      (parEmb_eq_inr firstImage secondImage (secondImage.tail edge) middle).mp tail
    refine ⟨rightCoarse, originalEqual, ?_⟩
    exact ⟨by rw [imageEqual, ← middleEqual]; exact Ne.symm (secondPartition.loopless edge),
      Or.inr ⟨edge, middleEqual, imageEqual.symm⟩⟩

end OldNewPartition

/-- A two-edge fine route between old vertices compresses to a return or a coarse edge. -/
def ReflectsTwoSteps {coarseNetwork fineNetwork : TTN}
    (embedding : TerminalEmbedding coarseNetwork fineNetwork) : Prop :=
  ∀ (first last : coarseNetwork.V) (middle : fineNetwork.V),
    fineNetwork.underlyingGraph.Adj (embedding.vertices first) middle →
    fineNetwork.underlyingGraph.Adj middle (embedding.vertices last) →
    first = last ∨ coarseNetwork.underlyingGraph.Adj first last

namespace ReflectsTwoSteps

theorem series {firstNetwork secondNetwork firstImage secondImage : TTN}
    {firstEmbedding : TerminalEmbedding firstNetwork firstImage}
    {secondEmbedding : TerminalEmbedding secondNetwork secondImage}
    (firstPartition : OldNewPartition firstEmbedding)
    (secondPartition : OldNewPartition secondEmbedding)
    (firstReflection : ReflectsTwoSteps firstEmbedding)
    (secondReflection : ReflectsTwoSteps secondEmbedding) :
    ReflectsTwoSteps (firstEmbedding.series secondEmbedding) := by
  intro first last middle firstAdjacent lastAdjacent
  let partition := firstPartition.series secondPartition
  have firstOld : partition.old ((firstEmbedding.series secondEmbedding).vertices first) = true :=
    (partition.old_iff _).mpr ⟨first, rfl⟩
  have different := partition.adjacent_alternates firstAdjacent
  have middleNew : partition.old middle = false := by
    rw [firstOld] at different
    cases value : partition.old middle <;> simp_all
  cases middle with
  | inl middle =>
      change firstPartition.old middle = false at middleNew
      obtain ⟨firstCoarse, firstEqual, firstChildAdjacent⟩ :=
        firstPartition.series_left_neighbor_pullback secondPartition first middle middleNew firstAdjacent
      obtain ⟨lastCoarse, lastEqual, lastChildAdjacent⟩ :=
        firstPartition.series_left_neighbor_pullback secondPartition last middle middleNew lastAdjacent.symm
      rcases firstReflection firstCoarse lastCoarse middle firstChildAdjacent lastChildAdjacent.symm with equality | adjacent
      · exact Or.inl (by rw [firstEqual, lastEqual, equality])
      · apply Or.inr
        rw [firstEqual, lastEqual]
        exact series_left_adjacent firstNetwork secondNetwork adjacent
  | inr middle =>
      obtain ⟨firstCoarse, firstEqual, firstChildAdjacent⟩ :=
        firstPartition.series_right_neighbor_pullback secondPartition first middle firstAdjacent
      obtain ⟨lastCoarse, lastEqual, lastChildAdjacent⟩ :=
        firstPartition.series_right_neighbor_pullback secondPartition last middle lastAdjacent.symm
      rcases secondReflection firstCoarse lastCoarse middle.1 firstChildAdjacent lastChildAdjacent.symm with equality | adjacent
      · exact Or.inl (by rw [firstEqual, lastEqual, equality])
      · apply Or.inr
        rw [firstEqual, lastEqual]
        exact series_right_adjacent firstNetwork secondNetwork adjacent

theorem parallel {firstNetwork secondNetwork firstImage secondImage : TTN}
    {firstEmbedding : TerminalEmbedding firstNetwork firstImage}
    {secondEmbedding : TerminalEmbedding secondNetwork secondImage}
    (firstPartition : OldNewPartition firstEmbedding)
    (secondPartition : OldNewPartition secondEmbedding)
    (firstReflection : ReflectsTwoSteps firstEmbedding)
    (secondReflection : ReflectsTwoSteps secondEmbedding) :
    ReflectsTwoSteps (firstEmbedding.parallel secondEmbedding) := by
  intro first last middle firstAdjacent lastAdjacent
  let partition := firstPartition.parallel secondPartition
  have firstOld : partition.old ((firstEmbedding.parallel secondEmbedding).vertices first) = true :=
    (partition.old_iff _).mpr ⟨first, rfl⟩
  have different := partition.adjacent_alternates firstAdjacent
  have middleNew : partition.old middle = false := by
    rw [firstOld] at different
    cases value : partition.old middle <;> simp_all
  cases middle with
  | inl middle =>
      change firstPartition.old middle = false at middleNew
      obtain ⟨firstCoarse, firstEqual, firstChildAdjacent⟩ :=
        firstPartition.parallel_left_neighbor_pullback secondPartition first middle middleNew firstAdjacent
      obtain ⟨lastCoarse, lastEqual, lastChildAdjacent⟩ :=
        firstPartition.parallel_left_neighbor_pullback secondPartition last middle middleNew lastAdjacent.symm
      rcases firstReflection firstCoarse lastCoarse middle firstChildAdjacent lastChildAdjacent.symm with equality | adjacent
      · exact Or.inl (by rw [firstEqual, lastEqual, equality])
      · apply Or.inr
        rw [firstEqual, lastEqual]
        exact parallel_left_adjacent firstNetwork secondNetwork adjacent
  | inr middle =>
      obtain ⟨firstCoarse, firstEqual, firstChildAdjacent⟩ :=
        firstPartition.parallel_right_neighbor_pullback secondPartition first middle firstAdjacent
      obtain ⟨lastCoarse, lastEqual, lastChildAdjacent⟩ :=
        firstPartition.parallel_right_neighbor_pullback secondPartition last middle lastAdjacent.symm
      rcases secondReflection firstCoarse lastCoarse middle.1 firstChildAdjacent lastChildAdjacent.symm with equality | adjacent
      · exact Or.inl (by rw [firstEqual, lastEqual, equality])
      · apply Or.inr
        rw [firstEqual, lastEqual]
        exact parallel_right_adjacent firstNetwork secondNetwork adjacent

end ReflectsTwoSteps

/-- Turn real incidence witnesses into a real walk, using actual absence of loops. -/
theorem TwoEdgePath.exists_walk_length_two {network : TTN} {first last : network.V}
    (path : TwoEdgePath network first last)
    (loopless : ∀ edge : network.E, network.tail edge ≠ network.head edge) :
    ∃ walk : network.underlyingGraph.Walk first last, walk.length = 2 := by
  rcases path with ⟨firstEdge, secondEdge, firstEqual, middleEqual, lastEqual⟩
  have firstAdjacent : network.underlyingGraph.Adj first (network.tail secondEdge) :=
    ⟨by rw [← firstEqual, ← middleEqual]; exact loopless firstEdge,
      Or.inl ⟨firstEdge, firstEqual, middleEqual⟩⟩
  have secondAdjacent : network.underlyingGraph.Adj (network.tail secondEdge) last :=
    ⟨by rw [← lastEqual]; exact loopless secondEdge, Or.inl ⟨secondEdge, rfl, lastEqual⟩⟩
  exact ⟨.cons firstAdjacent (.cons secondAdjacent .nil), rfl⟩

namespace TwoStepEmbedding

theorem adjacent_walk_length_two {coarseNetwork fineNetwork : TTN}
    (embedding : TwoStepEmbedding coarseNetwork fineNetwork)
    (loopless : ∀ edge : fineNetwork.E, fineNetwork.tail edge ≠ fineNetwork.head edge)
    {first last : coarseNetwork.V} (adjacent : coarseNetwork.underlyingGraph.Adj first last) :
    ∃ walk : fineNetwork.underlyingGraph.Walk (embedding.vertices first) (embedding.vertices last),
      walk.length = 2 := by
  rcases adjacent.2 with ⟨edge, rfl, rfl⟩ | ⟨edge, rfl, rfl⟩
  · exact (embedding.edge_steps edge).exists_walk_length_two loopless
  · obtain ⟨walk, length⟩ := (embedding.edge_steps edge).exists_walk_length_two loopless
    exact ⟨walk.reverse, by simpa only [SimpleGraph.Walk.length_reverse] using length⟩

theorem walk_lift_exact_length {coarseNetwork fineNetwork : TTN}
    (embedding : TwoStepEmbedding coarseNetwork fineNetwork)
    (loopless : ∀ edge : fineNetwork.E, fineNetwork.tail edge ≠ fineNetwork.head edge)
    {first last : coarseNetwork.V} (walk : coarseNetwork.underlyingGraph.Walk first last) :
    ∃ lifted : fineNetwork.underlyingGraph.Walk (embedding.vertices first) (embedding.vertices last),
      lifted.length = 2 * walk.length := by
  induction walk with
  | nil => exact ⟨.nil, rfl⟩
  | cons adjacent walk induction =>
      obtain ⟨step, stepLength⟩ := embedding.adjacent_walk_length_two loopless adjacent
      obtain ⟨rest, restLength⟩ := induction
      refine ⟨step.append rest, ?_⟩
      rw [SimpleGraph.Walk.length_append, stepLength, restLength, SimpleGraph.Walk.length_cons]
      omega

end TwoStepEmbedding
end Cluster.TTN

namespace Outlook.FourColourActualLengthInterface
open Cluster Outlook.FourColourActualCoarseEmbedding

/-- Endpoints are old; the two actual diamond midpoints are new. -/
def diamondOldFlag :
    (TTN.parTTN (TTN.seriesTTN TTN.edgeTTN TTN.edgeTTN)
      (TTN.seriesTTN TTN.edgeTTN TTN.edgeTTN)).V → Bool :=
  Sum.elim (Sum.elim (fun vertex : Bool => !vertex) (fun _ => true))
    (fun vertex => Sum.elim (fun endpoint : Bool => !endpoint) (fun _ => true) vertex.1)

def diamondPartition (configuration : Conf 1) :
    TTN.OldNewPartition (actualOldEmbedding 0 configuration).toTerminalEmbedding := by
  rcases configuration with ⟨first, second, third, fourth⟩
  cases first <;> cases second <;> cases third <;> cases fourth
  all_goals exact {
    old := diamondOldFlag
    source := rfl
    target := rfl
    old_iff := by decide
    edge_alternates := by decide
  }

/-- A real two-step fine walk in one diamond compresses to a coarse edge or a return.
This statement checks the actual sixteen configurations and all actual vertices. -/
theorem diamond_common_neighbor (configuration : Conf 1) :
    ∀ (first last : (net 0 (coarse 0 configuration)).V) (middle : (net 1 configuration).V),
      (net 1 configuration).underlyingGraph.Adj
        ((actualOldEmbedding 0 configuration).vertices first) middle →
      (net 1 configuration).underlyingGraph.Adj middle
        ((actualOldEmbedding 0 configuration).vertices last) →
      first = last ∨ (net 0 (coarse 0 configuration)).underlyingGraph.Adj first last := by
  rcases configuration with ⟨first, second, third, fourth⟩
  cases first <;> cases second <;> cases third <;> cases fourth
  all_goals decide

def actualPartition : (depth : ℕ) → (configuration : Conf (depth + 1)) →
    TTN.OldNewPartition (actualOldEmbedding depth configuration).toTerminalEmbedding
  | 0, configuration => diamondPartition configuration
  | depth + 1, configuration =>
      TTN.OldNewPartition.parallel
        (TTN.OldNewPartition.series (actualPartition depth configuration.1)
          (actualPartition depth configuration.2.1))
        (TTN.OldNewPartition.series (actualPartition depth configuration.2.2.1)
          (actualPartition depth configuration.2.2.2))

/-- Recursive local compression on the actual net/coarse pair, with no geometric premise. -/
theorem actual_two_step_reflection : (depth : ℕ) → (configuration : Conf (depth + 1)) →
    TTN.ReflectsTwoSteps (actualOldEmbedding depth configuration).toTerminalEmbedding
  | 0, configuration => diamond_common_neighbor configuration
  | depth + 1, configuration =>
      TTN.ReflectsTwoSteps.parallel
        (TTN.OldNewPartition.series (actualPartition depth configuration.1)
          (actualPartition depth configuration.2.1))
        (TTN.OldNewPartition.series (actualPartition depth configuration.2.2.1)
          (actualPartition depth configuration.2.2.2))
        (TTN.ReflectsTwoSteps.series (actualPartition depth configuration.1)
          (actualPartition depth configuration.2.1)
          (actual_two_step_reflection depth configuration.1)
          (actual_two_step_reflection depth configuration.2.1))
        (TTN.ReflectsTwoSteps.series (actualPartition depth configuration.2.2.1)
          (actualPartition depth configuration.2.2.2)
          (actual_two_step_reflection depth configuration.2.2.1)
          (actual_two_step_reflection depth configuration.2.2.2))

theorem actual_old_image_iff (depth : ℕ) (configuration : Conf (depth + 1))
    (vertex : (net (depth + 1) configuration).V) :
    (actualPartition depth configuration).old vertex = true ↔
      ∃ original, (actualOldEmbedding depth configuration).vertices original = vertex :=
  (actualPartition depth configuration).old_iff vertex

theorem actual_fine_edge_alternates (depth : ℕ) (configuration : Conf (depth + 1))
    (edge : (net (depth + 1) configuration).E) :
    (actualPartition depth configuration).old ((net (depth + 1) configuration).tail edge) ≠
      (actualPartition depth configuration).old ((net (depth + 1) configuration).head edge) :=
  (actualPartition depth configuration).edge_alternates edge

theorem actual_walk_lift_exact_length (depth : ℕ) (configuration : Conf (depth + 1))
    {first last : (net depth (coarse depth configuration)).V}
    (walk : (net depth (coarse depth configuration)).underlyingGraph.Walk first last) :
    ∃ lifted : (net (depth + 1) configuration).underlyingGraph.Walk
        ((actualOldEmbedding depth configuration).vertices first)
        ((actualOldEmbedding depth configuration).vertices last),
      lifted.length = 2 * walk.length :=
  (actualOldEmbedding depth configuration).walk_lift_exact_length
    (actualPartition depth configuration).loopless walk

theorem actual_edist_le_twice (depth : ℕ) (configuration : Conf (depth + 1))
    (first last : (net depth (coarse depth configuration)).V) :
    (net (depth + 1) configuration).underlyingGraph.edist
        ((actualOldEmbedding depth configuration).vertices first)
        ((actualOldEmbedding depth configuration).vertices last) ≤
      2 * (net depth (coarse depth configuration)).underlyingGraph.edist first last := by
  by_cases reachable : (net depth (coarse depth configuration)).underlyingGraph.Reachable first last
  · obtain ⟨walk, shortest⟩ := reachable.exists_walk_length_eq_edist
    obtain ⟨lifted, length⟩ := actual_walk_lift_exact_length depth configuration walk
    calc
      _ ≤ (lifted.length : ℕ∞) := lifted.edist_le
      _ = 2 * (net depth (coarse depth configuration)).underlyingGraph.edist first last := by
        rw [length, Nat.cast_mul, shortest]
        rfl
  · rw [SimpleGraph.edist_eq_top_of_not_reachable reachable]
    simp

end Outlook.FourColourActualLengthInterface

#print axioms Outlook.FourColourActualLengthInterface.diamond_common_neighbor
#print axioms Outlook.FourColourActualLengthInterface.actual_two_step_reflection
#print axioms Outlook.FourColourActualLengthInterface.actualPartition
#print axioms Outlook.FourColourActualLengthInterface.actual_old_image_iff
#print axioms Outlook.FourColourActualLengthInterface.actual_fine_edge_alternates
#print axioms Outlook.FourColourActualLengthInterface.actual_walk_lift_exact_length
#print axioms Outlook.FourColourActualLengthInterface.actual_edist_le_twice
