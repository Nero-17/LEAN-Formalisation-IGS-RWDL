import RequestProject.Section31.NetworkSubstitutionEmbedding
import RequestProject.Section31.WatchedChain

/-!
Conductance rows formed from the actual coloured electrical edges. Parallel
edges retain their multiplicities. Incident closure derives every row
identity; no transition-kernel localization is supplied as a hypothesis.
-/

namespace EIGS.Network

open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

/-- Sum the conductances of actual oriented edges joining the two vertices,
in either orientation. Each edge is counted once, including a possible loop. -/
def colourConductance (network : EIGS.Network K) (weights : Fin K → ℝ)
    (first second : network.V) : ℝ :=
  ∑ edge : network.E,
    if (network.tail edge = first ∧ network.head edge = second) ∨
        (network.tail edge = second ∧ network.head edge = first)
    then weights (network.color edge) else 0

theorem colourConductance_nonnegative (network : EIGS.Network K) (weights : Fin K → ℝ)
    (nonnegative : ∀ colour, 0 ≤ weights colour) (first second : network.V) :
    0 ≤ network.colourConductance weights first second := by
  apply Finset.sum_nonneg
  intro edge _
  split_ifs
  · exact nonnegative _
  · exact le_refl _

/-- A genuine finite conductance chain. Positivity is a condition for the
chain to be defined, while all embedding transport is proved below. -/
def colourConductanceChain (network : EIGS.Network K) (weights : Fin K → ℝ)
    (nonnegative : ∀ colour, 0 ≤ weights colour)
    (positive : ∀ vertex, 0 < ∑ other, network.colourConductance weights vertex other) :
    IGS.Sec31.FinChain network.V :=
  IGS.Sec31.condChain (network.colourConductance weights)
    (network.colourConductance_nonnegative weights nonnegative) positive

namespace ColourEmbedding

variable {source target : EIGS.Network K} (embedding : ColourEmbedding source target)

/-- Restrict the ambient conductance sum to the exact embedded edge set. -/
theorem colourConductance_edge_sum (weights : Fin K → ℝ) (vertex : source.V)
    (closed : embedding.IncidentClosedAt vertex) (other : target.V) :
    target.colourConductance weights (embedding.vertex vertex) other =
      ∑ edge : source.E,
        if (target.tail (embedding.edge edge) = embedding.vertex vertex ∧
            target.head (embedding.edge edge) = other) ∨
            (target.tail (embedding.edge edge) = other ∧
              target.head (embedding.edge edge) = embedding.vertex vertex)
        then weights (target.color (embedding.edge edge)) else 0 := by
  apply embedding.sum_edges_of_incidentClosedAt vertex closed
  intro edge not_tail not_head
  split_ifs with endpoints
  · rcases endpoints with endpoints | endpoints
    · exact (not_tail endpoints.1).elim
    · exact (not_head endpoints.2).elim
  · rfl

theorem colourConductance_map (weights : Fin K → ℝ) (vertex : source.V)
    (closed : embedding.IncidentClosedAt vertex) (other : source.V) :
    target.colourConductance weights (embedding.vertex vertex) (embedding.vertex other) =
      source.colourConductance weights vertex other := by
  rw [embedding.colourConductance_edge_sum weights vertex closed]
  unfold colourConductance
  apply Finset.sum_congr rfl
  intro edge _
  simp only [← embedding.tail edge, ← embedding.head edge,
    embedding.vertex.injective.eq_iff, ← embedding.colour edge]

theorem colourConductance_zero_outside (weights : Fin K → ℝ) (vertex : source.V)
    (closed : embedding.IncidentClosedAt vertex) (other : target.V)
    (outside : other ∉ Set.range embedding.vertex) :
    target.colourConductance weights (embedding.vertex vertex) other = 0 := by
  rw [embedding.colourConductance_edge_sum weights vertex closed]
  apply Finset.sum_eq_zero
  intro edge _
  split_ifs with endpoints
  · rcases endpoints with endpoints | endpoints
    · exact (outside ⟨source.head edge, (embedding.head edge).trans endpoints.2⟩).elim
    · exact (outside ⟨source.tail edge, (embedding.tail edge).trans endpoints.1⟩).elim
  · rfl

theorem colourConductance_rowMass (weights : Fin K → ℝ) (vertex : source.V)
    (closed : embedding.IncidentClosedAt vertex) :
    (∑ other : target.V, target.colourConductance weights (embedding.vertex vertex) other) =
      ∑ other : source.V, source.colourConductance weights vertex other := by
  have restrictSum :
      (∑ other ∈ Finset.univ.image embedding.vertex,
        target.colourConductance weights (embedding.vertex vertex) other) =
      ∑ other : target.V, target.colourConductance weights (embedding.vertex vertex) other := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro other _ outsideImage
    apply embedding.colourConductance_zero_outside weights vertex closed other
    rintro ⟨original, rfl⟩
    exact outsideImage (Finset.mem_image.mpr ⟨original, Finset.mem_univ _, rfl⟩)
  rw [← restrictSum]
  rw [Finset.sum_image (fun first _ second _ same => embedding.vertex.injective same)]
  apply Finset.sum_congr rfl
  intro other _
  exact embedding.colourConductance_map weights vertex closed other

theorem colourConductanceChain_map (weights : Fin K → ℝ)
    (nonnegative : ∀ colour, 0 ≤ weights colour)
    (source_positive : ∀ vertex, 0 < ∑ other, source.colourConductance weights vertex other)
    (target_positive : ∀ vertex, 0 < ∑ other, target.colourConductance weights vertex other)
    (vertex : source.V) (closed : embedding.IncidentClosedAt vertex) (other : source.V) :
    (target.colourConductanceChain weights nonnegative target_positive).P
        (embedding.vertex vertex) (embedding.vertex other) =
      (source.colourConductanceChain weights nonnegative source_positive).P vertex other := by
  change target.colourConductance weights (embedding.vertex vertex) (embedding.vertex other) /
      (∑ other, target.colourConductance weights (embedding.vertex vertex) other) =
    source.colourConductance weights vertex other /
      (∑ other, source.colourConductance weights vertex other)
  rw [embedding.colourConductance_map weights vertex closed other,
    embedding.colourConductance_rowMass weights vertex closed]

theorem colourConductanceChain_zero_outside (weights : Fin K → ℝ)
    (nonnegative : ∀ colour, 0 ≤ weights colour)
    (positive : ∀ vertex, 0 < ∑ other, target.colourConductance weights vertex other)
    (vertex : source.V) (closed : embedding.IncidentClosedAt vertex) (other : target.V)
    (outside : other ∉ Set.range embedding.vertex) :
    (target.colourConductanceChain weights nonnegative positive).P
      (embedding.vertex vertex) other = 0 := by
  change target.colourConductance weights (embedding.vertex vertex) other / _ = 0
  rw [embedding.colourConductance_zero_outside weights vertex closed other outside, zero_div]

end ColourEmbedding
end
end EIGS.Network

#print axioms EIGS.Network.colourConductance_nonnegative
#print axioms EIGS.Network.colourConductanceChain
#print axioms EIGS.Network.ColourEmbedding.colourConductance_edge_sum
#print axioms EIGS.Network.ColourEmbedding.colourConductance_map
#print axioms EIGS.Network.ColourEmbedding.colourConductance_zero_outside
#print axioms EIGS.Network.ColourEmbedding.colourConductance_rowMass
#print axioms EIGS.Network.ColourEmbedding.colourConductanceChain_map
#print axioms EIGS.Network.ColourEmbedding.colourConductanceChain_zero_outside
