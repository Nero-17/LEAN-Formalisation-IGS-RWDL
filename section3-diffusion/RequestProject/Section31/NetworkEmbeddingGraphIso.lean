import RequestProject.Section31.NetworkSubstitutionEmbedding
import RequestProject.Section31.NetworkCellEmbeddingSurjectivity

namespace EIGS.Network.ColourEmbedding
open scoped Classical
noncomputable section
variable {K : ℕ} {source target : EIGS.Network K}
    (embedding : ColourEmbedding source target)

theorem incidentClosed_of_edge_surjective (edges : Function.Surjective embedding.edge)
    (vertex : source.V) : embedding.IncidentClosedAt vertex := by
  intro edge _
  exact edges edge

/-- A literal network embedding which exhausts both carriers induces the
actual undirected graph isomorphism. No adjacency identification is assumed. -/
def graphIso (vertices : Function.Surjective embedding.vertex)
    (edges : Function.Surjective embedding.edge) :
    source.toSimpleGraph ≃g target.toSimpleGraph where
  toEquiv := Equiv.ofBijective embedding.vertex ⟨embedding.vertex.injective, vertices⟩
  map_rel_iff' := by
    intro first second
    exact embedding.adj_iff_of_incidentClosedAt first
      (embedding.incidentClosed_of_edge_surjective edges first) second

theorem connected_iff_of_surjective (vertices : Function.Surjective embedding.vertex)
    (edges : Function.Surjective embedding.edge) :
    source.toSimpleGraph.Connected ↔ target.toSimpleGraph.Connected :=
  (embedding.graphIso vertices edges).connected_iff

theorem positive_degree_of_surjective (vertices : Function.Surjective embedding.vertex)
    (edges : Function.Surjective embedding.edge)
    (positive : ∀ vertex, 0 < target.toSimpleGraph.degree vertex) :
    ∀ vertex, 0 < source.toSimpleGraph.degree vertex := by
  intro vertex
  rw [← embedding.degree_of_incidentClosedAt vertex
    (embedding.incidentClosed_of_edge_surjective edges vertex)]
  exact positive _

end
end EIGS.Network.ColourEmbedding

#print axioms EIGS.Network.ColourEmbedding.graphIso
#print axioms EIGS.Network.ColourEmbedding.connected_iff_of_surjective
#print axioms EIGS.Network.ColourEmbedding.positive_degree_of_surjective
