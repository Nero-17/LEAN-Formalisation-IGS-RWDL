import RequestProject.Section31.NetworkIteratedCellEmbedding

/-!
Actual incident-edge localization for iterated substitution cells. The
ambient edge set is exhausted at every nonterminal cell vertex. No claim
is made about ambient rows at the two cell terminals.
-/

namespace EIGS.Network

open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

theorem substEmbed_eq_old_iff (network : EIGS.Network K) (rules : EIGS.RuleFamily K)
    (edge : network.E) (child : (rules.R (network.color edge)).V) (vertex : network.V) :
    network.substEmbed rules edge child = Sum.inl vertex ↔
      (child = rules.βplus (network.color edge) ∧ network.tail edge = vertex) ∨
      (child = rules.βminus (network.color edge) ∧ network.head edge = vertex) := by
  unfold Network.substEmbed
  split_ifs <;> simp_all
  all_goals grind [rules.plant_ne]

namespace ColourEmbedding

variable {source target : EIGS.Network K} (embedding : ColourEmbedding source target)

/-- Every ambient edge incident to the image vertex belongs to the embedded
edge set. This is an assertion about actual oriented electrical edges. -/
def IncidentClosedAt (vertex : source.V) : Prop :=
  ∀ ambient : target.E,
    (target.tail ambient = embedding.vertex vertex ∨
      target.head ambient = embedding.vertex vertex) →
    ∃ original : source.E, embedding.edge original = ambient

/-- Exact edge-sum transport, retaining oriented edge multiplicity and
arbitrary edge weights. Conductance numerators and row masses are instances. -/
theorem sum_edges_of_incidentClosedAt (vertex : source.V)
    (closed : embedding.IncidentClosedAt vertex) (values : target.E → ℝ)
    (supported : ∀ edge, target.tail edge ≠ embedding.vertex vertex →
      target.head edge ≠ embedding.vertex vertex → values edge = 0) :
    (∑ edge : target.E, values edge) = ∑ edge : source.E, values (embedding.edge edge) := by
  have restrictSum :
      (∑ edge ∈ Finset.univ.image embedding.edge, values edge) = ∑ edge : target.E, values edge := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro edge _ outsideImage
    have not_incident : ¬ (target.tail edge = embedding.vertex vertex ∨
        target.head edge = embedding.vertex vertex) := by
      intro incident
      obtain ⟨original, same⟩ := closed edge incident
      exact outsideImage (Finset.mem_image.mpr ⟨original, Finset.mem_univ _, same⟩)
    exact supported edge (fun same => not_incident (Or.inl same))
      (fun same => not_incident (Or.inr same))
  rw [← restrictSum]
  exact Finset.sum_image (fun first _ second _ same => embedding.edge.injective same)

theorem map_adj {first second : source.V}
    (adjacency : source.toSimpleGraph.Adj first second) :
    target.toSimpleGraph.Adj (embedding.vertex first) (embedding.vertex second) := by
  refine ⟨embedding.vertex.injective.ne adjacency.1, ?_⟩
  rcases adjacency.2 with ⟨edge, tail, head⟩ | ⟨edge, tail, head⟩
  · exact Or.inl ⟨embedding.edge edge, (embedding.tail edge).symm.trans (congrArg embedding.vertex tail),
      (embedding.head edge).symm.trans (congrArg embedding.vertex head)⟩
  · exact Or.inr ⟨embedding.edge edge, (embedding.tail edge).symm.trans (congrArg embedding.vertex tail),
      (embedding.head edge).symm.trans (congrArg embedding.vertex head)⟩

theorem neighbor_iff_of_incidentClosedAt (vertex : source.V)
    (closed : embedding.IncidentClosedAt vertex) (neighbor : target.V) :
    target.toSimpleGraph.Adj (embedding.vertex vertex) neighbor ↔
      ∃ other : source.V, source.toSimpleGraph.Adj vertex other ∧
        embedding.vertex other = neighbor := by
  constructor
  · intro adjacency
    rcases adjacency.2 with ⟨edge, tail, head⟩ | ⟨edge, tail, head⟩
    · obtain ⟨original, same⟩ := closed edge (Or.inl tail)
      have source_tail : source.tail original = vertex := embedding.vertex.injective
        ((embedding.tail original).trans ((congrArg target.tail same).trans tail))
      have source_head : embedding.vertex (source.head original) = neighbor :=
        (embedding.head original).trans ((congrArg target.head same).trans head)
      refine ⟨source.head original, ⟨?_, Or.inl ⟨original, source_tail, rfl⟩⟩, source_head⟩
      intro equal
      exact adjacency.1 ((congrArg embedding.vertex equal).trans source_head)
    · obtain ⟨original, same⟩ := closed edge (Or.inr head)
      have source_head : source.head original = vertex := embedding.vertex.injective
        ((embedding.head original).trans ((congrArg target.head same).trans head))
      have source_tail : embedding.vertex (source.tail original) = neighbor :=
        (embedding.tail original).trans ((congrArg target.tail same).trans tail)
      refine ⟨source.tail original, ⟨?_, Or.inr ⟨original, rfl, source_head⟩⟩, source_tail⟩
      intro equal
      exact adjacency.1 ((congrArg embedding.vertex equal).trans source_tail)
  · rintro ⟨other, adjacency, rfl⟩
    exact embedding.map_adj adjacency

theorem adj_iff_of_incidentClosedAt (vertex : source.V)
    (closed : embedding.IncidentClosedAt vertex) (other : source.V) :
    target.toSimpleGraph.Adj (embedding.vertex vertex) (embedding.vertex other) ↔
      source.toSimpleGraph.Adj vertex other := by
  rw [embedding.neighbor_iff_of_incidentClosedAt vertex closed]
  constructor
  · rintro ⟨candidate, adjacency, same⟩
    exact embedding.vertex.injective same ▸ adjacency
  · intro adjacency
    exact ⟨other, adjacency, rfl⟩

def neighborEquivOfIncidentClosedAt (vertex : source.V)
    (closed : embedding.IncidentClosedAt vertex) :
    source.toSimpleGraph.neighborSet vertex ≃
      target.toSimpleGraph.neighborSet (embedding.vertex vertex) :=
  Equiv.ofBijective (fun other => ⟨embedding.vertex other.val, embedding.map_adj other.property⟩) (by
    constructor
    · intro first second same
      exact Subtype.ext (embedding.vertex.injective (congrArg Subtype.val same))
    · intro neighbor
      obtain ⟨other, adjacency, same⟩ :=
        (embedding.neighbor_iff_of_incidentClosedAt vertex closed neighbor.val).mp neighbor.property
      exact ⟨⟨other, adjacency⟩, Subtype.ext same⟩)

theorem degree_of_incidentClosedAt (vertex : source.V)
    (closed : embedding.IncidentClosedAt vertex) :
    target.toSimpleGraph.degree (embedding.vertex vertex) = source.toSimpleGraph.degree vertex := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  exact (Fintype.card_congr (embedding.neighborEquivOfIncidentClosedAt vertex closed)).symm

theorem transProb_of_incidentClosedAt (vertex : source.V)
    (closed : embedding.IncidentClosedAt vertex) (other : source.V) :
    EIGS.transProb target.toSimpleGraph (embedding.vertex vertex) (embedding.vertex other) =
      EIGS.transProb source.toSimpleGraph vertex other := by
  simp only [EIGS.transProb, embedding.adj_iff_of_incidentClosedAt vertex closed,
    embedding.degree_of_incidentClosedAt vertex closed]

theorem transProb_zero_outside_of_incidentClosedAt (vertex : source.V)
    (closed : embedding.IncidentClosedAt vertex) (other : target.V)
    (outside : other ∉ Set.range embedding.vertex) :
    EIGS.transProb target.toSimpleGraph (embedding.vertex vertex) other = 0 := by
  have not_adjacent : ¬ target.toSimpleGraph.Adj (embedding.vertex vertex) other := by
    intro adjacency
    obtain ⟨preimage, _, same⟩ :=
      (embedding.neighbor_iff_of_incidentClosedAt vertex closed other).mp adjacency
    exact outside ⟨preimage, same⟩
  simp [EIGS.transProb, not_adjacent]

theorem substEdge_surjective_over_image (rules : EIGS.RuleFamily K)
    (parent : source.E) (child : (rules.R (target.color (embedding.edge parent))).E) :
    ∃ original : (source.subst rules).E,
      (embedding.subst rules).edge original = ⟨embedding.edge parent, child⟩ := by
  refine ⟨⟨parent, (rules.edgeColourEquiv (embedding.colour parent)).symm child⟩, ?_⟩
  change Sigma.mk (β := fun ambient : target.E => (rules.R (target.color ambient)).E)
      (embedding.edge parent)
      (rules.edgeColourEquiv (embedding.colour parent)
        ((rules.edgeColourEquiv (embedding.colour parent)).symm child)) = _
  rw [Equiv.apply_symm_apply]

theorem subst_incidentClosedAt_old (rules : EIGS.RuleFamily K) (vertex : source.V)
    (closed : embedding.IncidentClosedAt vertex) :
    (embedding.subst rules).IncidentClosedAt (Sum.inl vertex) := by
  rintro ⟨parent, child⟩ incident
  have parent_incident : target.tail parent = embedding.vertex vertex ∨
      target.head parent = embedding.vertex vertex := by
    rcases incident with incident | incident
    · change target.substEmbed rules parent ((rules.R (target.color parent)).tail child) =
          Sum.inl (embedding.vertex vertex) at incident
      rcases (substEmbed_eq_old_iff target rules parent _ _).mp incident with first | second
      · exact Or.inl first.2
      · exact Or.inr second.2
    · change target.substEmbed rules parent ((rules.R (target.color parent)).head child) =
          Sum.inl (embedding.vertex vertex) at incident
      rcases (substEmbed_eq_old_iff target rules parent _ _).mp incident with first | second
      · exact Or.inl first.2
      · exact Or.inr second.2
  obtain ⟨original, same⟩ := closed parent parent_incident
  subst parent
  exact embedding.substEdge_surjective_over_image rules original child

theorem subst_incidentClosedAt_private (rules : EIGS.RuleFamily K) (parent : source.E)
    (vertex : source.SubstInner rules parent) :
    (embedding.subst rules).IncidentClosedAt (Sum.inr ⟨parent, vertex⟩) := by
  rintro ⟨ambient_parent, child⟩ incident
  have same : embedding.edge parent = ambient_parent := by
    rcases incident with incident | incident
    · change target.substEmbed rules ambient_parent
          ((rules.R (target.color ambient_parent)).tail child) =
          Sum.inr ⟨embedding.edge parent,
            rules.innerColourEquiv (embedding.colour parent) vertex⟩ at incident
      apply target.substEmbed_copy_of_inner rules (embedding.edge parent) ambient_parent
        (rules.innerColourEquiv (embedding.colour parent) vertex)
        ((rules.R (target.color ambient_parent)).tail child)
      simpa only [Network.substEmbed,
        (rules.innerColourEquiv (embedding.colour parent) vertex).property.1,
        (rules.innerColourEquiv (embedding.colour parent) vertex).property.2, ↓reduceDIte]
        using incident.symm
    · change target.substEmbed rules ambient_parent
          ((rules.R (target.color ambient_parent)).head child) =
          Sum.inr ⟨embedding.edge parent,
            rules.innerColourEquiv (embedding.colour parent) vertex⟩ at incident
      apply target.substEmbed_copy_of_inner rules (embedding.edge parent) ambient_parent
        (rules.innerColourEquiv (embedding.colour parent) vertex)
        ((rules.R (target.color ambient_parent)).head child)
      simpa only [Network.substEmbed,
        (rules.innerColourEquiv (embedding.colour parent) vertex).property.1,
        (rules.innerColourEquiv (embedding.colour parent) vertex).property.2, ↓reduceDIte]
        using incident.symm
  subst ambient_parent
  exact embedding.substEdge_surjective_over_image rules parent child

end ColourEmbedding

theorem firstCopyEmbedding_incidentClosedAt (network : EIGS.Network K)
    (rules : EIGS.RuleFamily K) (loopless : network.Loopless) (edge : network.E)
    (vertex : (rules.R (network.color edge)).V)
    (not_plus : vertex ≠ rules.βplus (network.color edge))
    (not_minus : vertex ≠ rules.βminus (network.color edge)) :
    (network.firstCopyEmbedding rules loopless edge).IncidentClosedAt vertex := by
  rintro ⟨parent, child⟩ incident
  have same : edge = parent := by
    rcases incident with incident | incident
    · exact network.substEmbed_copy_of_inner rules edge parent ⟨vertex, not_plus, not_minus⟩
        ((rules.R (network.color parent)).tail child) incident.symm
    · exact network.substEmbed_copy_of_inner rules edge parent ⟨vertex, not_plus, not_minus⟩
        ((rules.R (network.color parent)).head child) incident.symm
  subst parent
  exact ⟨child, rfl⟩

/-- Localization at all depths includes old nonterminal vertices as well as
new private vertices. Only the two iterated planting vertices are excluded. -/
theorem iteratedCellEmbedding_incidentClosedAt (network : EIGS.Network K)
    (rules : EIGS.RuleFamily K) (loopless : network.Loopless) (edge : network.E)
    (level : ℕ) (vertex : ((rules.R (network.color edge)).substIter rules level).V)
    (not_plus : vertex ≠
      (rules.R (network.color edge)).inlIter rules (rules.βplus (network.color edge)) level)
    (not_minus : vertex ≠
      (rules.R (network.color edge)).inlIter rules (rules.βminus (network.color edge)) level) :
    (network.iteratedCellEmbedding rules loopless edge level).IncidentClosedAt vertex := by
  induction level with
  | zero =>
      exact network.firstCopyEmbedding_incidentClosedAt rules loopless edge vertex not_plus not_minus
  | succ level induction_hypothesis =>
      rcases vertex with vertex | ⟨parent, vertex⟩
      · apply (network.iteratedCellEmbedding rules loopless edge level).subst_incidentClosedAt_old
          rules vertex
        apply induction_hypothesis vertex
        · intro same
          exact not_plus (congrArg Sum.inl same)
        · intro same
          exact not_minus (congrArg Sum.inl same)
      · exact (network.iteratedCellEmbedding rules loopless edge level).subst_incidentClosedAt_private
          rules parent vertex

end
end EIGS.Network

#print axioms EIGS.Network.substEmbed_eq_old_iff
#print axioms EIGS.Network.ColourEmbedding.sum_edges_of_incidentClosedAt
#print axioms EIGS.Network.ColourEmbedding.neighbor_iff_of_incidentClosedAt
#print axioms EIGS.Network.ColourEmbedding.transProb_of_incidentClosedAt
#print axioms EIGS.Network.ColourEmbedding.transProb_zero_outside_of_incidentClosedAt
#print axioms EIGS.Network.ColourEmbedding.subst_incidentClosedAt_old
#print axioms EIGS.Network.ColourEmbedding.subst_incidentClosedAt_private
#print axioms EIGS.Network.firstCopyEmbedding_incidentClosedAt
#print axioms EIGS.Network.iteratedCellEmbedding_incidentClosedAt
