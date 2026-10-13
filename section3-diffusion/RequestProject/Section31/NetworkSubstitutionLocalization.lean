import RequestProject.Section2Simplicity
import RequestProject.Section2RandomWalk

/-! Exact localization of a simple random walk at an interior vertex of a
substitution copy. Both the neighbour set and its degree are transported;
no transition-kernel localization is assumed. -/

namespace EIGS.Network

open scoped Classical
noncomputable section
variable {K : ℕ} (network : EIGS.Network K) (rules : EIGS.RuleFamily K)

theorem substEmbed_adj_of_adj (loopless : network.Loopless) (edge : network.E)
    {first second : (rules.R (network.color edge)).V}
    (adjacency : (rules.R (network.color edge)).toSimpleGraph.Adj first second) :
    (network.subst rules).toSimpleGraph.Adj
      (network.substEmbed rules edge first) (network.substEmbed rules edge second) := by
  refine ⟨(network.substEmbed_injective rules loopless edge).ne adjacency.1, ?_⟩
  rcases adjacency.2 with ⟨child, tailEquality, headEquality⟩ |
      ⟨child, tailEquality, headEquality⟩
  · exact Or.inl ⟨⟨edge, child⟩, congrArg (network.substEmbed rules edge) tailEquality,
      congrArg (network.substEmbed rules edge) headEquality⟩
  · exact Or.inr ⟨⟨edge, child⟩, congrArg (network.substEmbed rules edge) tailEquality,
      congrArg (network.substEmbed rules edge) headEquality⟩

theorem subst_interior_neighbor_iff (loopless : network.Loopless) (edge : network.E)
    (interior : network.SubstInner rules edge) (neighbor : (network.subst rules).V) :
    (network.subst rules).toSimpleGraph.Adj (network.substEmbed rules edge interior.val) neighbor ↔
      ∃ other : (rules.R (network.color edge)).V,
        (rules.R (network.color edge)).toSimpleGraph.Adj interior.val other ∧
          network.substEmbed rules edge other = neighbor := by
  constructor
  · intro adjacency
    rcases adjacency.2 with ⟨⟨parent, child⟩, tailEquality, headEquality⟩ |
        ⟨⟨parent, child⟩, tailEquality, headEquality⟩
    · have same : edge = parent := network.substEmbed_copy_of_inner rules edge parent interior
        ((rules.R (network.color parent)).tail child) tailEquality.symm
      subst parent
      refine ⟨(rules.R (network.color edge)).head child, ⟨?_, ?_⟩, headEquality⟩
      · intro equal
        exact adjacency.1 ((congrArg (network.substEmbed rules edge) equal).trans headEquality)
      · exact Or.inl ⟨child, network.substEmbed_injective rules loopless edge tailEquality, rfl⟩
    · have same : edge = parent := network.substEmbed_copy_of_inner rules edge parent interior
        ((rules.R (network.color parent)).head child) headEquality.symm
      subst parent
      refine ⟨(rules.R (network.color edge)).tail child, ⟨?_, ?_⟩, tailEquality⟩
      · intro equal
        exact adjacency.1 ((congrArg (network.substEmbed rules edge) equal).trans tailEquality)
      · exact Or.inr ⟨child, rfl, network.substEmbed_injective rules loopless edge headEquality⟩
  · rintro ⟨other, adjacency, rfl⟩
    exact network.substEmbed_adj_of_adj rules loopless edge adjacency

theorem subst_interior_adj_iff (loopless : network.Loopless) (edge : network.E)
    (interior : network.SubstInner rules edge) (other : (rules.R (network.color edge)).V) :
    (network.subst rules).toSimpleGraph.Adj (network.substEmbed rules edge interior.val)
      (network.substEmbed rules edge other) ↔
      (rules.R (network.color edge)).toSimpleGraph.Adj interior.val other := by
  rw [network.subst_interior_neighbor_iff rules loopless edge interior]
  constructor
  · rintro ⟨candidate, adjacency, equal⟩
    have same := network.substEmbed_injective rules loopless edge equal
    simpa only [same] using adjacency
  · intro adjacency
    exact ⟨other, adjacency, rfl⟩

noncomputable def substInteriorNeighborEquiv (loopless : network.Loopless) (edge : network.E)
    (interior : network.SubstInner rules edge) :
    (rules.R (network.color edge)).toSimpleGraph.neighborSet interior.val ≃
      (network.subst rules).toSimpleGraph.neighborSet (network.substEmbed rules edge interior.val) :=
  Equiv.ofBijective
    (fun other => ⟨network.substEmbed rules edge other.val,
      network.substEmbed_adj_of_adj rules loopless edge other.property⟩) (by
      constructor
      · intro first second same
        exact Subtype.ext (network.substEmbed_injective rules loopless edge (congrArg Subtype.val same))
      · intro neighbor
        obtain ⟨other, adjacency, equal⟩ :=
          (network.subst_interior_neighbor_iff rules loopless edge interior neighbor.val).mp neighbor.property
        exact ⟨⟨other, adjacency⟩, Subtype.ext equal⟩)

theorem subst_interior_degree (loopless : network.Loopless) (edge : network.E)
    (interior : network.SubstInner rules edge) :
    (network.subst rules).toSimpleGraph.degree (network.substEmbed rules edge interior.val) =
      (rules.R (network.color edge)).toSimpleGraph.degree interior.val := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  exact (Fintype.card_congr (network.substInteriorNeighborEquiv rules loopless edge interior)).symm

theorem subst_interior_transProb (loopless : network.Loopless) (edge : network.E)
    (interior : network.SubstInner rules edge) (other : (rules.R (network.color edge)).V) :
    EIGS.transProb (network.subst rules).toSimpleGraph
      (network.substEmbed rules edge interior.val) (network.substEmbed rules edge other) =
      EIGS.transProb (rules.R (network.color edge)).toSimpleGraph interior.val other := by
  simp only [EIGS.transProb, network.subst_interior_adj_iff rules loopless edge interior,
    network.subst_interior_degree rules loopless edge interior]

end
end EIGS.Network

#print axioms EIGS.Network.substEmbed_adj_of_adj
#print axioms EIGS.Network.subst_interior_neighbor_iff
#print axioms EIGS.Network.subst_interior_adj_iff
#print axioms EIGS.Network.subst_interior_degree
#print axioms EIGS.Network.subst_interior_transProb
