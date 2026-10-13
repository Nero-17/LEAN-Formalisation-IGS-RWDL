import RequestProject.Section31.NetworkIteratedCellEmbedding

namespace EIGS.Network
open scoped Classical
noncomputable section
variable {K : ℕ}

namespace ColourEmbedding
variable {source target : Network K} (embedding : ColourEmbedding source target)
    (rules : RuleFamily K)

theorem subst_vertex_surjective (vertices : Function.Surjective embedding.vertex)
    (edges : Function.Surjective embedding.edge) :
    Function.Surjective (embedding.subst rules).vertex := by
  intro vertex
  rcases vertex with old | ⟨parent, interior⟩
  · obtain ⟨original, rfl⟩ := vertices old
    exact ⟨Sum.inl original, rfl⟩
  · obtain ⟨original, rfl⟩ := edges parent
    refine ⟨Sum.inr ⟨original, (rules.innerColourEquiv (embedding.colour original)).symm interior⟩, ?_⟩
    change (Sum.inr ⟨embedding.edge original,
      rules.innerColourEquiv (embedding.colour original)
        ((rules.innerColourEquiv (embedding.colour original)).symm interior)⟩ :
      (target.subst rules).V) = Sum.inr ⟨embedding.edge original, interior⟩
    rw [Equiv.apply_symm_apply]

theorem subst_edge_surjective (edges : Function.Surjective embedding.edge) :
    Function.Surjective (embedding.subst rules).edge := by
  rintro ⟨parent, child⟩
  obtain ⟨original, rfl⟩ := edges parent
  refine ⟨⟨original, (rules.edgeColourEquiv (embedding.colour original)).symm child⟩, ?_⟩
  change (⟨embedding.edge original, rules.edgeColourEquiv (embedding.colour original)
    ((rules.edgeColourEquiv (embedding.colour original)).symm child)⟩ : (target.subst rules).E) = _
  rw [Equiv.apply_symm_apply]

theorem substIter_surjective (vertices : Function.Surjective embedding.vertex)
    (edges : Function.Surjective embedding.edge) (level : ℕ) :
    Function.Surjective (embedding.substIter rules level).vertex ∧
      Function.Surjective (embedding.substIter rules level).edge := by
  induction level with
  | zero => exact ⟨vertices, edges⟩
  | succ level induction =>
      exact ⟨(embedding.substIter rules level).subst_vertex_surjective rules induction.1 induction.2,
        (embedding.substIter rules level).subst_edge_surjective rules induction.2⟩

end ColourEmbedding

/-- Substituting the unique edge produces precisely its rule carrier;
the two old vertices are exactly the two planting vertices. -/
theorem firstCopy_singleEdge_vertex_surjective (rules : RuleFamily K) (colour : Fin K)
    (loopless : (singleEdge colour).Loopless) :
    Function.Surjective ((singleEdge colour).firstCopyEmbedding rules loopless ()).vertex := by
  intro vertex
  rcases vertex with old | ⟨parent, interior⟩
  · cases old with
    | false =>
        refine ⟨rules.βplus colour, ?_⟩
        change (singleEdge colour).substEmbed rules () (rules.βplus colour) = Sum.inl false
        simp [Network.substEmbed, singleEdge]
    | true =>
        refine ⟨rules.βminus colour, ?_⟩
        change (singleEdge colour).substEmbed rules () (rules.βminus colour) = Sum.inl true
        simp [Network.substEmbed, singleEdge, (rules.plant_ne colour).symm]
  · cases parent
    refine ⟨interior.val, ?_⟩
    change (singleEdge colour).substEmbed rules () interior.val = Sum.inr ⟨(), interior⟩
    simp [Network.substEmbed, interior.property.1, interior.property.2]

theorem firstCopy_singleEdge_edge_surjective (rules : RuleFamily K) (colour : Fin K)
    (loopless : (singleEdge colour).Loopless) :
    Function.Surjective ((singleEdge colour).firstCopyEmbedding rules loopless ()).edge := by
  rintro ⟨parent, child⟩
  cases parent
  exact ⟨child, rfl⟩

theorem iteratedCell_singleEdge_surjective (rules : RuleFamily K) (colour : Fin K)
    (loopless : (singleEdge colour).Loopless) (level : ℕ) :
    Function.Surjective ((singleEdge colour).iteratedCellEmbedding rules loopless () level).vertex ∧
      Function.Surjective ((singleEdge colour).iteratedCellEmbedding rules loopless () level).edge :=
  ((singleEdge colour).firstCopyEmbedding rules loopless ()).substIter_surjective rules
    (firstCopy_singleEdge_vertex_surjective rules colour loopless)
    (firstCopy_singleEdge_edge_surjective rules colour loopless) level

end
end EIGS.Network

#print axioms EIGS.Network.ColourEmbedding.subst_vertex_surjective
#print axioms EIGS.Network.ColourEmbedding.subst_edge_surjective
#print axioms EIGS.Network.ColourEmbedding.substIter_surjective
#print axioms EIGS.Network.firstCopy_singleEdge_vertex_surjective
#print axioms EIGS.Network.firstCopy_singleEdge_edge_surjective
#print axioms EIGS.Network.iteratedCell_singleEdge_surjective
