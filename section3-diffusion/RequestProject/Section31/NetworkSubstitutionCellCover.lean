import RequestProject.Section31.NetworkCellExitTransport

/-!
Every actual fine edge belongs to an original-edge cell. Every actual fine
vertex is either on the original skeleton or in one of these cells. The
two cell terminals lie on that skeleton, so killing on the full skeleton
can only occur earlier than killing on the two cell terminals.
-/

namespace EIGS.Network

open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

namespace ColourEmbedding

theorem substVertex_private_surjective_over_image {source target : EIGS.Network K}
    (embedding : ColourEmbedding source target) (rules : EIGS.RuleFamily K)
    (parent : source.E) (vertex : target.SubstInner rules (embedding.edge parent)) :
    ∃ original : (source.subst rules).V,
      (embedding.subst rules).vertex original = Sum.inr ⟨embedding.edge parent, vertex⟩ := by
  refine ⟨Sum.inr ⟨parent, (rules.innerColourEquiv (embedding.colour parent)).symm vertex⟩, ?_⟩
  change Sum.inr (Sigma.mk (β := fun ambient : target.E => target.SubstInner rules ambient)
      (embedding.edge parent) (rules.innerColourEquiv (embedding.colour parent)
        ((rules.innerColourEquiv (embedding.colour parent)).symm vertex))) = _
  rw [Equiv.apply_symm_apply]

end ColourEmbedding

/-- The original vertices tracked through the first substitution and every
subsequent substitution. -/
def iteratedSubstitutionSkeleton (network : EIGS.Network K) (rules : EIGS.RuleFamily K)
    (level : ℕ) : Finset ((network.subst rules).substIter rules level).V :=
  Finset.univ.image (fun vertex : network.V =>
    (network.subst rules).inlIter rules (Sum.inl vertex) level)

theorem iteratedCellEmbedding_edge_cover (network : EIGS.Network K) (rules : EIGS.RuleFamily K)
    (loopless : network.Loopless) (level : ℕ)
    (ambient : ((network.subst rules).substIter rules level).E) :
    ∃ parent : network.E, ∃ original : ((rules.R (network.color parent)).substIter rules level).E,
      (network.iteratedCellEmbedding rules loopless parent level).edge original = ambient := by
  induction level with
  | zero =>
      rcases ambient with ⟨parent, child⟩
      exact ⟨parent, child, rfl⟩
  | succ level induction_hypothesis =>
      rcases ambient with ⟨ambient_parent, child⟩
      obtain ⟨parent, original, same⟩ := induction_hypothesis ambient_parent
      subst ambient_parent
      obtain ⟨replacement, same⟩ :=
        (network.iteratedCellEmbedding rules loopless parent level).substEdge_surjective_over_image
          rules original child
      exact ⟨parent, replacement, same⟩

theorem iteratedCellEmbedding_vertex_cover (network : EIGS.Network K) (rules : EIGS.RuleFamily K)
    (loopless : network.Loopless) (level : ℕ)
    (ambient : ((network.subst rules).substIter rules level).V) :
    (∃ original : network.V,
      (network.subst rules).inlIter rules (Sum.inl original) level = ambient) ∨
    (∃ parent : network.E, ∃ original : ((rules.R (network.color parent)).substIter rules level).V,
      (network.iteratedCellEmbedding rules loopless parent level).vertex original = ambient) := by
  induction level with
  | zero =>
      rcases ambient with original | ⟨parent, interior⟩
      · exact Or.inl ⟨original, rfl⟩
      · refine Or.inr ⟨parent, interior.val, ?_⟩
        change network.substEmbed rules parent interior.val = Sum.inr ⟨parent, interior⟩
        simp only [Network.substEmbed, interior.property.1, interior.property.2, ↓reduceDIte]
        rfl
  | succ level induction_hypothesis =>
      rcases ambient with ambient | ⟨ambient_parent, interior⟩
      · rcases induction_hypothesis ambient with ⟨original, same⟩ | ⟨parent, original, same⟩
        · exact Or.inl ⟨original, congrArg Sum.inl same⟩
        · exact Or.inr ⟨parent, Sum.inl original, congrArg Sum.inl same⟩
      · obtain ⟨parent, original, same⟩ :=
          network.iteratedCellEmbedding_edge_cover rules loopless level ambient_parent
        subst ambient_parent
        obtain ⟨replacement, same⟩ :=
          (network.iteratedCellEmbedding rules loopless parent level).substVertex_private_surjective_over_image
            rules original interior
        exact Or.inr ⟨parent, replacement, same⟩

/-- A fine vertex outside the actual original skeleton lies in an actual
original-edge cell, with an explicit local preimage. -/
theorem iteratedCellEmbedding_cover_outside_skeleton (network : EIGS.Network K)
    (rules : EIGS.RuleFamily K) (loopless : network.Loopless) (level : ℕ)
    (ambient : ((network.subst rules).substIter rules level).V)
    (outside : ambient ∉ network.iteratedSubstitutionSkeleton rules level) :
    ∃ parent : network.E, ∃ original : ((rules.R (network.color parent)).substIter rules level).V,
      (network.iteratedCellEmbedding rules loopless parent level).vertex original = ambient := by
  rcases network.iteratedCellEmbedding_vertex_cover rules loopless level ambient with
      ⟨original, same⟩ | cell
  · exact (outside (Finset.mem_image.mpr ⟨original, Finset.mem_univ _, same⟩)).elim
  · exact cell

/-- Both actual cell terminals belong to the original skeleton. -/
theorem iteratedCellEmbedding_boundary_subset_skeleton (network : EIGS.Network K)
    (rules : EIGS.RuleFamily K) (loopless : network.Loopless) (parent : network.E) (level : ℕ) :
    (network.iteratedCellBoundary rules parent level).image
        (network.iteratedCellEmbedding rules loopless parent level).vertex ⊆
      network.iteratedSubstitutionSkeleton rules level := by
  intro ambient membership
  obtain ⟨original, cellMembership, rfl⟩ := Finset.mem_image.mp membership
  simp only [iteratedCellBoundary, Finset.mem_insert, Finset.mem_singleton] at cellMembership
  rcases cellMembership with rfl | rfl
  · rw [network.iteratedCellEmbedding_plus rules loopless parent level]
    exact Finset.mem_image.mpr ⟨network.tail parent, Finset.mem_univ _, rfl⟩
  · rw [network.iteratedCellEmbedding_minus rules loopless parent level]
    exact Finset.mem_image.mpr ⟨network.head parent, Finset.mem_univ _, rfl⟩

end
end EIGS.Network

#print axioms EIGS.Network.ColourEmbedding.substVertex_private_surjective_over_image
#print axioms EIGS.Network.iteratedCellEmbedding_edge_cover
#print axioms EIGS.Network.iteratedCellEmbedding_vertex_cover
#print axioms EIGS.Network.iteratedCellEmbedding_cover_outside_skeleton
#print axioms EIGS.Network.iteratedCellEmbedding_boundary_subset_skeleton
