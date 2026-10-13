import RequestProject.Section31.NetworkSubstitutionEmbedding
import RequestProject.Section31.KilledChainEmbeddingTransport
import RequestProject.Section31.EIGSCellStarExit

/-!
Killed simple-walk quantities on actual embedded network cells. All
nonterminal rows are localized from actual incident edges. The terminal
rows may differ, and no exit-time conclusion is supplied as a hypothesis.
-/

namespace EIGS.Network

open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

namespace ColourEmbedding

variable {source target : EIGS.Network K} (embedding : ColourEmbedding source target)

theorem mem_boundary_image (boundary : Finset source.V) (vertex : source.V) :
    embedding.vertex vertex ∈ boundary.image embedding.vertex ↔ vertex ∈ boundary := by
  constructor
  · intro membership
    obtain ⟨original, member, same⟩ := Finset.mem_image.mp membership
    exact embedding.vertex.injective same ▸ member
  · intro membership
    exact Finset.mem_image.mpr ⟨vertex, membership, rfl⟩

theorem graphWalk_notHit
    (source_degree : ∀ vertex, 0 < source.toSimpleGraph.degree vertex)
    (target_degree : ∀ vertex, 0 < target.toSimpleGraph.degree vertex)
    (boundary : Finset source.V)
    (closed : ∀ vertex, vertex ∉ boundary → embedding.IncidentClosedAt vertex)
    (time : ℕ) (vertex : source.V) :
    IGS.Sec31.notHit (EIGS.graphWalkChain target.toSimpleGraph target_degree)
        (boundary.image embedding.vertex) time (embedding.vertex vertex) =
      IGS.Sec31.notHit (EIGS.graphWalkChain source.toSimpleGraph source_degree)
        boundary time vertex := by
  apply IGS.Sec31.killedEmbedding_notHit
    (EIGS.graphWalkChain source.toSimpleGraph source_degree)
    (EIGS.graphWalkChain target.toSimpleGraph target_degree) embedding.vertex boundary
    (boundary.image embedding.vertex) (embedding.mem_boundary_image boundary)
  · intro original outside other
    exact embedding.transProb_of_incidentClosedAt original (closed original outside) other
  · intro original outside other outsideRange
    exact embedding.transProb_zero_outside_of_incidentClosedAt original
      (closed original outside) other outsideRange

theorem graphWalk_partialHit
    (source_degree : ∀ vertex, 0 < source.toSimpleGraph.degree vertex)
    (target_degree : ∀ vertex, 0 < target.toSimpleGraph.degree vertex)
    (boundary : Finset source.V)
    (closed : ∀ vertex, vertex ∉ boundary → embedding.IncidentClosedAt vertex)
    (time : ℕ) (vertex : source.V) :
    IGS.Sec31.partialHit (EIGS.graphWalkChain target.toSimpleGraph target_degree)
        (boundary.image embedding.vertex) time (embedding.vertex vertex) =
      IGS.Sec31.partialHit (EIGS.graphWalkChain source.toSimpleGraph source_degree)
        boundary time vertex := by
  unfold IGS.Sec31.partialHit
  apply Finset.sum_congr rfl
  intro index _
  exact embedding.graphWalk_notHit source_degree target_degree boundary closed index vertex

theorem graphWalk_hitTime
    (source_degree : ∀ vertex, 0 < source.toSimpleGraph.degree vertex)
    (target_degree : ∀ vertex, 0 < target.toSimpleGraph.degree vertex)
    (boundary : Finset source.V)
    (closed : ∀ vertex, vertex ∉ boundary → embedding.IncidentClosedAt vertex)
    (vertex : source.V) :
    IGS.Sec31.hitTime (EIGS.graphWalkChain target.toSimpleGraph target_degree)
        (boundary.image embedding.vertex) (embedding.vertex vertex) =
      IGS.Sec31.hitTime (EIGS.graphWalkChain source.toSimpleGraph source_degree)
        boundary vertex := by
  unfold IGS.Sec31.hitTime
  congr 1
  funext time
  exact embedding.graphWalk_partialHit source_degree target_degree boundary closed time vertex

theorem graphWalk_expExit
    (source_connected : source.toSimpleGraph.Connected)
    (target_connected : target.toSimpleGraph.Connected)
    (source_degree : ∀ vertex, 0 < source.toSimpleGraph.degree vertex)
    (target_degree : ∀ vertex, 0 < target.toSimpleGraph.degree vertex)
    (boundary : Finset source.V) (boundary_nonempty : boundary.Nonempty)
    (closed : ∀ vertex, vertex ∉ boundary → embedding.IncidentClosedAt vertex)
    (vertex : source.V) :
    EIGS.expExit target.toSimpleGraph (boundary.image embedding.vertex)ᶜ (embedding.vertex vertex) =
      EIGS.expExit source.toSimpleGraph boundaryᶜ vertex := by
  have image_nonempty : (boundary.image embedding.vertex).Nonempty := by
    obtain ⟨original, membership⟩ := boundary_nonempty
    exact ⟨embedding.vertex original, Finset.mem_image.mpr ⟨original, membership, rfl⟩⟩
  rw [← EIGS.graphWalkChain_hitTime target.toSimpleGraph target_connected target_degree
      (boundary.image embedding.vertex) image_nonempty (embedding.vertex vertex),
    ← EIGS.graphWalkChain_hitTime source.toSimpleGraph source_connected source_degree
      boundary boundary_nonempty vertex]
  exact embedding.graphWalk_hitTime source_degree target_degree boundary closed vertex

end ColourEmbedding

/-- The actual two terminal vertices of an iterated rule copy. -/
def iteratedCellBoundary (network : EIGS.Network K) (rules : EIGS.RuleFamily K)
    (edge : network.E) (level : ℕ) :
    Finset ((rules.R (network.color edge)).substIter rules level).V :=
  {(rules.R (network.color edge)).inlIter rules (rules.βplus (network.color edge)) level,
    (rules.R (network.color edge)).inlIter rules (rules.βminus (network.color edge)) level}

theorem iteratedCellBoundary_nonempty (network : EIGS.Network K) (rules : EIGS.RuleFamily K)
    (edge : network.E) (level : ℕ) : (network.iteratedCellBoundary rules edge level).Nonempty := by
  exact ⟨_, Finset.mem_insert_self _ _⟩

theorem iteratedCellEmbedding_closed_outside_boundary (network : EIGS.Network K)
    (rules : EIGS.RuleFamily K) (loopless : network.Loopless) (edge : network.E) (level : ℕ)
    (vertex : ((rules.R (network.color edge)).substIter rules level).V)
    (outside : vertex ∉ network.iteratedCellBoundary rules edge level) :
    (network.iteratedCellEmbedding rules loopless edge level).IncidentClosedAt vertex := by
  simp only [iteratedCellBoundary, Finset.mem_insert, Finset.mem_singleton, not_or] at outside
  exact network.iteratedCellEmbedding_incidentClosedAt rules loopless edge level vertex
    outside.1 outside.2

theorem iteratedCellEmbedding_notHit (network : EIGS.Network K) (rules : EIGS.RuleFamily K)
    (loopless : network.Loopless) (edge : network.E) (level : ℕ)
    (source_degree : ∀ vertex,
      0 < ((rules.R (network.color edge)).substIter rules level).toSimpleGraph.degree vertex)
    (target_degree : ∀ vertex,
      0 < ((network.subst rules).substIter rules level).toSimpleGraph.degree vertex)
    (time : ℕ) (vertex : ((rules.R (network.color edge)).substIter rules level).V) :
    IGS.Sec31.notHit
        (EIGS.graphWalkChain ((network.subst rules).substIter rules level).toSimpleGraph target_degree)
        ((network.iteratedCellBoundary rules edge level).image
          (network.iteratedCellEmbedding rules loopless edge level).vertex)
        time ((network.iteratedCellEmbedding rules loopless edge level).vertex vertex) =
      IGS.Sec31.notHit
        (EIGS.graphWalkChain ((rules.R (network.color edge)).substIter rules level).toSimpleGraph source_degree)
        (network.iteratedCellBoundary rules edge level) time vertex :=
  (network.iteratedCellEmbedding rules loopless edge level).graphWalk_notHit source_degree target_degree
    (network.iteratedCellBoundary rules edge level)
    (network.iteratedCellEmbedding_closed_outside_boundary rules loopless edge level) time vertex

theorem iteratedCellEmbedding_partialHit (network : EIGS.Network K) (rules : EIGS.RuleFamily K)
    (loopless : network.Loopless) (edge : network.E) (level : ℕ)
    (source_degree : ∀ vertex,
      0 < ((rules.R (network.color edge)).substIter rules level).toSimpleGraph.degree vertex)
    (target_degree : ∀ vertex,
      0 < ((network.subst rules).substIter rules level).toSimpleGraph.degree vertex)
    (time : ℕ) (vertex : ((rules.R (network.color edge)).substIter rules level).V) :
    IGS.Sec31.partialHit
        (EIGS.graphWalkChain ((network.subst rules).substIter rules level).toSimpleGraph target_degree)
        ((network.iteratedCellBoundary rules edge level).image
          (network.iteratedCellEmbedding rules loopless edge level).vertex)
        time ((network.iteratedCellEmbedding rules loopless edge level).vertex vertex) =
      IGS.Sec31.partialHit
        (EIGS.graphWalkChain ((rules.R (network.color edge)).substIter rules level).toSimpleGraph source_degree)
        (network.iteratedCellBoundary rules edge level) time vertex :=
  (network.iteratedCellEmbedding rules loopless edge level).graphWalk_partialHit source_degree target_degree
    (network.iteratedCellBoundary rules edge level)
    (network.iteratedCellEmbedding_closed_outside_boundary rules loopless edge level) time vertex

theorem iteratedCellEmbedding_hitTime (network : EIGS.Network K) (rules : EIGS.RuleFamily K)
    (loopless : network.Loopless) (edge : network.E) (level : ℕ)
    (source_degree : ∀ vertex,
      0 < ((rules.R (network.color edge)).substIter rules level).toSimpleGraph.degree vertex)
    (target_degree : ∀ vertex,
      0 < ((network.subst rules).substIter rules level).toSimpleGraph.degree vertex)
    (vertex : ((rules.R (network.color edge)).substIter rules level).V) :
    IGS.Sec31.hitTime
        (EIGS.graphWalkChain ((network.subst rules).substIter rules level).toSimpleGraph target_degree)
        ((network.iteratedCellBoundary rules edge level).image
          (network.iteratedCellEmbedding rules loopless edge level).vertex)
        ((network.iteratedCellEmbedding rules loopless edge level).vertex vertex) =
      IGS.Sec31.hitTime
        (EIGS.graphWalkChain ((rules.R (network.color edge)).substIter rules level).toSimpleGraph source_degree)
        (network.iteratedCellBoundary rules edge level) vertex :=
  (network.iteratedCellEmbedding rules loopless edge level).graphWalk_hitTime source_degree target_degree
    (network.iteratedCellBoundary rules edge level)
    (network.iteratedCellEmbedding_closed_outside_boundary rules loopless edge level) vertex

theorem iteratedCellEmbedding_expExit (network : EIGS.Network K) (rules : EIGS.RuleFamily K)
    (loopless : network.Loopless) (edge : network.E) (level : ℕ)
    (source_connected : ((rules.R (network.color edge)).substIter rules level).toSimpleGraph.Connected)
    (target_connected : ((network.subst rules).substIter rules level).toSimpleGraph.Connected)
    (source_degree : ∀ vertex,
      0 < ((rules.R (network.color edge)).substIter rules level).toSimpleGraph.degree vertex)
    (target_degree : ∀ vertex,
      0 < ((network.subst rules).substIter rules level).toSimpleGraph.degree vertex)
    (vertex : ((rules.R (network.color edge)).substIter rules level).V) :
    EIGS.expExit ((network.subst rules).substIter rules level).toSimpleGraph
        ((network.iteratedCellBoundary rules edge level).image
          (network.iteratedCellEmbedding rules loopless edge level).vertex)ᶜ
        ((network.iteratedCellEmbedding rules loopless edge level).vertex vertex) =
      EIGS.expExit ((rules.R (network.color edge)).substIter rules level).toSimpleGraph
        (network.iteratedCellBoundary rules edge level)ᶜ vertex :=
  (network.iteratedCellEmbedding rules loopless edge level).graphWalk_expExit
    source_connected target_connected source_degree target_degree
    (network.iteratedCellBoundary rules edge level) (network.iteratedCellBoundary_nonempty rules edge level)
    (network.iteratedCellEmbedding_closed_outside_boundary rules loopless edge level) vertex

end
end EIGS.Network

#print axioms EIGS.Network.ColourEmbedding.mem_boundary_image
#print axioms EIGS.Network.ColourEmbedding.graphWalk_notHit
#print axioms EIGS.Network.ColourEmbedding.graphWalk_partialHit
#print axioms EIGS.Network.ColourEmbedding.graphWalk_hitTime
#print axioms EIGS.Network.ColourEmbedding.graphWalk_expExit
#print axioms EIGS.Network.iteratedCellEmbedding_closed_outside_boundary
#print axioms EIGS.Network.iteratedCellEmbedding_notHit
#print axioms EIGS.Network.iteratedCellEmbedding_partialHit
#print axioms EIGS.Network.iteratedCellEmbedding_hitTime
#print axioms EIGS.Network.iteratedCellEmbedding_expExit
