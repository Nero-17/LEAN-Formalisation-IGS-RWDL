import RequestProject.Section31.NetworkSubstitutionCellCover
import RequestProject.Section31.EIGSIteratedRuleExitComparison
import RequestProject.Section31.EIGSReplantedExitMaximum

/-! Actual first-skeleton reach bounds. A fine vertex belongs to an actual
child cell; killing on the whole skeleton precedes killing at that cell's
two endpoints. The child exit is compared with a strictly lower Xi level. -/

namespace IGS.Sec31
open scoped BigOperators Classical
variable {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]

theorem notHit_antitone_boundary (chain : FinChain Vertex) (smaller larger : Finset Vertex)
    (subset : smaller ⊆ larger) (time : ℕ) (vertex : Vertex) :
    notHit chain larger time vertex ≤ notHit chain smaller time vertex := by
  induction time generalizing vertex with
  | zero =>
      by_cases inside : vertex ∈ larger
      · rw [notHit_of_mem chain larger inside]
        exact notHit_nonneg chain smaller 0 vertex
      · have outside : vertex ∉ smaller := fun member => inside (subset member)
        simp [notHit, inside, outside]
  | succ time induction_hypothesis =>
      by_cases inside : vertex ∈ larger
      · rw [notHit_of_mem chain larger inside]
        exact notHit_nonneg chain smaller (time + 1) vertex
      · have outside : vertex ∉ smaller := fun member => inside (subset member)
        simp only [notHit, inside, outside, if_false]
        exact Finset.sum_le_sum fun other _ =>
          mul_le_mul_of_nonneg_left (induction_hypothesis other) (chain.P_nonneg vertex other)

theorem partialHit_antitone_boundary (chain : FinChain Vertex) (smaller larger : Finset Vertex)
    (subset : smaller ⊆ larger) (time : ℕ) (vertex : Vertex) :
    partialHit chain larger time vertex ≤ partialHit chain smaller time vertex := by
  unfold partialHit
  exact Finset.sum_le_sum fun index _ =>
    notHit_antitone_boundary chain smaller larger subset index vertex

theorem partialHit_zero_on_boundary (chain : FinChain Vertex) (boundary : Finset Vertex)
    {vertex : Vertex} (inside : vertex ∈ boundary) (time : ℕ) :
    partialHit chain boundary time vertex = 0 := by
  unfold partialHit
  exact Finset.sum_eq_zero fun index _ => notHit_of_mem chain boundary inside index

end IGS.Sec31

namespace EIGS.Network
open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

theorem graphWalk_partialHit_cast {source target : EIGS.Network K} (equal : source = target)
    (source_degree : ∀ vertex, 0 < source.toSimpleGraph.degree vertex)
    (target_degree : ∀ vertex, 0 < target.toSimpleGraph.degree vertex)
    (boundary : Finset source.V) (time : ℕ) (vertex : source.V) :
    IGS.Sec31.partialHit (EIGS.graphWalkChain target.toSimpleGraph target_degree)
        (boundary.image (castVertex equal)) time (castVertex equal vertex) =
      IGS.Sec31.partialHit (EIGS.graphWalkChain source.toSimpleGraph source_degree)
        boundary time vertex := by
  cases equal
  simp [castVertex]

theorem graphWalk_partialHit_le_expExit (network : EIGS.Network K)
    (connected : network.toSimpleGraph.Connected)
    (degree : ∀ vertex, 0 < network.toSimpleGraph.degree vertex)
    (boundary : Finset network.V) (nonempty : boundary.Nonempty) (time : ℕ) (vertex : network.V) :
    IGS.Sec31.partialHit (EIGS.graphWalkChain network.toSimpleGraph degree) boundary time vertex ≤
      EIGS.expExit network.toSimpleGraph boundaryᶜ vertex := by
  simp only [IGS.Sec31.partialHit, EIGS.graphWalkChain_notHit]
  exact (EIGS.expExit_summable connected (by simpa using nonempty) vertex).sum_le_tsum _
    (fun _ _ => EIGS.surv_nonneg _ _)

/-- The cell preimage has one fewer substitution than the ambient carrier.
The right side is the actual maximum at Xi level `1 + level`. -/
theorem skeleton_partialHit_le_replantedMaximum (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (network : EIGS.Network K) (loopless : network.Loopless) (level : ℕ)
    (degree : ∀ vertex,
      0 < ((network.subst (system.ruleFamily rulesConnected)).substIter
        (system.ruleFamily rulesConnected) level).toSimpleGraph.degree vertex)
    (time : ℕ) (vertex : ((network.subst (system.ruleFamily rulesConnected)).substIter
      (system.ruleFamily rulesConnected) level).V) :
    IGS.Sec31.partialHit
        (EIGS.graphWalkChain ((network.subst (system.ruleFamily rulesConnected)).substIter
          (system.ruleFamily rulesConnected) level).toSimpleGraph degree)
        (network.iteratedSubstitutionSkeleton (system.ruleFamily rulesConnected) level) time vertex ≤
      xiReplantedTerminalExitMaximum system (1 + level) := by
  by_cases inside : vertex ∈ network.iteratedSubstitutionSkeleton (system.ruleFamily rulesConnected) level
  · rw [IGS.Sec31.partialHit_zero_on_boundary _ _ inside]
    exact xiReplantedTerminalExitMaximum_nonnegative system (1 + level)
  · obtain ⟨parent, original, same⟩ := network.iteratedCellEmbedding_cover_outside_skeleton
      (system.ruleFamily rulesConnected) loopless level vertex inside
    subst vertex
    calc
      _ ≤ IGS.Sec31.partialHit
          (EIGS.graphWalkChain ((network.subst (system.ruleFamily rulesConnected)).substIter
            (system.ruleFamily rulesConnected) level).toSimpleGraph degree)
          ((network.iteratedCellBoundary (system.ruleFamily rulesConnected) parent level).image
            (network.iteratedCellEmbedding (system.ruleFamily rulesConnected) loopless parent level).vertex)
          time ((network.iteratedCellEmbedding (system.ruleFamily rulesConnected) loopless parent level).vertex
            original) :=
        IGS.Sec31.partialHit_antitone_boundary _ _ _
          (network.iteratedCellEmbedding_boundary_subset_skeleton
            (system.ruleFamily rulesConnected) loopless parent level) time _
      _ = IGS.Sec31.partialHit
          (EIGS.graphWalkChain (((system.ruleFamily rulesConnected).R (network.color parent)).substIter
            (system.ruleFamily rulesConnected) level).toSimpleGraph
            (ruleFamily_iterated_degree_positive system rulesConnected (network.color parent) level))
          (network.iteratedCellBoundary (system.ruleFamily rulesConnected) parent level) time original :=
        network.iteratedCellEmbedding_partialHit (system.ruleFamily rulesConnected) loopless parent level
          (ruleFamily_iterated_degree_positive system rulesConnected (network.color parent) level)
          degree time original
      _ ≤ EIGS.expExit (((system.ruleFamily rulesConnected).R (network.color parent)).substIter
            (system.ruleFamily rulesConnected) level).toSimpleGraph
          (network.iteratedCellBoundary (system.ruleFamily rulesConnected) parent level)ᶜ original :=
        graphWalk_partialHit_le_expExit _
          (ruleFamily_iterated_connected system rulesConnected (network.color parent) level)
          (ruleFamily_iterated_degree_positive system rulesConnected (network.color parent) level)
          _ (network.iteratedCellBoundary_nonempty (system.ruleFamily rulesConnected) parent level) time original
      _ = EIGS.expExit (XiSimpleGraph {system with initCol := network.color parent} (1 + level))
          {xiPositiveTerminal {system with initCol := network.color parent} (1 + level),
            xiNegativeTerminal {system with initCol := network.color parent} (1 + level)}ᶜ
          (replantedRuleVertex system rulesConnected (network.color parent) level original) :=
        (ruleFamily_iterated_expExit_eq_replanted system rulesConnected (network.color parent) level original).symm
      _ ≤ xiReplantedTerminalExitMaximum system (1 + level) :=
        xiReplantedTerminalExit_le_maximum system (1 + level) (network.color parent) _

end
end EIGS.Network

namespace EIGS
open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

theorem xiNetwork_succ_substIter (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (coarse level : ℕ) :
    XiNetwork system (coarse + (level + 1)) =
      ((XiNetwork system coarse).subst (system.ruleFamily rulesConnected)).substIter
        (system.ruleFamily rulesConnected) level := by
  induction level with
  | zero => exact xiNetwork_succ system rulesConnected coarse
  | succ level induction_hypothesis =>
      rw [Nat.add_succ, xiNetwork_succ system rulesConnected, Network.substIter_succ, induction_hypothesis]

theorem xiNetwork_succ_substIter_forward (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (coarse level : ℕ)
    (vertex : XiVtx system coarse) :
    Network.castVertex (xiNetwork_succ_substIter system rulesConnected coarse level).symm
        (((XiNetwork system coarse).subst (system.ruleFamily rulesConnected)).inlIter
          (system.ruleFamily rulesConnected) (Sum.inl vertex) level) =
      xiForward system coarse (level + 1) vertex := by
  induction level with
  | zero => rfl
  | succ level induction_hypothesis =>
      change Network.castVertex
        (congrArg (fun network : Network K => network.subst (system.ruleFamily rulesConnected))
          (xiNetwork_succ_substIter system rulesConnected coarse level).symm)
        (Sum.inl (((XiNetwork system coarse).subst (system.ruleFamily rulesConnected)).inlIter
          (system.ruleFamily rulesConnected) (Sum.inl vertex) level)) =
        Sum.inl (xiForward system coarse (level + 1) vertex)
      rw [Network.castVertex_subst_old
        (xiNetwork_succ_substIter system rulesConnected coarse level).symm, induction_hypothesis]

theorem xiNetwork_succ_substIter_skeleton (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (coarse level : ℕ) :
    ((XiNetwork system coarse).iteratedSubstitutionSkeleton (system.ruleFamily rulesConnected) level).image
        (Network.castVertex (xiNetwork_succ_substIter system rulesConnected coarse level).symm) =
      Finset.univ.image (xiForward system coarse (level + 1)) := by
  rw [Network.iteratedSubstitutionSkeleton, Finset.image_image]
  apply Finset.image_congr
  intro vertex _
  exact xiNetwork_succ_substIter_forward system rulesConnected coarse level vertex

/-- At Xi level `1 + steps`, the mean truncated time to reach the level-one
skeleton is bounded by the full terminal exit maximum at Xi level `steps`.
All child-carrier localization and the lower-level comparison are internal. -/
theorem xiReplanted_first_skeleton_partialHit_le_exitMaximum (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (colour : Fin K) (steps time : ℕ)
    (vertex : XiVtx {system with initCol := colour} (1 + steps)) :
    IGS.Sec31.partialHit (xiGraphWalkChain {system with initCol := colour} rulesConnected (1 + steps))
        (Finset.univ.image (xiForward {system with initCol := colour} 1 steps)) time vertex ≤
      xiReplantedTerminalExitMaximum system steps := by
  cases steps with
  | zero =>
      have member : vertex ∈ Finset.univ.image (xiForward {system with initCol := colour} 1 0) :=
        Finset.mem_image.mpr ⟨vertex, Finset.mem_univ _, rfl⟩
      rw [IGS.Sec31.partialHit_zero_on_boundary _ _ member]
      exact xiReplantedTerminalExitMaximum_nonnegative system 0
  | succ level =>
      have degree : ∀ vertex,
          0 < (XiNetwork {system with initCol := colour} (1 + (level + 1))).toSimpleGraph.degree vertex := by
        intro vertex
        exact_mod_cast xiSimpleGraph_degree_positive {system with initCol := colour}
          rulesConnected (1 + (level + 1)) vertex
      have ambient_degree : ∀ vertex,
          0 < (((XiNetwork {system with initCol := colour} 1).subst (system.ruleFamily rulesConnected)).substIter
            (system.ruleFamily rulesConnected) level).toSimpleGraph.degree vertex := by
        have positive := degree
        rw [xiNetwork_succ_substIter {system with initCol := colour} rulesConnected 1 level] at positive
        exact positive
      have comparison := Network.graphWalk_partialHit_cast
        (xiNetwork_succ_substIter {system with initCol := colour} rulesConnected 1 level).symm
        ambient_degree degree
        ((XiNetwork {system with initCol := colour} 1).iteratedSubstitutionSkeleton
          (system.ruleFamily rulesConnected) level) time
        ((Network.castVertex
          (xiNetwork_succ_substIter {system with initCol := colour} rulesConnected 1 level).symm).symm vertex)
      have skeleton := xiNetwork_succ_substIter_skeleton
        {system with initCol := colour} rulesConnected 1 level
      change ((XiNetwork {system with initCol := colour} 1).iteratedSubstitutionSkeleton
          (system.ruleFamily rulesConnected) level).image
          (Network.castVertex
            (xiNetwork_succ_substIter {system with initCol := colour} rulesConnected 1 level).symm) =
        Finset.univ.image (xiForward {system with initCol := colour} 1 (level + 1)) at skeleton
      rw [Equiv.apply_symm_apply, skeleton] at comparison
      simpa only [Nat.add_comm 1 level] using
        (comparison.le.trans (Network.skeleton_partialHit_le_replantedMaximum system rulesConnected
          (XiNetwork {system with initCol := colour} 1)
          (xiNetwork_loopless {system with initCol := colour} rulesConnected rulesLoopless 1) level
          ambient_degree time _))

end
end EIGS

#print axioms IGS.Sec31.partialHit_antitone_boundary
#print axioms EIGS.Network.graphWalk_partialHit_cast
#print axioms EIGS.Network.skeleton_partialHit_le_replantedMaximum
#print axioms EIGS.xiNetwork_succ_substIter
#print axioms EIGS.xiNetwork_succ_substIter_forward
#print axioms EIGS.xiNetwork_succ_substIter_skeleton
#print axioms EIGS.xiReplanted_first_skeleton_partialHit_le_exitMaximum
