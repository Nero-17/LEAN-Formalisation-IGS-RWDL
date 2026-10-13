import RequestProject.Section31.EIGSIteratedRuleConnectivity
import RequestProject.Section31.NetworkCellExitTransport

/-! Exact comparison of the actual iterated rule carrier with the replanted
Xi network. The vertex map and both canonical terminal images are explicit.
No exit estimate or kernel identification is assumed. -/

namespace EIGS.Network

open scoped Classical
noncomputable section
variable {K : ℕ}

def castVertex {source target : EIGS.Network K} (equal : source = target) : source.V ≃ target.V :=
  Equiv.cast (congrArg (fun network : EIGS.Network K => network.V) equal)

theorem castVertex_subst_old {source target : EIGS.Network K} (equal : source = target)
    (rules : EIGS.RuleFamily K) (vertex : source.V) :
    castVertex (congrArg (fun network => network.subst rules) equal) (Sum.inl vertex) =
      Sum.inl (castVertex equal vertex) := by
  cases equal
  rfl

theorem expExit_cast {source target : EIGS.Network K} (equal : source = target)
    (boundary : Finset source.V) (vertex : source.V) :
    EIGS.expExit target.toSimpleGraph (boundary.image (castVertex equal))ᶜ (castVertex equal vertex) =
      EIGS.expExit source.toSimpleGraph boundaryᶜ vertex := by
  cases equal
  simp [castVertex]

theorem singleEdge_loopless (colour : Fin K) : (singleEdge colour).Loopless := by
  intro edge
  simp [singleEdge]

end
end EIGS.Network

namespace EIGS

open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

theorem xiNetwork_one_add_substIter_plus (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (level : ℕ) :
    Network.castVertex (xiNetwork_one_add_substIter system rulesConnected level).symm
        (((Network.singleEdge system.initCol).subst (system.ruleFamily rulesConnected)).inlIter
          (system.ruleFamily rulesConnected) (Sum.inl false) level) =
      xiPositiveTerminal system (1 + level) := by
  induction level with
  | zero => rfl
  | succ level induction_hypothesis =>
      change Network.castVertex
        (congrArg (fun network : Network K => network.subst (system.ruleFamily rulesConnected))
          (xiNetwork_one_add_substIter system rulesConnected level).symm)
        (Sum.inl (((Network.singleEdge system.initCol).subst (system.ruleFamily rulesConnected)).inlIter
          (system.ruleFamily rulesConnected) (Sum.inl false) level)) =
        Sum.inl (xiPositiveTerminal system (1 + level))
      rw [Network.castVertex_subst_old
        (xiNetwork_one_add_substIter system rulesConnected level).symm, induction_hypothesis]

theorem xiNetwork_one_add_substIter_minus (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (level : ℕ) :
    Network.castVertex (xiNetwork_one_add_substIter system rulesConnected level).symm
        (((Network.singleEdge system.initCol).subst (system.ruleFamily rulesConnected)).inlIter
          (system.ruleFamily rulesConnected) (Sum.inl true) level) =
      xiNegativeTerminal system (1 + level) := by
  induction level with
  | zero => rfl
  | succ level induction_hypothesis =>
      change Network.castVertex
        (congrArg (fun network : Network K => network.subst (system.ruleFamily rulesConnected))
          (xiNetwork_one_add_substIter system rulesConnected level).symm)
        (Sum.inl (((Network.singleEdge system.initCol).subst (system.ruleFamily rulesConnected)).inlIter
          (system.ruleFamily rulesConnected) (Sum.inl true) level)) =
        Sum.inl (xiNegativeTerminal system (1 + level))
      rw [Network.castVertex_subst_old
        (xiNetwork_one_add_substIter system rulesConnected level).symm, induction_hypothesis]

def replantedRuleVertex (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (colour : Fin K) (level : ℕ)
    (vertex : (((system.ruleFamily rulesConnected).R colour).substIter
      (system.ruleFamily rulesConnected) level).V) : XiVtx {system with initCol := colour} (1 + level) :=
  Network.castVertex
    (xiNetwork_one_add_substIter {system with initCol := colour} rulesConnected level).symm
    (((Network.singleEdge colour).iteratedCellEmbedding (system.ruleFamily rulesConnected)
      (Network.singleEdge_loopless colour) () level).vertex vertex)

theorem replantedRuleVertex_plus (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (colour : Fin K) (level : ℕ) :
    replantedRuleVertex system rulesConnected colour level
      (((system.ruleFamily rulesConnected).R colour).inlIter (system.ruleFamily rulesConnected)
        ((system.ruleFamily rulesConnected).βplus colour) level) =
      xiPositiveTerminal {system with initCol := colour} (1 + level) := by
  unfold replantedRuleVertex
  exact (congrArg
    (Network.castVertex
      (xiNetwork_one_add_substIter {system with initCol := colour} rulesConnected level).symm)
    ((Network.singleEdge colour).iteratedCellEmbedding_plus (system.ruleFamily rulesConnected)
      (Network.singleEdge_loopless colour) () level)).trans
    (xiNetwork_one_add_substIter_plus {system with initCol := colour} rulesConnected level)

theorem replantedRuleVertex_minus (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (colour : Fin K) (level : ℕ) :
    replantedRuleVertex system rulesConnected colour level
      (((system.ruleFamily rulesConnected).R colour).inlIter (system.ruleFamily rulesConnected)
        ((system.ruleFamily rulesConnected).βminus colour) level) =
      xiNegativeTerminal {system with initCol := colour} (1 + level) := by
  unfold replantedRuleVertex
  exact (congrArg
    (Network.castVertex
      (xiNetwork_one_add_substIter {system with initCol := colour} rulesConnected level).symm)
    ((Network.singleEdge colour).iteratedCellEmbedding_minus (system.ruleFamily rulesConnected)
      (Network.singleEdge_loopless colour) () level)).trans
    (xiNetwork_one_add_substIter_minus {system with initCol := colour} rulesConnected level)

theorem replantedRuleVertex_boundary (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (colour : Fin K) (level : ℕ) :
    ((Network.singleEdge colour).iteratedCellBoundary (system.ruleFamily rulesConnected) () level).image
        (replantedRuleVertex system rulesConnected colour level) =
      {xiPositiveTerminal {system with initCol := colour} (1 + level),
        xiNegativeTerminal {system with initCol := colour} (1 + level)} := by
  simp only [Network.iteratedCellBoundary, Network.singleEdge, Finset.image_insert, Finset.image_singleton,
    replantedRuleVertex_plus, replantedRuleVertex_minus]

/-- The rule carrier and the canonically replanted Xi graph have exactly
the same two-terminal exit time at every corresponding starting vertex. -/
theorem ruleFamily_iterated_expExit_eq_replanted (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (colour : Fin K) (level : ℕ)
    (vertex : (((system.ruleFamily rulesConnected).R colour).substIter
      (system.ruleFamily rulesConnected) level).V) :
    EIGS.expExit (XiSimpleGraph {system with initCol := colour} (1 + level))
        {xiPositiveTerminal {system with initCol := colour} (1 + level),
          xiNegativeTerminal {system with initCol := colour} (1 + level)}ᶜ
        (replantedRuleVertex system rulesConnected colour level vertex) =
      EIGS.expExit (((system.ruleFamily rulesConnected).R colour).substIter
          (system.ruleFamily rulesConnected) level).toSimpleGraph
        ((Network.singleEdge colour).iteratedCellBoundary (system.ruleFamily rulesConnected) () level)ᶜ
        vertex := by
  have target_connected : (((Network.singleEdge colour).subst (system.ruleFamily rulesConnected)).substIter
      (system.ruleFamily rulesConnected) level).toSimpleGraph.Connected := by
    have connected := xiSimpleGraph_connected {system with initCol := colour} rulesConnected (1 + level)
    change (XiNetwork {system with initCol := colour} (1 + level)).toSimpleGraph.Connected at connected
    rw [xiNetwork_one_add_substIter {system with initCol := colour} rulesConnected level] at connected
    exact connected
  have target_degree : ∀ vertex,
      0 < (((Network.singleEdge colour).subst (system.ruleFamily rulesConnected)).substIter
        (system.ruleFamily rulesConnected) level).toSimpleGraph.degree vertex := by
    have positive : ∀ vertex,
        0 < (XiNetwork {system with initCol := colour} (1 + level)).toSimpleGraph.degree vertex := by
      intro vertex
      exact_mod_cast xiSimpleGraph_degree_positive {system with initCol := colour}
        rulesConnected (1 + level) vertex
    rw [xiNetwork_one_add_substIter {system with initCol := colour} rulesConnected level] at positive
    exact positive
  have cast_exit := Network.expExit_cast
    (xiNetwork_one_add_substIter {system with initCol := colour} rulesConnected level).symm
    (((Network.singleEdge colour).iteratedCellBoundary (system.ruleFamily rulesConnected) () level).image
      ((Network.singleEdge colour).iteratedCellEmbedding (system.ruleFamily rulesConnected)
        (Network.singleEdge_loopless colour) () level).vertex)
    (((Network.singleEdge colour).iteratedCellEmbedding (system.ruleFamily rulesConnected)
      (Network.singleEdge_loopless colour) () level).vertex vertex)
  rw [Finset.image_image] at cast_exit
  change EIGS.expExit (XiSimpleGraph {system with initCol := colour} (1 + level))
    (((Network.singleEdge colour).iteratedCellBoundary (system.ruleFamily rulesConnected) () level).image
      (replantedRuleVertex system rulesConnected colour level))ᶜ
    (replantedRuleVertex system rulesConnected colour level vertex) = _ at cast_exit
  rw [replantedRuleVertex_boundary] at cast_exit
  exact cast_exit.trans ((Network.singleEdge colour).iteratedCellEmbedding_expExit
    (system.ruleFamily rulesConnected) (Network.singleEdge_loopless colour) () level
    (ruleFamily_iterated_connected system rulesConnected colour level) target_connected
    (ruleFamily_iterated_degree_positive system rulesConnected colour level) target_degree vertex)

end
end EIGS

#print axioms EIGS.Network.expExit_cast
#print axioms EIGS.xiNetwork_one_add_substIter_plus
#print axioms EIGS.xiNetwork_one_add_substIter_minus
#print axioms EIGS.replantedRuleVertex_plus
#print axioms EIGS.replantedRuleVertex_minus
#print axioms EIGS.replantedRuleVertex_boundary
#print axioms EIGS.ruleFamily_iterated_expExit_eq_replanted
