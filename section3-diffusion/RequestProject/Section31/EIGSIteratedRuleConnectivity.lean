import RequestProject.Section31.NetworkEmbeddingGraphIso
import RequestProject.Section31.XiNetworkIteratedSubstitution
import RequestProject.Section31.EIGSCellStarExit

namespace EIGS
open scoped Classical
noncomputable section
variable {K : ℕ}

theorem xiNetwork_one_add_substIter (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (level : ℕ) :
    XiNetwork system (1 + level) =
      ((Network.singleEdge system.initCol).subst (system.ruleFamily rulesConnected)).substIter
        (system.ruleFamily rulesConnected) level := by
  rw [xiNetwork_add_substIter system rulesConnected 1 level]
  have first : XiNetwork system 1 =
      (Network.singleEdge system.initCol).subst (system.ruleFamily rulesConnected) := by
    simpa only [xiNetwork_zero] using xiNetwork_succ system rulesConnected 0
  rw [first]

theorem ruleFamily_iterated_connected (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (colour : Fin K) (level : ℕ) :
    (((system.ruleFamily rulesConnected).R colour).substIter
      (system.ruleFamily rulesConnected) level).toSimpleGraph.Connected := by
  have loopless : (Network.singleEdge colour).Loopless := by
    intro edge
    simp [Network.singleEdge]
  have surjective := Network.iteratedCell_singleEdge_surjective
    (system.ruleFamily rulesConnected) colour loopless level
  apply ((Network.singleEdge colour).iteratedCellEmbedding
    (system.ruleFamily rulesConnected) loopless () level).connected_iff_of_surjective
      surjective.1 surjective.2 |>.mpr
  have connected := xiSimpleGraph_connected {system with initCol := colour} rulesConnected (1 + level)
  change (XiNetwork {system with initCol := colour} (1 + level)).toSimpleGraph.Connected at connected
  rw [xiNetwork_one_add_substIter {system with initCol := colour} rulesConnected level] at connected
  exact connected

theorem ruleFamily_iterated_degree_positive (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (colour : Fin K) (level : ℕ) :
    ∀ vertex, 0 < (((system.ruleFamily rulesConnected).R colour).substIter
      (system.ruleFamily rulesConnected) level).toSimpleGraph.degree vertex := by
  have loopless : (Network.singleEdge colour).Loopless := by
    intro edge
    simp [Network.singleEdge]
  have surjective := Network.iteratedCell_singleEdge_surjective
    (system.ruleFamily rulesConnected) colour loopless level
  apply ((Network.singleEdge colour).iteratedCellEmbedding
    (system.ruleFamily rulesConnected) loopless () level).positive_degree_of_surjective
      surjective.1 surjective.2
  have positive : ∀ vertex,
      0 < (XiNetwork {system with initCol := colour} (1 + level)).toSimpleGraph.degree vertex := by
    intro vertex
    exact_mod_cast xiSimpleGraph_degree_positive {system with initCol := colour}
      rulesConnected (1 + level) vertex
  rw [xiNetwork_one_add_substIter {system with initCol := colour} rulesConnected level] at positive
  exact positive

end
end EIGS

#print axioms EIGS.xiNetwork_one_add_substIter
#print axioms EIGS.ruleFamily_iterated_connected
#print axioms EIGS.ruleFamily_iterated_degree_positive
