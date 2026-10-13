import RequestProject.Outlook.FourColourGraphRealization

/-! Passing from the ambient incidence identification to the genuine source
cluster removes every inactive isolated vertex from both sides. -/
namespace Cluster.TTN

namespace IncidenceIso

theorem adjacent_forward {firstNetwork secondNetwork : TTN}
    (isomorphism : IncidenceIso firstNetwork secondNetwork) {firstVertex secondVertex : firstNetwork.V}
    (adjacent : firstNetwork.underlyingGraph.Adj firstVertex secondVertex) :
    secondNetwork.underlyingGraph.Adj (isomorphism.vertices firstVertex) (isomorphism.vertices secondVertex) := by
  rcases adjacent with ⟨distinct, forward | backward⟩
  · refine ⟨fun equal => distinct (isomorphism.vertices.injective equal), Or.inl ?_⟩
    rcases forward with ⟨edge, tail, head⟩
    exact ⟨isomorphism.edges edge, by rw [← isomorphism.tail, tail], by rw [← isomorphism.head, head]⟩
  · refine ⟨fun equal => distinct (isomorphism.vertices.injective equal), Or.inr ?_⟩
    rcases backward with ⟨edge, tail, head⟩
    exact ⟨isomorphism.edges edge, by rw [← isomorphism.tail, tail], by rw [← isomorphism.head, head]⟩

theorem adjacent_iff {firstNetwork secondNetwork : TTN}
    (isomorphism : IncidenceIso firstNetwork secondNetwork) (firstVertex secondVertex : firstNetwork.V) :
    secondNetwork.underlyingGraph.Adj (isomorphism.vertices firstVertex) (isomorphism.vertices secondVertex) ↔
      firstNetwork.underlyingGraph.Adj firstVertex secondVertex := by
  constructor
  · intro adjacent
    simpa only [symm, Equiv.symm_apply_apply] using isomorphism.symm.adjacent_forward adjacent
  · exact isomorphism.adjacent_forward

end IncidenceIso

def sourceClusterGraph (network : TTN) :
    SimpleGraph {vertex : network.V // network.EdgePath network.a vertex} :=
  network.underlyingGraph.induce {vertex | network.EdgePath network.a vertex}

def IncidenceIso.sourceClusterIso {firstNetwork secondNetwork : TTN}
    (isomorphism : IncidenceIso firstNetwork secondNetwork) :
    sourceClusterGraph firstNetwork ≃g sourceClusterGraph secondNetwork where
  toEquiv := isomorphism.vertices.subtypeEquiv (fun vertex => by
    simpa only [isomorphism.source] using isomorphism.edgePath_iff firstNetwork.a vertex)
  map_rel_iff' := by
    intro firstVertex secondVertex
    exact isomorphism.adjacent_iff firstVertex.1 secondVertex.1

theorem retainedNetwork_adjacent_iff (network : TTN) (parent : Fin 4) (reversed : Bool)
    {firstVertex secondVertex : network.V}
    (firstActive : activeComponent network parent reversed firstVertex)
    (secondActive : activeComponent network parent reversed secondVertex) :
    (retainedNetwork network parent reversed).underlyingGraph.Adj firstVertex secondVertex ↔
      network.underlyingGraph.Adj firstVertex secondVertex := by
  constructor
  · rintro ⟨distinct, forward | backward⟩
    · rcases forward with ⟨edge, tail, head⟩
      exact ⟨distinct, Or.inl ⟨edge.1, tail, head⟩⟩
    · rcases backward with ⟨edge, tail, head⟩
      exact ⟨distinct, Or.inr ⟨edge.1, tail, head⟩⟩
  · rintro ⟨distinct, forward | backward⟩
    · rcases forward with ⟨edge, tail, head⟩
      have retained : retainedEdge network parent reversed edge := by
        change activeComponent network parent reversed (network.tail edge)
        rw [tail]
        exact firstActive
      exact ⟨distinct, Or.inl ⟨⟨edge, retained⟩, tail, head⟩⟩
    · rcases backward with ⟨edge, tail, head⟩
      have retained : retainedEdge network parent reversed edge := by
        change activeComponent network parent reversed (network.tail edge)
        rw [tail]
        exact secondActive
      exact ⟨distinct, Or.inr ⟨⟨edge, retained⟩, tail, head⟩⟩

noncomputable def retainedSourceClusterIso (network : TTN) :
    sourceClusterGraph (retainedNetwork network 0 false) ≃g sourceClusterGraph network where
  toEquiv := (Equiv.refl network.V).subtypeEquiv (fun vertex =>
    retainedNetwork_path_iff network 0 false (Or.inl (edgePath_self network network.a)))
  map_rel_iff' := by
    intro firstVertex secondVertex
    exact (retainedNetwork_adjacent_iff network 0 false
      (Or.inl (retainedNetwork_path_to_original network 0 false firstVertex.2))
      (Or.inl (retainedNetwork_path_to_original network 0 false secondVertex.2))).symm

end Cluster.TTN

namespace Outlook.FourColourClusterIsomorphism
open Cluster FourColourConditionalHierarchy FourColourCodingTree FourColourGraphRealization

/-- The graph reconstructed from the adopted encoded tree has exactly the
actual source cluster, with all inactive ambient vertices removed. -/
noncomputable def actualRedClusterIso (depth : ℕ) (configuration : Conf depth)
    (connected : configuration ∈ parentEvent depth 0) :
    TTN.sourceClusterGraph (realize depth 0 (encode depth 0 configuration)) ≃g
      TTN.sourceClusterGraph (net depth configuration) :=
  (actualRealizationIso depth 0 configuration connected).sourceClusterIso.trans
    (TTN.retainedSourceClusterIso (net depth configuration))

end Outlook.FourColourClusterIsomorphism

#print axioms Cluster.TTN.IncidenceIso.sourceClusterIso
#print axioms Cluster.TTN.retainedSourceClusterIso
#print axioms Outlook.FourColourClusterIsomorphism.actualRedClusterIso
