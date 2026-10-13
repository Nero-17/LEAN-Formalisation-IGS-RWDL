import RequestProject.Outlook.FourColourGraphLocalization
import RequestProject.Outlook.FourColourNetworkReflection

/-! The actual retained graph is defined by genuine component membership in
the existing percolation network. Black has no active vertices. Green retains
the component of its marked active endpoint, with its orientation explicit. -/
namespace Cluster.TTN

def activeComponent (network : TTN) (parent : Fin 4) (reversed : Bool) (vertex : network.V) : Prop :=
  if parent=3 then False else if parent=2 then
    (if reversed then network.EdgePath network.b vertex else network.EdgePath network.a vertex)
  else boundaryComponent network vertex

def retainedGraph (network : TTN) (parent : Fin 4) (reversed : Bool) :
    SimpleGraph {vertex : network.V // activeComponent network parent reversed vertex} :=
  network.underlyingGraph.induce {vertex | activeComponent network parent reversed vertex}

def retainedEdge (network : TTN) (parent : Fin 4) (reversed : Bool) (edge : network.E) : Prop :=
  activeComponent network parent reversed (network.tail edge)

theorem activeComponent_edge (network : TTN) (parent : Fin 4) (reversed : Bool) (edge : network.E) :
    activeComponent network parent reversed (network.tail edge) ↔
      activeComponent network parent reversed (network.head edge) := by
  unfold activeComponent
  split
  · rfl
  · split
    · split
      · exact component_edge_iff network network.b edge
      · exact component_edge_iff network network.a edge
    · exact Iff.of_eq (boundaryComponent_edge network edge)

theorem retainedEdge_endpoints (network : TTN) (parent : Fin 4) (reversed : Bool) (edge : network.E) :
    retainedEdge network parent reversed edge ↔
      activeComponent network parent reversed (network.tail edge) ∧
        activeComponent network parent reversed (network.head edge) := by
  change activeComponent network parent reversed (network.tail edge) ↔ _
  rw [← activeComponent_edge]
  exact ⟨fun active => ⟨active, active⟩, And.left⟩

theorem activeComponent_reflection {firstNetwork secondNetwork : TTN}
    (reflection : Reflection firstNetwork secondNetwork) (parent : Fin 4) (reversed : Bool)
    (vertex : firstNetwork.V) :
    activeComponent firstNetwork parent reversed vertex ↔
      activeComponent secondNetwork parent (!reversed) (reflection.vertices vertex) := by
  have fromSource : firstNetwork.EdgePath firstNetwork.a vertex ↔
      secondNetwork.EdgePath secondNetwork.b (reflection.vertices vertex) := by
    simpa only [reflection.source] using reflection.edgePath_iff firstNetwork.a vertex
  have fromTarget : firstNetwork.EdgePath firstNetwork.b vertex ↔
      secondNetwork.EdgePath secondNetwork.a (reflection.vertices vertex) := by
    simpa only [reflection.target] using reflection.edgePath_iff firstNetwork.b vertex
  fin_cases parent <;> cases reversed <;>
    simp [activeComponent, boundaryComponent, fromSource, fromTarget, or_comm]

theorem retainedEdge_reflection {firstNetwork secondNetwork : TTN}
    (reflection : Reflection firstNetwork secondNetwork) (parent : Fin 4) (reversed : Bool)
    (edge : firstNetwork.E) :
    retainedEdge firstNetwork parent reversed edge ↔
      retainedEdge secondNetwork parent (!reversed) (reflection.edges edge) := by
  unfold retainedEdge
  rw [activeComponent_reflection reflection, reflection.tail, ← activeComponent_edge]

theorem connected_components_iff (network : TTN)
    (connected : network.EdgePath network.a network.b) (vertex : network.V) :
    network.EdgePath network.a vertex ↔ network.EdgePath network.b vertex :=
  ⟨fun path => edgePath_trans (edgePath_symm connected) path,
    fun path => edgePath_trans connected path⟩

/-- On a connected red parent, the retained graph is precisely its actual
source connected component; no union of extraneous components is retained. -/
theorem red_active_iff_source (network : TTN)
    (connected : network.EdgePath network.a network.b) (vertex : network.V) :
    activeComponent network 0 false vertex ↔ network.underlyingGraph.Reachable network.a vertex := by
  change (network.EdgePath network.a vertex ∨ network.EdgePath network.b vertex) ↔ _
  rw [← connected_components_iff network connected vertex, or_self, edgePath_iff_reachable]

end Cluster.TTN

#print axioms Cluster.TTN.activeComponent_edge
#print axioms Cluster.TTN.retainedEdge_endpoints
#print axioms Cluster.TTN.activeComponent_reflection
#print axioms Cluster.TTN.retainedEdge_reflection
#print axioms Cluster.TTN.red_active_iff_source
