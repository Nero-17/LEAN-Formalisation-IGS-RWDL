import RequestProject.Section2Substitution
import RequestProject.Section2Simplicity

/-!
# A precise audit witness for antiparallel directed arcs

This witness is an audit of the larger legacy directed-network type. It is not
an instance claimed to satisfy the paper's intended graph convention. A rule
with two antiparallel arcs on each of two successive links carries four electrical
resistors, whereas its underlying simple graph has only two links.
-/

namespace EIGS.AntiparallelAudit

open scoped BigOperators

inductive Vertex
  | source | middle | sink
  deriving DecidableEq

instance : Fintype Vertex :=
  ⟨{Vertex.source, Vertex.middle, Vertex.sink}, by intro vertex; cases vertex <;> simp⟩

@[simp] theorem source_ne_middle : Vertex.source ≠ Vertex.middle := by decide
@[simp] theorem source_ne_sink : Vertex.source ≠ Vertex.sink := by decide
@[simp] theorem middle_ne_source : Vertex.middle ≠ Vertex.source := by decide
@[simp] theorem middle_ne_sink : Vertex.middle ≠ Vertex.sink := by decide
@[simp] theorem sink_ne_source : Vertex.sink ≠ Vertex.source := by decide
@[simp] theorem sink_ne_middle : Vertex.sink ≠ Vertex.middle := by decide

def network : EIGS.Network 1 where
  V := Vertex
  E := Fin 4
  fintypeV := inferInstance
  decEqV := inferInstance
  fintypeE := inferInstance
  tail := ![Vertex.source, Vertex.middle, Vertex.middle, Vertex.sink]
  head := ![Vertex.middle, Vertex.source, Vertex.sink, Vertex.middle]
  color := fun _ => 0

noncomputable def terminalFlow : network.Flow Vertex.source Vertex.sink :=
  ⟨![1 / 2, -(1 / 2), 1 / 2, -(1 / 2)], by
    intro vertex
    dsimp only [Network.div, network]
    cases vertex <;>
      norm_num [Network.div, network, Fin.sum_univ_succ]⟩

theorem loopless : network.Loopless := by
  intro edge
  fin_cases edge <;> decide

theorem not_unique_edges : ¬ network.EdgesUnique := by
  intro unique_edges
  have contradiction := unique_edges (0 : Fin 4) (1 : Fin 4)
    (Or.inr ⟨rfl, rfl⟩)
  exact Fin.zero_ne_one contradiction

theorem electrical_edge_card : Fintype.card network.E = 4 := rfl

/-- Four directed resistors give resistance one, rather than the resistance
two of the underlying unoriented two-link path. -/
theorem effective_resistance :
    network.effRes Vertex.source Vertex.sink ⟨terminalFlow⟩ (fun _ => 1) = 1 := by
  apply le_antisymm
  · convert network.effRes_le_energy Vertex.source Vertex.sink ⟨terminalFlow⟩ (fun _ => zero_le_one)
      terminalFlow using 1
    dsimp only [Network.energyNetwork, terminalFlow, network]
    norm_num [Network.energyNetwork, terminalFlow, network, Fin.sum_univ_succ]
  · apply network.le_effRes Vertex.source Vertex.sink ⟨terminalFlow⟩
    intro flow
    have source_divergence := flow.property Vertex.source
    have sink_divergence := flow.property Vertex.sink
    dsimp only [Network.div, network] at source_divergence sink_divergence
    norm_num [Network.div, network, Fin.sum_univ_succ] at source_divergence sink_divergence
    dsimp only [Network.energyNetwork, network]
    norm_num [Network.energyNetwork, network, Fin.sum_univ_succ]
    have source_square := congrArg (fun value : ℝ => value ^ 2) source_divergence
    have sink_square := congrArg (fun value : ℝ => value ^ 2) sink_divergence
    simp only [one_pow, neg_one_sq] at source_square sink_square
    nlinarith [sq_nonneg (flow.1 (0 : Fin 4) + flow.1 (1 : Fin 4)),
      sq_nonneg (flow.1 (2 : Fin 4) + flow.1 (Fin.succ (2 : Fin 3)))]

end EIGS.AntiparallelAudit
