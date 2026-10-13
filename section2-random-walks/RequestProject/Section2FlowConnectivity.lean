import RequestProject.Section2Network
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace EIGS

open scoped BigOperators
open scoped Classical

namespace Network

variable {K : ℕ} (network : Network K)

/-- The undirected adjacency relation carried by a finite electrical network. -/
def toSimpleGraph : SimpleGraph network.V :=
  SimpleGraph.fromRel fun source sink =>
    ∃ edge : network.E, network.tail edge = source ∧ network.head edge = sink

lemma div_add (first second : network.E → ℝ) (vertex : network.V) :
    network.div (fun edge => first edge + second edge) vertex =
      network.div first vertex + network.div second vertex := by
  simp only [Network.div, ← Finset.sum_filter, Finset.sum_add_distrib]
  ring

lemma div_scalar (scalar : ℝ) (current : network.E → ℝ) (vertex : network.V) :
    network.div (fun edge => scalar * current edge) vertex =
      scalar * network.div current vertex := by
  simp only [Network.div, mul_ite, mul_zero, Finset.mul_sum, mul_sub]

lemma div_single_edge (selectedEdge : network.E) (vertex : network.V) :
    network.div (fun edge => if edge = selectedEdge then 1 else 0) vertex =
      (if vertex = network.tail selectedEdge then 1 else 0) -
        (if vertex = network.head selectedEdge then 1 else 0) := by
  classical
  unfold Network.div
  rw [Finset.sum_eq_single selectedEdge, Finset.sum_eq_single selectedEdge]
  · simp [eq_comm]
  all_goals intros <;> simp_all

/-- An undirected walk gives a signed current with one unit of transport between
its endpoints.  The formula also permits equal endpoints, giving zero transport. -/
theorem current_of_walk {source sink : network.V}
    (walk : network.toSimpleGraph.Walk source sink) :
    ∃ current : network.E → ℝ, ∀ vertex,
      network.div current vertex = (if vertex = source then 1 else 0) -
        (if vertex = sink then 1 else 0) := by
  classical
  induction walk with
  | nil =>
      exact ⟨fun _ => 0, fun vertex => by simp [Network.div]⟩
  | @cons source next sink adjacent walk induction =>
      obtain ⟨current, current_divergence⟩ := induction
      have edge_exists :
          (∃ edge : network.E, network.tail edge = source ∧ network.head edge = next) ∨
          (∃ edge : network.E, network.tail edge = next ∧ network.head edge = source) := by
        exact adjacent.2
      rcases edge_exists with ⟨edge, tail_eq, head_eq⟩ | ⟨edge, tail_eq, head_eq⟩
      · refine ⟨fun candidate => (if candidate = edge then 1 else 0) + current candidate,
          fun vertex => ?_⟩
        rw [network.div_add, network.div_single_edge, current_divergence, tail_eq, head_eq]
        ring
      · refine ⟨fun candidate => (-1) * (if candidate = edge then 1 else 0) +
          current candidate, fun vertex => ?_⟩
        rw [network.div_add, network.div_scalar, network.div_single_edge,
          current_divergence, tail_eq, head_eq]
        ring

/-- Connected underlying graph and distinct terminals supply an actual unit flow. -/
theorem flow_nonempty_of_connected (connected : network.toSimpleGraph.Connected)
    (source sink : network.V) (terminals_distinct : source ≠ sink) :
    Nonempty (network.Flow source sink) := by
  obtain ⟨walk⟩ := connected source sink
  obtain ⟨current, current_divergence⟩ := network.current_of_walk walk
  refine ⟨current, fun vertex => ?_⟩
  rw [current_divergence]
  by_cases source_eq : vertex = source
  · subst vertex
    simp [terminals_distinct]
  · by_cases sink_eq : vertex = sink <;>
      simp_all [terminals_distinct, Ne.symm terminals_distinct]

end Network

end EIGS

