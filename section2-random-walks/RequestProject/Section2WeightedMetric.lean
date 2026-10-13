import RequestProject.Section2WeightedWalk
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! The actual nonnegative weighted graph distance, defined using all labelled
network walks. Its unit-length specialization is the native graph distance. -/

namespace EIGS.Network

open scoped BigOperators

variable {K : ℕ} (network : Network K)

noncomputable def weightedDistance (lengths : Fin K → ℝ) (source sink : network.V) : ℝ :=
  ⨅ walk : network.EdgeWalk source sink, walk.cost lengths

theorem edgeWalk_nonempty_of_connected (connected : network.toSimpleGraph.Connected)
    (source sink : network.V) : Nonempty (network.EdgeWalk source sink) := by
  obtain ⟨walk⟩ := connected source sink
  exact ⟨EdgeWalk.ofGraphWalk walk⟩

theorem weightedDistance_le_cost {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths)
    {source sink : network.V} (walk : network.EdgeWalk source sink) :
    network.weightedDistance lengths source sink ≤ walk.cost lengths := by
  exact ciInf_le ⟨0, fun value membership => by
    obtain ⟨candidate, rfl⟩ := membership
    exact candidate.cost_nonnegative nonnegative⟩ walk

theorem weightedDistance_nonnegative (connected : network.toSimpleGraph.Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths) (source sink : network.V) :
    0 ≤ network.weightedDistance lengths source sink := by
  letI := network.edgeWalk_nonempty_of_connected connected source sink
  exact le_ciInf (fun walk => walk.cost_nonnegative nonnegative)

@[simp] theorem weightedDistance_self {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths)
    (vertex : network.V) : network.weightedDistance lengths vertex vertex = 0 := by
  have lower : 0 ≤ network.weightedDistance lengths vertex vertex := by
    letI : Nonempty (network.EdgeWalk vertex vertex) := ⟨.nil vertex⟩
    exact le_ciInf (fun walk => walk.cost_nonnegative nonnegative)
  exact le_antisymm (network.weightedDistance_le_cost nonnegative (.nil vertex)) lower

theorem weightedDistance_symm (connected : network.toSimpleGraph.Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths) (source sink : network.V) :
    network.weightedDistance lengths source sink =
      network.weightedDistance lengths sink source := by
  have comparison (first last : network.V) :
      network.weightedDistance lengths first last ≤ network.weightedDistance lengths last first := by
    letI := network.edgeWalk_nonempty_of_connected connected last first
    apply le_ciInf
    intro walk
    simpa only [EdgeWalk.cost_reverse] using
      network.weightedDistance_le_cost nonnegative walk.reverse
  exact le_antisymm (comparison source sink) (comparison sink source)

theorem weightedDistance_triangle_of_walks
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths)
    (source middle sink : network.V)
    (first_nonempty : Nonempty (network.EdgeWalk source middle))
    (second_nonempty : Nonempty (network.EdgeWalk middle sink)) :
    network.weightedDistance lengths source sink ≤
      network.weightedDistance lengths source middle + network.weightedDistance lengths middle sink := by
  letI := first_nonempty
  letI := second_nonempty
  apply le_of_forall_pos_le_add
  intro tolerance tolerance_positive
  obtain ⟨first, first_bound⟩ := exists_lt_of_ciInf_lt
    (lt_add_of_pos_right (network.weightedDistance lengths source middle) (half_pos tolerance_positive))
  obtain ⟨second, second_bound⟩ := exists_lt_of_ciInf_lt
    (lt_add_of_pos_right (network.weightedDistance lengths middle sink) (half_pos tolerance_positive))
  have bound := network.weightedDistance_le_cost nonnegative (first.append second)
  rw [EdgeWalk.cost_append] at bound
  linarith

theorem weightedDistance_triangle (connected : network.toSimpleGraph.Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths)
    (source middle sink : network.V) :
    network.weightedDistance lengths source sink ≤
      network.weightedDistance lengths source middle + network.weightedDistance lengths middle sink :=
  network.weightedDistance_triangle_of_walks nonnegative source middle sink
    (network.edgeWalk_nonempty_of_connected connected source middle)
    (network.edgeWalk_nonempty_of_connected connected middle sink)

theorem weightedDistance_edge {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths)
    (edge : network.E) :
    network.weightedDistance lengths (network.tail edge) (network.head edge) ≤
      lengths (network.color edge) := by
  simpa only [EdgeWalk.cost, add_zero] using network.weightedDistance_le_cost nonnegative
    (EdgeWalk.cons edge (Or.inl ⟨rfl, rfl⟩) (.nil (network.head edge)))

def EdgeLipschitz (lengths : Fin K → ℝ) (potential : network.V → ℝ) : Prop :=
  ∀ edge : network.E, |potential (network.tail edge) - potential (network.head edge)| ≤
    lengths (network.color edge)

theorem EdgeWalk.potential_difference_le_cost {lengths : Fin K → ℝ}
    {potential : network.V → ℝ} (lipschitz : network.EdgeLipschitz lengths potential)
    {source sink : network.V} (walk : network.EdgeWalk source sink) :
    |potential source - potential sink| ≤ walk.cost lengths := by
  induction walk with
  | nil => simp [EdgeWalk.cost]
  | @cons source next sink edge joins rest induction_hypothesis =>
    have first_bound : |potential source - potential next| ≤ lengths (network.color edge) := by
      rcases joins with ⟨tail_eq, head_eq⟩ | ⟨tail_eq, head_eq⟩
      · simpa only [tail_eq, head_eq] using lipschitz edge
      · simpa only [tail_eq, head_eq, abs_sub_comm] using lipschitz edge
    exact (abs_sub_le (potential source) (potential next) (potential sink)).trans
      (add_le_add first_bound induction_hypothesis)

theorem potential_difference_le_weightedDistance (connected : network.toSimpleGraph.Connected)
    {lengths : Fin K → ℝ} {potential : network.V → ℝ}
    (lipschitz : network.EdgeLipschitz lengths potential) (source sink : network.V) :
    |potential source - potential sink| ≤ network.weightedDistance lengths source sink := by
  letI := network.edgeWalk_nonempty_of_connected connected source sink
  exact le_ciInf (fun walk => walk.potential_difference_le_cost network lipschitz)

theorem weightedDistance_edgeLipschitz (connected : network.toSimpleGraph.Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths) (source : network.V) :
    network.EdgeLipschitz lengths (network.weightedDistance lengths source) := by
  intro edge
  apply abs_le.mpr
  have forward := network.weightedDistance_triangle connected nonnegative source
    (network.tail edge) (network.head edge)
  have backward := network.weightedDistance_triangle connected nonnegative source
    (network.head edge) (network.tail edge)
  have edge_bound := network.weightedDistance_edge nonnegative edge
  have reverse_bound : network.weightedDistance lengths (network.head edge) (network.tail edge) ≤
      lengths (network.color edge) := by
    rw [network.weightedDistance_symm connected nonnegative]
    exact edge_bound
  constructor <;> linarith

theorem EdgeWalk.cost_unit_eq_graphWalk_length (loopless : network.Loopless)
    {source sink : network.V} (walk : network.EdgeWalk source sink) :
    walk.cost (fun _ => 1) = ((walk.toGraphWalk loopless).length : ℝ) := by
  induction walk with
  | nil => simp [EdgeWalk.cost, EdgeWalk.toGraphWalk]
  | cons edge joins rest induction_hypothesis =>
    simp [EdgeWalk.cost, EdgeWalk.toGraphWalk, induction_hypothesis, add_comm]

theorem weightedDistance_unit_eq_graphDistance (connected : network.toSimpleGraph.Connected)
    (loopless : network.Loopless) (source sink : network.V) :
    network.weightedDistance (fun _ => 1) source sink =
      (network.toSimpleGraph.dist source sink : ℝ) := by
  letI := network.edgeWalk_nonempty_of_connected connected source sink
  obtain ⟨shortest, simple_shortest, shortest_length⟩ :=
    (connected source sink).exists_path_of_dist
  apply le_antisymm
  · have bound := network.weightedDistance_le_cost (fun _ => zero_le_one)
      (EdgeWalk.ofGraphWalk shortest)
    simpa only [EdgeWalk.cost_unit_eq_graphWalk_length network loopless,
      EdgeWalk.toGraphWalk_ofGraphWalk, shortest_length] using bound
  · apply le_ciInf
    intro walk
    rw [EdgeWalk.cost_unit_eq_graphWalk_length network loopless]
    exact_mod_cast network.toSimpleGraph.dist_le (walk.toGraphWalk loopless)

theorem weightedDistance_subst_le_lift (rules : RuleFamily K)
    (connected : network.toSimpleGraph.Connected)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths)
    (selected : ∀ colour, (rules.R colour).EdgeWalk
      (rules.βplus colour) (rules.βminus colour)) (source sink : network.V) :
    (network.subst rules).weightedDistance lengths (Sum.inl source) (Sum.inl sink) ≤
      network.weightedDistance (fun colour => (selected colour).cost lengths) source sink := by
  letI := network.edgeWalk_nonempty_of_connected connected source sink
  apply le_ciInf
  intro walk
  have bound := (network.subst rules).weightedDistance_le_cost nonnegative
    (network.liftEdgeWalk rules selected walk)
  simpa only [network.cost_liftEdgeWalk] using bound

end EIGS.Network
