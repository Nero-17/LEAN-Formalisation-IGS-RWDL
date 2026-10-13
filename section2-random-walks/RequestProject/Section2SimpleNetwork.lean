import RequestProject.Section2Simplicity
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace EIGS.Network

open scoped BigOperators Classical

variable {K : ℕ} (network : Network K)

/-- Each chosen oriented edge supplies precisely the two darts of its
underlying simple undirected edge. -/
noncomputable def simpleDartEquiv (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique) : network.E × Bool ≃ network.toSimpleGraph.Dart := by
  let dart_map : network.E × Bool → network.toSimpleGraph.Dart := fun pair =>
    if pair.2 then
      ⟨(network.head pair.1, network.tail pair.1),
        ⟨(loopless pair.1).symm, Or.inr ⟨pair.1, rfl, rfl⟩⟩⟩
    else
      ⟨(network.tail pair.1, network.head pair.1),
        ⟨loopless pair.1, Or.inl ⟨pair.1, rfl, rfl⟩⟩⟩
  apply Equiv.ofBijective dart_map
  constructor
  · rintro ⟨first, first_reverse⟩ ⟨second, second_reverse⟩ same
    have edges_same : first = second := by
      apply unique_edges first second
      apply Sym2.eq_iff.mp
      have edges_same := congrArg SimpleGraph.Dart.edge same
      cases first_reverse <;> cases second_reverse <;>
        simpa [dart_map, SimpleGraph.Dart.edge, Sym2.eq_swap] using edges_same
    subst second
    cases first_reverse <;> cases second_reverse
    · rfl
    · have endpoints_same := congrArg (fun dart : network.toSimpleGraph.Dart => dart.fst) same
      exact (loopless first (by simpa [dart_map] using endpoints_same)).elim
    · have endpoints_same := congrArg (fun dart : network.toSimpleGraph.Dart => dart.fst) same
      exact (loopless first (by simpa [dart_map] using endpoints_same.symm)).elim
    · rfl
  · intro dart
    rcases dart.adj.2 with ⟨edge, tail_eq, head_eq⟩ | ⟨edge, tail_eq, head_eq⟩
    · refine ⟨(edge, false), SimpleGraph.Dart.ext _ _ ?_⟩
      simp [dart_map, tail_eq, head_eq]
    · refine ⟨(edge, true), SimpleGraph.Dart.ext _ _ ?_⟩
      simp [dart_map, tail_eq, head_eq]

theorem sum_adj_eq_sum_edges (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique) (function : network.V → network.V → ℝ) :
    (∑ source, ∑ sink, if network.toSimpleGraph.Adj source sink then function source sink else 0) =
      ∑ edge, (function (network.tail edge) (network.head edge) +
        function (network.head edge) (network.tail edge)) := by
  let dart_sigma : network.toSimpleGraph.Dart ≃
      Σ source, network.toSimpleGraph.neighborSet source :=
    { toFun := fun dart => ⟨dart.fst, dart.snd, dart.adj⟩
      invFun := fun pair => ⟨(pair.1, pair.2.1), pair.2.2⟩
      left_inv := fun dart => by cases dart; rfl
      right_inv := fun pair => by cases pair; rfl }
  have sum_darts : (∑ dart : network.toSimpleGraph.Dart, function dart.fst dart.snd) =
      ∑ source, ∑ sink, if network.toSimpleGraph.Adj source sink then function source sink else 0 := by
    have reindex_sum := dart_sigma.sum_comp (fun pair => function pair.1 pair.2.1)
    change (∑ dart : network.toSimpleGraph.Dart, function dart.fst dart.snd) =
      ∑ pair : Σ source, network.toSimpleGraph.neighborSet source,
        function pair.1 pair.2.1 at reindex_sum
    rw [reindex_sum]
    simp only [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro source _
    rw [← Finset.sum_subtype (network.toSimpleGraph.neighborFinset source)
      (fun sink => by simp)]
    rw [SimpleGraph.neighborFinset_def, ← Finset.sum_filter]
    apply Finset.sum_congr
    · ext sink
      simp
    · intro sink _
      rfl
  rw [← sum_darts, ← (network.simpleDartEquiv loopless unique_edges).sum_comp
    (fun dart => function dart.fst dart.snd)]
  simp [simpleDartEquiv, Fintype.sum_prod_type, add_comm]

/-- The potential energy on chosen oriented edges is exactly the conventional
simple-graph energy, with the factor one-half accounting for two darts. -/
theorem potential_energy_eq_simpleGraph (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique) (potential : network.V → ℝ) :
    (∑ edge, (potential (network.tail edge) - potential (network.head edge)) ^ 2) =
      (∑ source, ∑ sink, if network.toSimpleGraph.Adj source sink then
        (potential source - potential sink) ^ 2 else 0) / 2 := by
  rw [network.sum_adj_eq_sum_edges loopless unique_edges]
  have summand : ∀ edge : network.E,
      (potential (network.tail edge) - potential (network.head edge)) ^ 2 +
        (potential (network.head edge) - potential (network.tail edge)) ^ 2 =
      2 * (potential (network.tail edge) - potential (network.head edge)) ^ 2 := by
    intro edge
    ring
  simp_rw [summand]
  rw [← Finset.mul_sum]
  ring

/-- An oriented edge current represented as an antisymmetric vertex-pair
current. The sums retain orientation signs explicitly. -/
noncomputable def pairCurrent (current : network.E → ℝ) (source sink : network.V) : ℝ :=
  (∑ edge, if network.tail edge = source ∧ network.head edge = sink then current edge else 0) -
    ∑ edge, if network.tail edge = sink ∧ network.head edge = source then current edge else 0

theorem pairCurrent_antisymmetric (current : network.E → ℝ) (source sink : network.V) :
    network.pairCurrent current source sink = - network.pairCurrent current sink source := by
  unfold pairCurrent
  ring

theorem pairCurrent_on_edge (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique) (current : network.E → ℝ) (edge : network.E) :
    network.pairCurrent current (network.tail edge) (network.head edge) = current edge := by
  have forward_sum : (∑ other, if network.tail other = network.tail edge ∧
      network.head other = network.head edge then current other else 0) = current edge := by
    rw [Finset.sum_eq_single edge]
    · simp
    · intro other _ other_ne
      split_ifs with endpoints
      · exact (other_ne (unique_edges other edge (Or.inl endpoints))).elim
      · rfl
    · simp
  have reverse_sum : (∑ other, if network.tail other = network.head edge ∧
      network.head other = network.tail edge then current other else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro other _
    split_ifs with endpoints
    · have same_edge := unique_edges other edge (Or.inr endpoints)
      subst other
      exact (loopless edge endpoints.1).elim
    · rfl
  exact by unfold pairCurrent; rw [forward_sum, reverse_sum, sub_zero]

/-- Divergence is unchanged by passing between the oriented-edge and
antisymmetric vertex-pair representations. -/
theorem div_restrict_eq_simpleGraph (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique) (current : network.V → network.V → ℝ)
    (antisymmetric : ∀ source sink, current source sink = - current sink source)
    (vertex : network.V) :
    network.div (fun edge => current (network.tail edge) (network.head edge)) vertex =
      ∑ neighbor, if network.toSimpleGraph.Adj vertex neighbor then current vertex neighbor else 0 := by
  have pair_sum := network.sum_adj_eq_sum_edges loopless unique_edges
    (fun source sink => if source = vertex then current source sink else 0)
  have left_sum :
      (∑ source, ∑ sink, if network.toSimpleGraph.Adj source sink then
        (if source = vertex then current source sink else 0) else 0) =
      ∑ neighbor, if network.toSimpleGraph.Adj vertex neighbor then current vertex neighbor else 0 := by
    calc
      _ = ∑ source, if source = vertex then
          (∑ sink, if network.toSimpleGraph.Adj source sink then current source sink else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro source _
        by_cases same : source = vertex <;> simp [same]
      _ = _ := by simp
  rw [left_sum] at pair_sum
  rw [pair_sum]
  unfold Network.div
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  rw [antisymmetric (network.head edge) (network.tail edge)]
  by_cases tail_eq : network.tail edge = vertex <;>
    by_cases head_eq : network.head edge = vertex <;> simp [tail_eq, head_eq]

theorem energy_restrict_eq_simpleGraph (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique) (current : network.V → network.V → ℝ)
    (antisymmetric : ∀ source sink, current source sink = - current sink source) :
    network.energyNetwork (fun edge => current (network.tail edge) (network.head edge)) (fun _ => 1) =
      (∑ source, ∑ sink, if network.toSimpleGraph.Adj source sink then
        (current source sink) ^ 2 else 0) / 2 := by
  rw [network.sum_adj_eq_sum_edges loopless unique_edges]
  have summand : ∀ edge : network.E,
      (current (network.tail edge) (network.head edge)) ^ 2 +
        (current (network.head edge) (network.tail edge)) ^ 2 =
      2 * (current (network.tail edge) (network.head edge)) ^ 2 := by
    intro edge
    rw [antisymmetric (network.head edge) (network.tail edge), neg_sq]
    ring
  simp_rw [summand]
  rw [← Finset.mul_sum]
  simp [Network.energyNetwork]

theorem div_pairCurrent (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique) (current : network.E → ℝ) (vertex : network.V) :
    (∑ neighbor, if network.toSimpleGraph.Adj vertex neighbor then
      network.pairCurrent current vertex neighbor else 0) = network.div current vertex := by
  rw [← network.div_restrict_eq_simpleGraph loopless unique_edges _
    (network.pairCurrent_antisymmetric current)]
  congr 1
  funext edge
  exact network.pairCurrent_on_edge loopless unique_edges current edge

theorem energy_pairCurrent (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique) (current : network.E → ℝ) :
    (∑ source, ∑ sink, if network.toSimpleGraph.Adj source sink then
      (network.pairCurrent current source sink) ^ 2 else 0) / 2 =
      network.energyNetwork current (fun _ => 1) := by
  rw [← network.energy_restrict_eq_simpleGraph loopless unique_edges _
    (network.pairCurrent_antisymmetric current)]
  congr 1
  funext edge
  exact network.pairCurrent_on_edge loopless unique_edges current edge

end EIGS.Network
