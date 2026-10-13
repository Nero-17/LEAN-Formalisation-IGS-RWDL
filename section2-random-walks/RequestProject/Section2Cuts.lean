import RequestProject.Section2Monochrome
import RequestProject.Section2FlowConnectivity
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Monochromatic cuts and strict positivity of resistance

This is the finite-network cut argument used in the paper's proof of Lemma 2.6.
The bound is obtained directly from Kirchhoff's law and Cauchy--Schwarz, without
assuming Rayleigh monotonicity or the desired resistance lower bound.
-/

namespace EIGS.Network

open scoped BigOperators

variable {K : ℕ} (network : EIGS.Network K)

/-- Delete one colour before forgetting edge orientation. -/
def withoutColour (colour : Fin K) : SimpleGraph network.V :=
  SimpleGraph.fromRel fun source sink =>
    ∃ edge : network.E, network.color edge ≠ colour ∧
      network.tail edge = source ∧ network.head edge = sink

/-- With at least two colours, distance positivity already excludes an edge
directly joining the planting vertices. The one-colour model imposes distance
at least two separately. -/
theorem terminals_nonadjacent_of_distance_positive (source sink : network.V)
    (colours_at_least_two : 2 ≤ K)
    (distance_positive : ∀ colour : Fin K,
      ¬ (network.withoutColour colour).Reachable source sink) :
    ¬ network.toSimpleGraph.Adj source sink := by
  haveI : Nontrivial (Fin K) := Fin.nontrivial_iff_two_le.mpr colours_at_least_two
  intro adjacent
  rcases adjacent.2 with ⟨edge, tail_eq, head_eq⟩ | ⟨edge, tail_eq, head_eq⟩
  · obtain ⟨otherColour, colour_ne⟩ := exists_ne (network.color edge)
    apply distance_positive otherColour
    exact ⟨SimpleGraph.Walk.cons
      ⟨adjacent.1, Or.inl ⟨edge, colour_ne.symm, tail_eq, head_eq⟩⟩
      SimpleGraph.Walk.nil⟩
  · obtain ⟨otherColour, colour_ne⟩ := exists_ne (network.color edge)
    apply distance_positive otherColour
    exact ⟨SimpleGraph.Walk.cons
      ⟨adjacent.1, Or.inr ⟨edge, colour_ne.symm, tail_eq, head_eq⟩⟩
      SimpleGraph.Walk.nil⟩

/-- The reachable component after deleting a colour is a cut whose crossing
edges all have the deleted colour. -/
theorem colour_cut_of_not_reachable (source sink : network.V) (colour : Fin K)
    (disconnected : ¬ (network.withoutColour colour).Reachable source sink) :
    ∃ cut : Finset network.V, source ∈ cut ∧ sink ∉ cut ∧
      ∀ edge : network.E,
        (¬ (network.tail edge ∈ cut ↔ network.head edge ∈ cut)) →
          network.color edge = colour := by
  classical
  refine ⟨Finset.univ.filter ((network.withoutColour colour).Reachable source),
    by simp, by simpa using disconnected, ?_⟩
  intro edge crossing
  by_contra colour_ne
  have endpoints_distinct : network.tail edge ≠ network.head edge := by
    intro same
    exact crossing (by simp [same])
  have adjacent : (network.withoutColour colour).Adj (network.tail edge)
      (network.head edge) :=
    ⟨endpoints_distinct, Or.inl ⟨edge, colour_ne, rfl, rfl⟩⟩
  have forward : (network.withoutColour colour).Reachable (network.tail edge)
      (network.head edge) := ⟨SimpleGraph.Walk.cons adjacent SimpleGraph.Walk.nil⟩
  apply crossing
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun reachable => reachable.trans forward,
    fun reachable => reachable.trans forward.symm⟩

theorem cut_divergence (cut : Finset network.V) (current : network.E → ℝ) :
    ∑ vertex ∈ cut, network.div current vertex =
      ∑ edge : network.E,
        ((if network.tail edge ∈ cut then (1 : ℝ) else 0) -
          (if network.head edge ∈ cut then (1 : ℝ) else 0)) * current edge := by
  classical
  unfold Network.div
  rw [Finset.sum_sub_distrib, Finset.sum_comm (s := cut), Finset.sum_comm (s := cut)]
  simp [sub_mul, Finset.sum_sub_distrib, Finset.sum_ite, eq_comm]

/-- A monochromatic cut separating the terminals forces a positive lower bound
for the energy carried by edges of that colour. -/
theorem colour_energy_lower_bound (source sink : network.V)
    (flow : network.Flow source sink) (cut : Finset network.V)
    (source_mem : source ∈ cut) (sink_not_mem : sink ∉ cut) (colour : Fin K)
    (crossing_colour : ∀ edge : network.E,
      (¬ (network.tail edge ∈ cut ↔ network.head edge ∈ cut)) →
        network.color edge = colour) :
    1 / ((Fintype.card network.E : ℝ) + 1) ≤
      ∑ edge : network.E, if network.color edge = colour then (flow.1 edge) ^ 2 else 0 := by
  classical
  have total_transport :
      (∑ edge : network.E,
        ((if network.tail edge ∈ cut then (1 : ℝ) else 0) -
          (if network.head edge ∈ cut then (1 : ℝ) else 0)) * flow.1 edge) = 1 := by
    rw [← network.cut_divergence]
    have current_divergence := flow.property
    unfold Network.IsUnitFlow at current_divergence
    simp_rw [current_divergence]
    have terminals_distinct : source ≠ sink := by aesop
    rw [Finset.sum_eq_single source]
    · simp
    · intro vertex vertex_mem vertex_ne
      have vertex_ne_sink : vertex ≠ sink := by aesop
      simp [vertex_ne, vertex_ne_sink]
    · exact fun source_not_mem => (source_not_mem source_mem).elim
  have restricted_transport :
      (∑ edge : network.E,
        ((if network.tail edge ∈ cut then (1 : ℝ) else 0) -
          (if network.head edge ∈ cut then (1 : ℝ) else 0)) *
            (if network.color edge = colour then flow.1 edge else 0)) = 1 := by
    convert total_transport using 1
    apply Finset.sum_congr rfl
    intro edge _
    by_cases colour_eq : network.color edge = colour
    · simp [colour_eq]
    · have no_crossing : network.tail edge ∈ cut ↔ network.head edge ∈ cut := by
        by_contra crossing
        exact colour_eq (crossing_colour edge crossing)
      by_cases tail_mem : network.tail edge ∈ cut
      · have head_mem := no_crossing.mp tail_mem
        simp [tail_mem, head_mem]
      · have head_not_mem : network.head edge ∉ cut :=
          fun head_mem => tail_mem (no_crossing.mpr head_mem)
        simp [tail_mem, head_not_mem]
  have coefficient_bound :
      (∑ edge : network.E,
        ((if network.tail edge ∈ cut then (1 : ℝ) else 0) -
          (if network.head edge ∈ cut then (1 : ℝ) else 0)) ^ 2) ≤
        (Fintype.card network.E : ℝ) := by
    calc
      _ ≤ ∑ _edge : network.E, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro edge _
        split_ifs <;> norm_num
      _ = _ := by simp
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset network.E)
    (fun edge => (if network.tail edge ∈ cut then (1 : ℝ) else 0) -
      (if network.head edge ∈ cut then (1 : ℝ) else 0))
    (fun edge => if network.color edge = colour then flow.1 edge else 0)
  rw [restricted_transport] at cauchy
  have restricted_nonneg : 0 ≤
      ∑ edge : network.E, (if network.color edge = colour then flow.1 edge else 0) ^ 2 :=
    Finset.sum_nonneg fun edge _ => sq_nonneg _
  have unit_bound : 1 ≤ (Fintype.card network.E : ℝ) *
      ∑ edge : network.E, (if network.color edge = colour then flow.1 edge else 0) ^ 2 :=
    le_trans (by simpa using cauchy)
      (mul_le_mul_of_nonneg_right coefficient_bound restricted_nonneg)
  have squares_eq :
      (∑ edge : network.E, (if network.color edge = colour then flow.1 edge else 0) ^ 2) =
        ∑ edge : network.E, if network.color edge = colour then (flow.1 edge) ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro edge _
    split_ifs <;> simp
  rw [squares_eq] at unit_bound restricted_nonneg
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (Fintype.card network.E : ℝ) + 1)).2
  nlinarith

/-- The cut bound holds on the entire closed nonnegative orthant, including
resistance vectors with zero coordinates. -/
theorem effRes_colour_cut_lower_bound (source sink : network.V)
    (connected : Nonempty (network.Flow source sink)) (cut : Finset network.V)
    (source_mem : source ∈ cut) (sink_not_mem : sink ∉ cut) (colour : Fin K)
    (crossing_colour : ∀ edge : network.E,
      (¬ (network.tail edge ∈ cut ↔ network.head edge ∈ cut)) →
        network.color edge = colour)
    (resistances : Fin K → ℝ) (resistances_nonneg : 0 ≤ resistances) :
    resistances colour / ((Fintype.card network.E : ℝ) + 1) ≤
      network.effRes source sink connected resistances := by
  classical
  rw [network.effRes_eq_iInf]
  apply le_ciInf
  intro flow
  calc
    _ ≤ resistances colour *
        ∑ edge : network.E, if network.color edge = colour then (flow.1 edge) ^ 2 else 0 := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
        (network.colour_energy_lower_bound source sink flow cut source_mem sink_not_mem
          colour crossing_colour) (resistances_nonneg colour)
    _ ≤ network.energyNetwork flow.1 resistances := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro edge _
      by_cases colour_eq : network.color edge = colour
      · simp [colour_eq]
      · simp only [colour_eq, ↓reduceIte, mul_zero]
        exact mul_nonneg (resistances_nonneg _) (sq_nonneg _)

theorem effRes_pos_of_colour_cut (source sink : network.V)
    (connected : Nonempty (network.Flow source sink)) (cut : Finset network.V)
    (source_mem : source ∈ cut) (sink_not_mem : sink ∉ cut) (colour : Fin K)
    (crossing_colour : ∀ edge : network.E,
      (¬ (network.tail edge ∈ cut ↔ network.head edge ∈ cut)) →
        network.color edge = colour)
    (resistances : Fin K → ℝ) (resistances_nonneg : 0 ≤ resistances)
    (colour_positive : 0 < resistances colour) :
    0 < network.effRes source sink connected resistances := by
  exact lt_of_lt_of_le (by positivity)
    (network.effRes_colour_cut_lower_bound source sink connected cut source_mem
      sink_not_mem colour crossing_colour resistances resistances_nonneg)

/-- Distance positivity in its deleted-colour characterization gives strict
positivity at every nonzero vector in the closed nonnegative orthant. -/
theorem effRes_strongly_positive (source sink : network.V)
    (connected : Nonempty (network.Flow source sink))
    (distance_positive : ∀ colour : Fin K,
      ¬ (network.withoutColour colour).Reachable source sink)
    (resistances : Fin K → ℝ) (resistances_nonneg : 0 ≤ resistances)
    (resistances_nonzero : resistances ≠ 0) :
    0 < network.effRes source sink connected resistances := by
  obtain ⟨colour, colour_positive⟩ : ∃ colour : Fin K, 0 < resistances colour := by
    by_contra no_positive
    apply resistances_nonzero
    ext colour
    have nonpositive : resistances colour ≤ 0 :=
      le_of_not_gt (not_exists.mp no_positive colour)
    exact le_antisymm nonpositive (resistances_nonneg colour)
  obtain ⟨cut, source_mem, sink_not_mem, crossing_colour⟩ :=
    network.colour_cut_of_not_reachable source sink colour (distance_positive colour)
  exact network.effRes_pos_of_colour_cut source sink connected cut source_mem
    sink_not_mem colour crossing_colour resistances resistances_nonneg colour_positive

end EIGS.Network

namespace EIGS.RuleSystem

variable {K : ℕ}

/-- The resistance renormalisation map of distance-positive finite rules is
strongly positive, with the deleted-colour formulation used in the paper. -/
theorem renorm_strongly_positive (rules : EIGS.RuleSystem K)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((rules.R ruleColour).withoutColour edgeColour).Reachable
        (rules.βplus ruleColour) (rules.βminus ruleColour))
    (resistances : Fin K → ℝ) (resistances_nonneg : 0 ≤ resistances)
    (resistances_nonzero : resistances ≠ 0) :
    ∀ colour, 0 < rules.toRenormMap.apply resistances colour := by
  intro colour
  exact (rules.R colour).effRes_strongly_positive (rules.βplus colour)
    (rules.βminus colour) (rules.connected colour) (distance_positive colour)
    resistances resistances_nonneg resistances_nonzero

end EIGS.RuleSystem
