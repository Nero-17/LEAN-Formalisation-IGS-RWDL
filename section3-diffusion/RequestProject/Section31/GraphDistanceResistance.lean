import RequestProject.Section31.DirichletThomson
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! The actual finite-network distance--mass--resistance inequality.

The graph distance potential is one-Lipschitz on every edge. Its energy is
therefore at most the number of oriented electrical edge identities. Discrete
Green and Cauchy--Schwarz then give d² ≤ |E| R, directly for the actual Thomson
resistance; no asymptotic exponent inequality is assumed.
-/

namespace EIGS.Network

open scoped BigOperators

variable {K : ℕ} (network : Network K)

theorem graphDistance_potential_edge_bound (source : network.V) (edge : network.E) :
    ((network.toSimpleGraph.dist source (network.tail edge) : ℝ) -
      (network.toSimpleGraph.dist source (network.head edge) : ℝ)) ^ 2 ≤ 1 := by
  by_cases same : network.tail edge = network.head edge
  · simp [same]
  · have adjacent : network.toSimpleGraph.Adj (network.tail edge) (network.head edge) :=
      ⟨same, Or.inl ⟨edge, rfl, rfl⟩⟩
    have forward : network.toSimpleGraph.dist source (network.head edge) ≤
        network.toSimpleGraph.dist source (network.tail edge) + 1 := by
      simpa only [SimpleGraph.dist_eq_one_iff_adj.mpr adjacent] using
        adjacent.reachable.dist_triangle_right source
    have backward : network.toSimpleGraph.dist source (network.tail edge) ≤
        network.toSimpleGraph.dist source (network.head edge) + 1 := by
      simpa only [SimpleGraph.dist_eq_one_iff_adj.mpr adjacent.symm] using
        adjacent.symm.reachable.dist_triangle_right source
    have forward_real : (network.toSimpleGraph.dist source (network.head edge) : ℝ) ≤
        (network.toSimpleGraph.dist source (network.tail edge) : ℝ) + 1 := by exact_mod_cast forward
    have backward_real : (network.toSimpleGraph.dist source (network.tail edge) : ℝ) ≤
        (network.toSimpleGraph.dist source (network.head edge) : ℝ) + 1 := by exact_mod_cast backward
    have absolute_bound : |(network.toSimpleGraph.dist source (network.tail edge) : ℝ) -
        (network.toSimpleGraph.dist source (network.head edge) : ℝ)| ≤ 1 := by
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) absolute_bound 2

theorem graphDistance_potential_energy_le_mass (source : network.V) :
    (network.potentialNetwork (fun _ => 1) (fun _ => zero_lt_one)).energy
      (fun vertex => (network.toSimpleGraph.dist source vertex : ℝ)) ≤
        (Fintype.card network.E : ℝ) := by
  calc
    (network.potentialNetwork (fun _ => 1) (fun _ => zero_lt_one)).energy
        (fun vertex => (network.toSimpleGraph.dist source vertex : ℝ)) =
      ∑ edge : network.E, ((network.toSimpleGraph.dist source (network.tail edge) : ℝ) -
        (network.toSimpleGraph.dist source (network.head edge) : ℝ)) ^ 2 := by
          simp only [potentialNetwork, IGS.Sec31.FiniteNetwork.energy, inv_one, one_mul]
    _ ≤ ∑ _edge : network.E, (1 : ℝ) :=
      Finset.sum_le_sum (fun edge _ => network.graphDistance_potential_edge_bound source edge)
    _ = (Fintype.card network.E : ℝ) := by simp

theorem graphDistance_sq_le_mass_mul_flow_energy
    (source sink : network.V) (terminals_distinct : source ≠ sink)
    (current : network.Flow source sink) :
    (network.toSimpleGraph.dist source sink : ℝ) ^ 2 ≤
      (Fintype.card network.E : ℝ) * network.energyNetwork current.val (fun _ => 1) := by
  have cauchy := network.potential_difference_sq_le_flow_energy_mul_potential_energy
    (fun _ => 1) (fun _ => zero_lt_one) source sink terminals_distinct current
    (fun vertex => (network.toSimpleGraph.dist source vertex : ℝ))
  have energy_nonnegative : 0 ≤ network.energyNetwork current.val (fun _ => 1) := by
    exact Finset.sum_nonneg (fun edge _ => by simp only [one_mul]; exact sq_nonneg _)
  have bound := mul_le_mul_of_nonneg_left
    (network.graphDistance_potential_energy_le_mass source) energy_nonnegative
  simpa only [SimpleGraph.dist_self, Nat.cast_zero, zero_sub, neg_sq, mul_comm] using
    cauchy.trans bound

theorem graphDistance_sq_le_mass_mul_effRes
    (source sink : network.V) (terminals_distinct : source ≠ sink)
    (connected : Nonempty (network.Flow source sink)) :
    (network.toSimpleGraph.dist source sink : ℝ) ^ 2 ≤
      (Fintype.card network.E : ℝ) * network.effRes source sink connected (fun _ => 1) := by
  rw [network.effRes_eq_iInf, Real.mul_iInf_of_nonneg (Nat.cast_nonneg _)]
  exact le_ciInf (fun current =>
    network.graphDistance_sq_le_mass_mul_flow_energy source sink terminals_distinct current)

end EIGS.Network
