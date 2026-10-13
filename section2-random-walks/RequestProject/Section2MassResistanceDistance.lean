import RequestProject.Section31.DirichletThomson
import RequestProject.Section2WeightedMetric

/-! The distance--mass--resistance inequality on the unchanged finite network.
It follows from the actual distance potential and Kirchhoff's flow equation;
no commute-time or geometric lower bound is supplied as a hypothesis. -/

namespace EIGS.Network

open scoped BigOperators
open IGS.Sec31

variable {K : ℕ} (network : Network K)

theorem distance_sq_le_edge_card_mul_flow_energy
    (connected : network.toSimpleGraph.Connected)
    (source sink : network.V) (distinct : source ≠ sink)
    (current : network.Flow source sink) :
    network.weightedDistance (fun _ => 1) source sink ^ 2 ≤
      (Fintype.card network.E : ℝ) * network.energyNetwork current.val (fun _ => 1) := by
  let potential := network.weightedDistance (fun _ => (1 : ℝ)) source
  have lipschitz := network.weightedDistance_edgeLipschitz connected (fun _ => zero_le_one) source
  have potentialEnergyBound :
      (network.potentialNetwork (fun _ => 1) (fun _ => zero_lt_one)).energy potential ≤
        (Fintype.card network.E : ℝ) := by
    calc
      _ = ∑ edge : network.E, (potential (network.tail edge) - potential (network.head edge)) ^ 2 := by
        simp only [potentialNetwork, FiniteNetwork.energy, inv_one, one_mul]
      _ ≤ ∑ _edge : network.E, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro edge _
        have bound := lipschitz edge
        have absoluteNonnegative := abs_nonneg
          (potential (network.tail edge) - potential (network.head edge))
        have squareAbsolute := sq_abs (potential (network.tail edge) - potential (network.head edge))
        nlinarith
      _ = _ := by simp
  have flowEnergyNonnegative : 0 ≤ network.energyNetwork current.val (fun _ => 1) := by
    exact Finset.sum_nonneg (fun edge _ => mul_nonneg zero_le_one (sq_nonneg _))
  have cauchy := network.potential_difference_sq_le_flow_energy_mul_potential_energy
    (fun _ => 1) (fun _ => zero_lt_one) source sink distinct current potential
  simp only [potential, network.weightedDistance_self (fun _ => zero_le_one), zero_sub, neg_sq] at cauchy
  exact cauchy.trans (by nlinarith [mul_le_mul_of_nonneg_left potentialEnergyBound flowEnergyNonnegative])

theorem distance_sq_le_edge_card_mul_effRes
    (connected : network.toSimpleGraph.Connected)
    (source sink : network.V) (distinct : source ≠ sink)
    (flowExists : Nonempty (network.Flow source sink)) :
    network.weightedDistance (fun _ => 1) source sink ^ 2 ≤
      (Fintype.card network.E : ℝ) * network.effRes source sink flowExists (fun _ => 1) := by
  have edgeCardPositive : 0 < (Fintype.card network.E : ℝ) := by
    by_contra notPositive
    have cardZero : Fintype.card network.E = 0 := by
      exact_mod_cast le_antisymm (not_lt.mp notPositive) (Nat.cast_nonneg _ : (0 : ℝ) ≤ _)
    letI : IsEmpty network.E := Fintype.card_eq_zero_iff.mp cardZero
    obtain ⟨current⟩ := flowExists
    have sourceEquation := current.property source
    simp [Network.IsUnitFlow, Network.div] at sourceEquation
  have lowerBound :
      network.weightedDistance (fun _ => 1) source sink ^ 2 / (Fintype.card network.E : ℝ) ≤
        network.effRes source sink flowExists (fun _ => 1) := by
    rw [network.effRes_eq_iInf]
    apply le_ciInf
    intro current
    apply (div_le_iff₀ edgeCardPositive).mpr
    simpa only [mul_comm] using
      network.distance_sq_le_edge_card_mul_flow_energy connected source sink distinct current
  simpa only [mul_comm] using (div_le_iff₀ edgeCardPositive).mp lowerBound

end EIGS.Network

#print axioms EIGS.Network.distance_sq_le_edge_card_mul_flow_energy
#print axioms EIGS.Network.distance_sq_le_edge_card_mul_effRes
