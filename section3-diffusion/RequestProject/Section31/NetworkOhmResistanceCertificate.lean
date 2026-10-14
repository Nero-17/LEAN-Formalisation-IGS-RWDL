import RequestProject.Section31.DirichletThomson

/-! A unit-current potential on the actual oriented edge set certifies
the Thomson resistance. Optimality is proved by expanding the actual sum
of nonnegative squared current differences. Candidate source. -/

namespace EIGS.Network
open scoped BigOperators
noncomputable section
variable {K : ℕ}

theorem effRes_eq_energy_of_unitFlow_ohm
    (network : Network K) (source sink : network.V) (sourceNeSink : source ≠ sink)
    (connected : Nonempty (network.Flow source sink))
    (resistances : Fin K → ℝ) (positive : ∀ colour, 0 < resistances colour)
    (current : network.Flow source sink) (potential : network.V → ℝ)
    (ohm : ∀ edge, resistances (network.color edge) * current.val edge =
      potential (network.tail edge) - potential (network.head edge)) :
    network.effRes source sink connected resistances = network.energyNetwork current.val resistances := by
  have lowerBounded : BddBelow (Set.range (fun other : network.Flow source sink =>
      network.energyNetwork other.val resistances)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨other, rfl⟩
    exact Finset.sum_nonneg (fun edge _ => mul_nonneg (positive _).le (sq_nonneg _))
  rw [network.effRes_eq_iInf]
  apply le_antisymm
  · exact ciInf_le lowerBounded current
  · apply le_ciInf
    intro other
    have pairing : (∑ edge, resistances (network.color edge) * other.val edge * current.val edge) =
        network.energyNetwork current.val resistances := by
      calc
        _ = ∑ edge, other.val edge * (potential (network.tail edge) - potential (network.head edge)) := by
          apply Finset.sum_congr rfl
          intro edge _
          rw [← ohm]
          ring
        _ = potential source - potential sink :=
          network.sum_current_mul_potential_difference_of_unitFlow source sink sourceNeSink other potential
        _ = ∑ edge, current.val edge * (potential (network.tail edge) - potential (network.head edge)) :=
          (network.sum_current_mul_potential_difference_of_unitFlow source sink sourceNeSink current potential).symm
        _ = network.energyNetwork current.val resistances := by
          unfold energyNetwork
          apply Finset.sum_congr rfl
          intro edge _
          rw [← ohm]
          ring
    have nonnegative : 0 ≤ ∑ edge, resistances (network.color edge) * (other.val edge - current.val edge) ^ 2 :=
      Finset.sum_nonneg (fun edge _ => mul_nonneg (positive _).le (sq_nonneg _))
    have expansion : (∑ edge, resistances (network.color edge) * (other.val edge - current.val edge) ^ 2) =
        network.energyNetwork other.val resistances + network.energyNetwork current.val resistances -
          2 * (∑ edge, resistances (network.color edge) * other.val edge * current.val edge) := by
      simp only [energyNetwork, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro edge _
      ring
    rw [pairing] at expansion
    linarith

end
end EIGS.Network

#print axioms EIGS.Network.effRes_eq_energy_of_unitFlow_ohm
