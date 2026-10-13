import RequestProject.Section2BoundaryCapacity
import RequestProject.Section2LocalBall
import RequestProject.Section2RandomWalk

/-! Exact finite exit time as resistance times voltage-weighted degree mass,
and the actual oriented-edge endpoint expression for that mass. -/

namespace EIGS

open scoped BigOperators Classical

variable {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]

theorem expExit_eq_resistance_mul_voltage_mass (graph : SimpleGraph Vertex)
    [DecidableRel graph.Adj] (connected : graph.Connected) {domain : Finset Vertex}
    (proper : domainᶜ.Nonempty) {source : Vertex} (source_inside : source ∈ domain) :
    expExit graph domain source = effResToBoundary graph domain source *
      ∑ vertex : Vertex, boundaryVoltageProfile graph domain source vertex * (graph.degree vertex : ℝ) := by
  rw [exit_eq_green_weighted graph connected proper (exitSystem_expExit connected proper) source_inside]
  have sum_restriction :
      (∑ vertex : Vertex, boundaryVoltageProfile graph domain source vertex * (graph.degree vertex : ℝ)) =
        ∑ vertex ∈ domain, boundaryVoltageProfile graph domain source vertex * (graph.degree vertex : ℝ) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro vertex _ vertex_outside
    rw [boundaryVoltageProfile_zero graph vertex_outside, zero_mul]
  rw [sum_restriction, Finset.mul_sum]
  conv_rhs => rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro vertex _
  rw [boundaryVoltageProfile, unitPotential_apply_mem graph source_inside vertex.property,
    green_symm graph domain vertex ⟨source, source_inside⟩]
  have resistance_ne_zero := ne_of_gt (effResToBoundary_pos graph connected proper source_inside)
  field_simp [resistance_ne_zero]

variable {K : ℕ}

theorem Network.voltage_degree_mass_eq_endpoint_sum (network : Network K)
    (loopless : network.Loopless) (unique_edges : network.EdgesUnique) (potential : network.V → ℝ) :
    (∑ vertex : network.V, potential vertex * (network.toSimpleGraph.degree vertex : ℝ)) =
      ∑ edge : network.E, (potential (network.tail edge) + potential (network.head edge)) := by
  classical
  simp_rw [network.degree_eq_incident_edge_sum loopless unique_edges, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro edge _
  simp_rw [mul_add, Finset.sum_add_distrib]
  have tail_sum : (∑ vertex : network.V,
      potential vertex * (if network.tail edge = vertex then (1 : ℝ) else 0)) =
      potential (network.tail edge) := by
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have head_sum : (∑ vertex : network.V,
      potential vertex * (if network.head edge = vertex then (1 : ℝ) else 0)) =
      potential (network.head edge) := by
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [tail_sum, head_sum]

end EIGS

#print axioms EIGS.expExit_eq_resistance_mul_voltage_mass
#print axioms EIGS.Network.voltage_degree_mass_eq_endpoint_sum
