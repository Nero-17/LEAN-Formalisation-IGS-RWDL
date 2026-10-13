import RequestProject.Section31.Oscillation

/-! A quantitative finite Euler estimate at a vertex adjacent to a unit-value
source. This lemma does not assume a Harnack or near-diagonal inequality. -/

namespace IGS.Sec31.FiniteNetwork

open scoped BigOperators Classical

variable {Vertex : Type*} [DecidableEq Vertex]

theorem source_neighbor_voltage_lower (network : FiniteNetwork Vertex)
    (potential : Vertex → ℝ) (potential_nonnegative : ∀ vertex, 0 ≤ potential vertex)
    (source vertex : Vertex) (source_ne_vertex : source ≠ vertex)
    (source_value : potential source = 1) (harmonic : network.grad potential vertex = 0)
    (source_edge : network.Edge)
    (source_edge_ends :
      ((network.ends source_edge).1 = source ∧ (network.ends source_edge).2 = vertex) ∨
      ((network.ends source_edge).1 = vertex ∧ (network.ends source_edge).2 = source)) :
    network.cond source_edge / (2 * ∑ edge : network.Edge, network.cond edge) ≤ potential vertex := by
  classical
  have conductance_sum_positive : 0 < ∑ edge : network.Edge, network.cond edge :=
    (network.cond_pos source_edge).trans_le (Finset.single_le_sum
      (fun edge _ => (network.cond_pos edge).le) (Finset.mem_univ source_edge))
  have vertex_product_nonnegative : ∀ edge, 0 ≤ network.cond edge * potential vertex :=
    fun edge => mul_nonneg (network.cond_pos edge).le (potential_nonnegative vertex)
  have edge_bound : ∀ edge : network.Edge,
      network.cond edge * network.inc edge vertex *
          (potential (network.ends edge).1 - potential (network.ends edge).2) ≤
        2 * network.cond edge * potential vertex -
          (if edge = source_edge then network.cond source_edge else 0) := by
    intro edge
    by_cases selected : edge = source_edge
    · subst edge
      rcases source_edge_ends with ⟨tail_source, head_vertex⟩ | ⟨tail_vertex, head_source⟩
      · simp only [inc, tail_source, head_vertex, if_neg source_ne_vertex, if_pos rfl,
          source_value, zero_sub, ↓reduceIte]
        nlinarith [vertex_product_nonnegative source_edge]
      · simp only [inc, tail_vertex, head_source, if_neg source_ne_vertex, if_pos rfl,
          source_value, sub_zero, ↓reduceIte]
        nlinarith [vertex_product_nonnegative source_edge]
    · simp only [if_neg selected, sub_zero]
      by_cases tail_vertex : (network.ends edge).1 = vertex <;>
        by_cases head_vertex : (network.ends edge).2 = vertex
      · simp only [inc, tail_vertex, head_vertex, ↓reduceIte, sub_self, mul_zero, zero_mul]
        nlinarith [vertex_product_nonnegative edge]
      · have opposite_nonnegative := mul_nonneg (network.cond_pos edge).le
          (potential_nonnegative (network.ends edge).2)
        simp only [inc, tail_vertex, head_vertex, ↓reduceIte, sub_zero, mul_one]
        nlinarith [vertex_product_nonnegative edge]
      · have opposite_nonnegative := mul_nonneg (network.cond_pos edge).le
          (potential_nonnegative (network.ends edge).1)
        simp only [inc, tail_vertex, head_vertex, ↓reduceIte, zero_sub]
        nlinarith [vertex_product_nonnegative edge]
      · simp only [inc, tail_vertex, head_vertex, ↓reduceIte, sub_self, mul_zero, zero_mul]
        nlinarith [vertex_product_nonnegative edge]
  have summed_bound := Finset.sum_le_sum (fun edge (_ : edge ∈ (Finset.univ : Finset network.Edge)) => edge_bound edge)
  have sum_identity :
      (∑ edge : network.Edge, (2 * network.cond edge * potential vertex -
        (if edge = source_edge then network.cond source_edge else 0))) =
      2 * (∑ edge : network.Edge, network.cond edge) * potential vertex - network.cond source_edge := by
    rw [Finset.sum_sub_distrib]
    simp only [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← grad, harmonic, sum_identity] at summed_bound
  apply (div_le_iff₀ (mul_pos (by norm_num) conductance_sum_positive)).mpr
  nlinarith

end IGS.Sec31.FiniteNetwork

#print axioms IGS.Sec31.FiniteNetwork.source_neighbor_voltage_lower
