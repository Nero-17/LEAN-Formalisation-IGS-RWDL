import RequestProject.Section2RandomWalk

/-! A finite-time survival lower bound from the actual exit-time tail sum.
The proof uses the actual transition recursion, without a stopping-time or
strong Markov hypothesis. Identification with an infinite-path event is separate. -/

namespace EIGS

open scoped BigOperators

variable {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
variable (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]

theorem expExit_le_time_add_upper_mul_survival
    (connected : graph.Connected) {domain : Finset Vertex}
    (proper : domainᶜ.Nonempty) (upper : ℝ)
    (upper_bound : ∀ vertex, expExit graph domain vertex ≤ upper)
    (time : ℕ) (vertex : Vertex) :
    expExit graph domain vertex ≤ (time : ℝ) + upper * surv graph domain time vertex := by
  induction time generalizing vertex with
  | zero =>
      by_cases inside : vertex ∈ domain
      · simpa [surv, inside] using upper_bound vertex
      · simp [expExit_zero_of_notMem inside, surv, inside]
  | succ time inductionHypothesis =>
      by_cases inside : vertex ∈ domain
      · rw [expExit_recurrence connected proper inside]
        have averaged := Finset.sum_le_sum (fun neighbour (_ : neighbour ∈ Finset.univ) =>
          mul_le_mul_of_nonneg_left (inductionHypothesis neighbour)
            (transProb_nonneg (G := graph) vertex neighbour))
        have row_sum := transProb_sum (G := graph) (degree_pos_of_mem connected proper inside)
        have expanded :
            (∑ neighbour, transProb graph vertex neighbour *
              ((time : ℝ) + upper * surv graph domain time neighbour)) =
            (time : ℝ) + upper * ∑ neighbour,
              transProb graph vertex neighbour * surv graph domain time neighbour := by
          simp only [mul_add, Finset.sum_add_distrib]
          rw [← Finset.sum_mul, row_sum, one_mul]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro neighbour _
          ring
        rw [expanded] at averaged
        simp only [surv, if_pos inside, Nat.cast_add, Nat.cast_one]
        linarith
      · simp only [expExit_zero_of_notMem inside, surv_zero_of_notMem inside,
          mul_zero, add_zero]
        positivity

theorem survival_lower_of_exit_bounds
    (connected : graph.Connected) {domain : Finset Vertex}
    (proper : domainᶜ.Nonempty) (upper : ℝ) (upper_positive : 0 < upper)
    (upper_bound : ∀ vertex, expExit graph domain vertex ≤ upper)
    (time : ℕ) (vertex : Vertex) :
    (expExit graph domain vertex - (time : ℝ)) / upper ≤
      surv graph domain time vertex := by
  apply (div_le_iff₀ upper_positive).mpr
  have bound := expExit_le_time_add_upper_mul_survival graph connected proper
    upper upper_bound time vertex
  nlinarith

theorem survival_uniform_positive_of_exit_bounds
    (connected : graph.Connected) {domain : Finset Vertex}
    (proper : domainᶜ.Nonempty) (lower upper scale : ℝ)
    (upper_positive : 0 < upper) (scale_positive : 0 < scale)
    (upper_bound : ∀ vertex, expExit graph domain vertex ≤ upper * scale)
    (time : ℕ) (vertex : Vertex)
    (lower_bound : lower * scale ≤ expExit graph domain vertex)
    (time_bound : (time : ℝ) ≤ lower * scale / 2) :
    lower / (2 * upper) ≤ surv graph domain time vertex := by
  have bound := expExit_le_time_add_upper_mul_survival graph connected proper
    (upper * scale) upper_bound time vertex
  apply (div_le_iff₀ (by positivity : 0 < 2 * upper)).mpr
  nlinarith

end EIGS

#print axioms EIGS.expExit_le_time_add_upper_mul_survival
#print axioms EIGS.survival_lower_of_exit_bounds
#print axioms EIGS.survival_uniform_positive_of_exit_bounds
