import RequestProject.Section2Concrete
import RequestProject.Section2FinitePerron

namespace EIGS

open scoped BigOperators Classical

variable {K : ℕ}

theorem xiTerminals_distinct (system : EIGSData K) (level : ℕ) :
    xiPositiveTerminal system level ≠ xiNegativeTerminal system level := by
  induction level with
  | zero => exact Bool.false_ne_true
  | succ level induction => exact fun equal => induction (Sum.inl.inj equal)

/-- Every actual vertex has a positive weighted incident degree whenever the
original rule graphs are connected and the weights are positive. -/
theorem degVec_weighted_positive (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (level : ℕ) (vertex : XiVtx system level)
    (weights : Fin K ⊕ Fin K → ℝ) (weights_positive : ∀ state, 0 < weights state) :
    0 < ∑ state, degVec system level vertex state * weights state := by
  letI : Nontrivial (XiVtx system level) :=
    ⟨⟨xiPositiveTerminal system level, xiNegativeTerminal system level,
      xiTerminals_distinct system level⟩⟩
  obtain ⟨neighbor, adjacency⟩ :=
    (xiSimpleGraph_connected system rule_connected level).preconnected.exists_adj_of_nontrivial vertex
  have incident : ∃ state, 0 < degVec system level vertex state := by
    rcases adjacency with ⟨distinct, forward | reverse⟩
    · obtain ⟨edge, tail_eq, head_eq⟩ := forward
      refine ⟨Sum.inl (XiCol system.toRuleData level edge), ?_⟩
      change 0 < (outDeg system level vertex (XiCol system.toRuleData level edge) : ℝ)
      apply Nat.cast_pos.mpr
      exact Finset.card_pos.mpr ⟨edge, by simp [outDeg, tail_eq]⟩
    · obtain ⟨edge, tail_eq, head_eq⟩ := reverse
      refine ⟨Sum.inr (XiCol system.toRuleData level edge), ?_⟩
      change 0 < (inDeg system level vertex (XiCol system.toRuleData level edge) : ℝ)
      apply Nat.cast_pos.mpr
      exact Finset.card_pos.mpr ⟨edge, by simp [inDeg, head_eq]⟩
  obtain ⟨state, degree_positive⟩ := incident
  apply Finset.sum_pos'
  · intro state _
    apply mul_nonneg _ (weights_positive state).le
    cases state <;> exact Nat.cast_nonneg _
  · exact ⟨state, Finset.mem_univ _, mul_pos degree_positive (weights_positive state)⟩

/-- Degree growth from the paper's primitive degree-matrix assumption, with the
Perron eigenpair and the nonzero initial degree both proved. -/
theorem degree_growth_from_primitive_rules (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (primitive_degree : (degreeMatrix system).IsPrimitive) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ initial_level (vertex : XiVtx system initial_level),
      ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ steps,
        lower * rate ^ steps ≤ ∑ state,
          degVec system (initial_level + steps) (xiForward system initial_level steps vertex) state ∧
        (∑ state, degVec system (initial_level + steps)
          (xiForward system initial_level steps vertex) state) ≤ upper * rate ^ steps := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  obtain ⟨vector, rate, vector_positive, rate_positive, normalized, eigenpair⟩ :=
    primitive_matrix_eigenpair_finite (degreeMatrix system) primitive_degree
  refine ⟨rate, rate_positive, fun initial_level vertex => ?_⟩
  exact degree_geometric_growth_proved system initial_level vertex vector_positive eigenpair
    rate_positive (degVec_weighted_positive system rule_connected initial_level vertex vector
      vector_positive)

end EIGS
