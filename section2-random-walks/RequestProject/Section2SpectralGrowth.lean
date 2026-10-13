import RequestProject.Section2FiniteSpectralRadius
import RequestProject.Section2MassGrowth
import RequestProject.Section2LocalBall

/-! Actual mass and degree growth with the usual complex spectral radii of the
actual matrices. The primitive degree eigenpair is constructed from the original
assumption. -/

namespace EIGS

open scoped BigOperators Classical

variable {K : ℕ}

theorem eigs_mass_spectral_growth (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    0 < realMatrixSpectralRadius (massMatrixR system.toRuleData) ∧
      ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ level,
        lower * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ level ≤
          (totalEdges system.toRuleData level : ℝ) ∧
        (totalEdges system.toRuleData level : ℝ) ≤
          upper * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ level := by
  obtain ⟨vector, vector_positive, rate_positive, _, eigenpair⟩ :=
    positive_matrix_spectralRadius_eigenpair
      (lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt)
      (massMatrixR system.toRuleData) (massMatrixR_positive system rule_connected distance_positive)
  exact ⟨rate_positive, mass_geometric_growth system vector_positive eigenpair rate_positive⟩

theorem degree_spectral_growth_from_primitive_rules (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (primitive_degree : (degreeMatrix system).IsPrimitive) :
    0 < finiteRealMatrixSpectralRadius (degreeMatrix system) ∧
      ∀ initial_level (vertex : XiVtx system initial_level),
        ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ steps,
          lower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ steps ≤
            ∑ state, degVec system (initial_level + steps)
              (xiForward system initial_level steps vertex) state ∧
          (∑ state, degVec system (initial_level + steps)
            (xiForward system initial_level steps vertex) state) ≤
              upper * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ steps := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  obtain ⟨vector, vector_positive, rate_positive, _, eigenpair⟩ :=
    primitive_matrix_spectralRadius_eigenpair_finite (degreeMatrix system) primitive_degree
  refine ⟨rate_positive, fun initial_level vertex => ?_⟩
  exact degree_geometric_growth_proved system initial_level vertex vector_positive eigenpair
    rate_positive (degVec_weighted_positive system rule_connected initial_level vertex vector
      vector_positive)

theorem xiSimpleGraph_small_ball_spectral_growth (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (primitive_degree : (degreeMatrix system).IsPrimitive) :
    0 < finiteRealMatrixSpectralRadius (degreeMatrix system) ∧
      ∀ initial_level (vertex : XiVtx system initial_level),
        ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ steps (radius : ℝ),
          1 < radius → radius ≤ 2 →
          lower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ steps ≤
            ((finiteGraphBall (XiSimpleGraph system (initial_level + steps))
              (xiForward system initial_level steps vertex) radius).card : ℝ) ∧
          ((finiteGraphBall (XiSimpleGraph system (initial_level + steps))
            (xiForward system initial_level steps vertex) radius).card : ℝ) ≤
              upper * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ steps := by
  obtain ⟨rate_positive, degree_growth⟩ :=
    degree_spectral_growth_from_primitive_rules system rule_connected primitive_degree
  refine ⟨rate_positive, fun initial_level vertex => ?_⟩
  obtain ⟨lower, upper, lower_positive, upper_positive, bounds⟩ := degree_growth initial_level vertex
  refine ⟨lower, 2 * upper, lower_positive, by positivity,
    fun steps radius radius_gt_one radius_le_two => ?_⟩
  let center := xiForward system initial_level steps vertex
  let graph := XiSimpleGraph system (initial_level + steps)
  have connected : graph.Connected := xiSimpleGraph_connected system rule_connected _
  letI : Nontrivial (XiVtx system (initial_level + steps)) :=
    ⟨⟨xiPositiveTerminal system _, xiNegativeTerminal system _, xiTerminals_distinct system _⟩⟩
  obtain ⟨neighbor, adjacent⟩ := connected.preconnected.exists_adj_of_nontrivial center
  have degree_at_least_one : (1 : ℝ) ≤ graph.degree center := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt ((graph.degree_pos_iff_exists_adj center).mpr ⟨neighbor, adjacent⟩)))
  rw [finiteGraphBall_card_eq_degree_add_one graph connected center radius_gt_one radius_le_two,
    Nat.cast_add, Nat.cast_one]
  have degree_bounds := bounds steps
  rw [← xiSimpleGraph_degree_eq_degree_state_sum system rule_connected rules_loopless
    rules_unique planting_nonadjacent] at degree_bounds
  constructor <;> nlinarith [degree_bounds.1, degree_bounds.2]

end EIGS

#print axioms EIGS.eigs_mass_spectral_growth
#print axioms EIGS.degree_spectral_growth_from_primitive_rules
#print axioms EIGS.xiSimpleGraph_small_ball_spectral_growth
