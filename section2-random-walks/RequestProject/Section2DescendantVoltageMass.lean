import RequestProject.Section31.EIGSNonstationaryHarmonics
import RequestProject.Section31.EIGSEdgeDescendants

/-! Actual descendant edge mass on cells whose coarse endpoint voltages have
a positive lower bound. The fine voltages are the constructed nonstationary
minimum-energy extension for arbitrary positive fine resistances. -/

namespace EIGS

open scoped BigOperators Classical

variable {K : ℕ}

theorem xiAncestorEdge_eq_xiEdgeAncestor (system : EIGSData K) (initial depth : ℕ)
    (edge : XiEdge system.toRuleData (initial + depth)) :
    xiAncestorEdge system initial depth edge = xiEdgeAncestor system initial depth edge := by
  induction depth with
  | zero => rfl
  | succ depth induction_hypothesis => exact induction_hypothesis edge.1

theorem xiPotentialValues_descendant_voltage_mass_lower (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (initial depth : ℕ) (initial_values : XiVtx system initial → ℝ)
    (initial_nonnegative : ∀ vertex, 0 ≤ initial_values vertex)
    (resistances : Fin K → ℝ) (resistances_positive : ∀ colour, 0 < resistances colour)
    (selected : Finset (XiEdge system.toRuleData initial)) (lower : ℝ)
    (selected_lower : ∀ edge ∈ selected,
      lower ≤ initial_values (XiTail system initial edge) ∧
        lower ≤ initial_values (XiHead system initial edge)) :
    (∑ ancestor ∈ selected, 2 * lower *
      (totalEdges {system.toRuleData with ι := XiCol system.toRuleData initial ancestor} depth : ℝ)) ≤
      ∑ edge : XiEdge system.toRuleData (initial + depth),
        (xiPotentialValues system rule_connected initial depth resistances resistances_positive initial_values
            (XiTail system (initial + depth) edge) +
          xiPotentialValues system rule_connected initial depth resistances resistances_positive initial_values
            (XiHead system (initial + depth) edge)) := by
  have fine_lower : ∀ edge : XiEdge system.toRuleData (initial + depth),
      (if xiEdgeAncestor system initial depth edge ∈ selected then 2 * lower else 0) ≤
        xiPotentialValues system rule_connected initial depth resistances resistances_positive initial_values
            (XiTail system (initial + depth) edge) +
          xiPotentialValues system rule_connected initial depth resistances resistances_positive initial_values
            (XiHead system (initial + depth) edge) := by
    intro edge
    have endpoint_range := xiPotentialValues_descendant_endpoint_range system rule_connected initial initial_values
      depth resistances resistances_positive edge
    simp only [xiAncestorEdge_eq_xiEdgeAncestor] at endpoint_range
    by_cases selected_ancestor : xiEdgeAncestor system initial depth edge ∈ selected
    · rw [if_pos selected_ancestor]
      have coarse_lower := selected_lower _ selected_ancestor
      have minimum_lower := le_min coarse_lower.1 coarse_lower.2
      linarith [minimum_lower.trans endpoint_range.1.1, minimum_lower.trans endpoint_range.2.1]
    · rw [if_neg selected_ancestor]
      have minimum_nonnegative := le_min
        (initial_nonnegative (XiTail system initial (xiEdgeAncestor system initial depth edge)))
        (initial_nonnegative (XiHead system initial (xiEdgeAncestor system initial depth edge)))
      exact add_nonneg (minimum_nonnegative.trans endpoint_range.1.1)
        (minimum_nonnegative.trans endpoint_range.2.1)
  have sum_identity :
      (∑ edge : XiEdge system.toRuleData (initial + depth),
        if xiEdgeAncestor system initial depth edge ∈ selected then 2 * lower else 0) =
      ∑ ancestor ∈ selected, 2 * lower *
        (totalEdges {system.toRuleData with ι := XiCol system.toRuleData initial ancestor} depth : ℝ) := by
    calc
      _ = ∑ edge : XiEdge system.toRuleData (initial + depth),
          ∑ ancestor ∈ selected,
            if xiEdgeAncestor system initial depth edge = ancestor then (2 * lower : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro edge _
        simp
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro ancestor _
        simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, totalEdges, mul_comm] using
          xiDescendant_weight_sum system initial depth ancestor (fun _ => (2 * lower : ℝ))
  rw [← sum_identity]
  exact Finset.sum_le_sum (fun edge _ => fine_lower edge)

end EIGS

#print axioms EIGS.xiAncestorEdge_eq_xiEdgeAncestor
#print axioms EIGS.xiPotentialValues_descendant_voltage_mass_lower
