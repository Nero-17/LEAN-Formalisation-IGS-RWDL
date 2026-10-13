import RequestProject.Section2PathMetric

/-! Lower bounds for the distance scale from actual rule path lengths. -/

namespace EIGS.RuleSystem

open scoped BigOperators

variable {K : ℕ} (rules : EIGS.RuleSystem K)

theorem pathRenormMap_unit_ge_colours
    (reachable : ∀ colour, (rules.R colour).toSimpleGraph.Reachable
      (rules.βplus colour) (rules.βminus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ∀ path : (rules.R ruleColour).toSimpleGraph.Walk
        (rules.βplus ruleColour) (rules.βminus ruleColour),
          path.IsPath → (rules.R ruleColour).UsesColour path edgeColour)
    (colour : Fin K) :
    (K : ℝ) ≤ (rules.pathRenormMap reachable).apply (fun _ => 1) colour := by
  apply le_ciInf
  intro path
  have counts_bound := Finset.sum_le_sum (s := Finset.univ)
    (fun edgeColour _ => (rules.R colour).one_le_pathColourCount_of_usesColour path
      edgeColour (distance_positive colour edgeColour path.val path.property))
  simpa only [pathRenormMap, Network.pathThomsonData, ThomsonData.energy, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using counts_bound

theorem path_eigenvalue_ge_colours
    (colours_positive : 0 < K)
    (reachable : ∀ colour, (rules.R colour).toSimpleGraph.Reachable
      (rules.βplus colour) (rules.βminus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ∀ path : (rules.R ruleColour).toSimpleGraph.Walk
        (rules.βplus ruleColour) (rules.βminus ruleColour),
          path.IsPath → (rules.R ruleColour).UsesColour path edgeColour)
    (vector : Fin K → ℝ) (rate : ℝ) (vector_positive : ∀ colour, 0 < vector colour)
    (eigenpair : (rules.pathRenormMap reachable).apply vector = rate • vector) :
    (K : ℝ) ≤ rate := by
  apply (rules.pathRenormMap reachable).subvalue_le_supervalue colours_positive
    (fun _ => 1) vector (K : ℝ) rate (fun _ => zero_lt_one) vector_positive
      (fun colour => by simpa only [Pi.smul_apply, smul_eq_mul, mul_one] using
        rules.pathRenormMap_unit_ge_colours reachable distance_positive colour)
  exact eigenpair.le

theorem path_eigenvalue_ge_rule_distance_bound
    (colours_positive : 0 < K)
    (reachable : ∀ colour, (rules.R colour).toSimpleGraph.Reachable
      (rules.βplus colour) (rules.βminus colour))
    (unique_edges : ∀ colour, (rules.R colour).EdgesUnique)
    (distance_bound : ℝ) (rule_distances : ∀ colour,
      distance_bound ≤ ((rules.R colour).toSimpleGraph.dist
        (rules.βplus colour) (rules.βminus colour) : ℝ))
    (vector : Fin K → ℝ) (rate : ℝ) (vector_positive : ∀ colour, 0 < vector colour)
    (eigenpair : (rules.pathRenormMap reachable).apply vector = rate • vector) :
    distance_bound ≤ rate := by
  apply (rules.pathRenormMap reachable).subvalue_le_supervalue colours_positive
    (fun _ => 1) vector distance_bound rate (fun _ => zero_lt_one) vector_positive
  · rw [rules.pathRenormMap_unit_eq_graphDistances reachable unique_edges]
    intro colour
    simpa only [Pi.smul_apply, smul_eq_mul, mul_one] using rule_distances colour
  · exact eigenpair.le

end EIGS.RuleSystem
