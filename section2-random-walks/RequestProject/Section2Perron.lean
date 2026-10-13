import RequestProject.Section2Cuts
import RequestProject.NonlinearPerron

/-!
# A positive nonlinear eigenpair from the original distance-positive rules

Distance positivity is expressed exactly as in the paper's Lemma 2.6 proof:
deleting any colour disconnects the two planting vertices. The finite-cut proof
supplies strong positivity; the compact Thomson argument then supplies existence.
There is no Perron-existence, eigenpair, continuity-at-the-boundary, or convergence
hypothesis in these statements.
-/

namespace EIGS.RuleSystem

open scoped BigOperators

variable {K : ℕ}

theorem distance_positive_eigenpair (rules : EIGS.RuleSystem K) (colours_positive : 0 < K)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((rules.R ruleColour).withoutColour edgeColour).Reachable
        (rules.βplus ruleColour) (rules.βminus ruleColour)) :
    ∃ (vector : Fin K → ℝ) (rate : ℝ),
      (∀ colour, 0 < vector colour) ∧ 0 < rate ∧ (∑ colour, vector colour) = 1 ∧
        rules.toRenormMap.apply vector = rate • vector := by
  exact rules.toRenormMap.positive_eigenpair_of_strongly_positive colours_positive
    (rules.renorm_strongly_positive distance_positive)

/-- The existence-and-uniqueness conclusion for the eigenvalue of the actual
distance-positive multicolour rule system. -/
theorem distance_positive_eigenvalue_exists_unique (rules : EIGS.RuleSystem K)
    (colours_positive : 0 < K)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((rules.R ruleColour).withoutColour edgeColour).Reachable
        (rules.βplus ruleColour) (rules.βminus ruleColour)) :
    ∃! rate : ℝ, 0 < rate ∧ ∃ vector : Fin K → ℝ,
      (∀ colour, 0 < vector colour) ∧ rules.toRenormMap.apply vector = rate • vector := by
  obtain ⟨vector, rate, vector_positive, rate_positive, normalized, eigenpair⟩ :=
    rules.distance_positive_eigenpair colours_positive distance_positive
  refine ⟨rate, ⟨rate_positive, vector, vector_positive, eigenpair⟩, ?_⟩
  rintro candidate ⟨candidate_positive, candidate_vector, candidate_vector_positive,
    candidate_eigenpair⟩
  exact rules.toRenormMap.eigenvalue_unique colours_positive candidate_vector_positive
    vector_positive candidate_positive rate_positive candidate_eigenpair eigenpair

/-- Corollary 2.7 for the original rule networks, with the positive eigenpair
proved from distance positivity rather than supplied as a hypothesis. -/
theorem distance_positive_iterate_growth (rules : EIGS.RuleSystem K)
    (colours_positive : 0 < K)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((rules.R ruleColour).withoutColour edgeColour).Reachable
        (rules.βplus ruleColour) (rules.βminus ruleColour)) :
    ∃ rate lower upper : ℝ, 0 < rate ∧ 0 < lower ∧ 0 < upper ∧
      ∀ level : ℕ, ∀ colour : Fin K,
        lower * rate ^ level ≤ rules.toRenormMap.apply^[level] (fun _ => 1) colour ∧
          rules.toRenormMap.apply^[level] (fun _ => 1) colour ≤ upper * rate ^ level := by
  obtain ⟨vector, rate, vector_positive, rate_positive, normalized, eigenpair⟩ :=
    rules.distance_positive_eigenpair colours_positive distance_positive
  obtain ⟨lower, upper, lower_positive, upper_positive, growth⟩ :=
    rules.toRenormMap.iterate_one_two_sided vector_positive rate_positive eigenpair
  exact ⟨rate, lower, upper, rate_positive, lower_positive, upper_positive, growth⟩

end EIGS.RuleSystem
