import RequestProject.Section2Perron
import RequestProject.NonlinearConvergence

/-! Multicolour Perron existence, uniqueness and convergence on concrete rules. -/

namespace EIGS.RuleSystem

open scoped BigOperators
open Filter Topology

variable {K : ℕ}

theorem distance_positive_normalized_eigenpair_exists_unique
    (rules : EIGS.RuleSystem K) (colours_positive : 0 < K)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((rules.R ruleColour).withoutColour edgeColour).Reachable
        (rules.βplus ruleColour) (rules.βminus ruleColour)) :
    ∃! pair : (Fin K → ℝ) × ℝ,
      (∀ i, 0 < pair.1 i) ∧ 0 < pair.2 ∧ (∑ i, pair.1 i) = 1 ∧
        rules.toRenormMap.apply pair.1 = pair.2 • pair.1 := by
  exact rules.toRenormMap.existsUnique_positive_normalized_eigenpair colours_positive
    (rules.renorm_strongly_positive distance_positive)

theorem distance_positive_normalized_iterate_limit
    (rules : EIGS.RuleSystem K) (colours_positive : 0 < K)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((rules.R ruleColour).withoutColour edgeColour).Reachable
        (rules.βplus ruleColour) (rules.βminus ruleColour)) :
    ∃ (rate limit : ℝ) (vector : Fin K → ℝ),
      0 < rate ∧ 0 < limit ∧ (∀ colour, 0 < vector colour) ∧
      (∑ colour, vector colour) = 1 ∧
      rules.toRenormMap.apply vector = rate • vector ∧
      Tendsto (fun level => fun colour =>
        rules.toRenormMap.apply^[level] (fun _ => 1) colour / rate ^ level)
        atTop (nhds (limit • vector)) := by
  obtain ⟨vector, rate, hvector, hrate, hnorm, heigen⟩ :=
    rules.distance_positive_eigenpair colours_positive distance_positive
  obtain ⟨limit, hlimit, hconvergence⟩ :=
    rules.toRenormMap.iterate_normalized_limit_of_strongly_positive colours_positive
      (rules.renorm_strongly_positive distance_positive) hvector hrate hnorm heigen
  exact ⟨rate, limit, vector, hrate, hlimit, hvector, hnorm, heigen, hconvergence⟩

end EIGS.RuleSystem
