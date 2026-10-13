import RequestProject.Section2ConcreteSimplicity
import RequestProject.Section2DegreeGrowth
import RequestProject.Section2SimpleCommute
import RequestProject.Section2MassGrowth

/-! Actual Xi simple-walk resistance and commute identities. The underlying
simple-graph convention is retained explicitly in each statement. -/

namespace EIGS

open scoped Classical

variable {K : ℕ}

theorem xiNetwork_effRes_eq_simpleGraph_resistance (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour)) (level : ℕ) :
    (XiNetwork system level).effRes (xiPositiveTerminal system level)
      (xiNegativeTerminal system level) (xiNetwork_terminal_flow system rule_connected level)
      (fun _ => 1) =
    effResToBoundary (XiSimpleGraph system level)
      (Finset.univ.erase (xiNegativeTerminal system level)) (xiPositiveTerminal system level) := by
  exact (XiNetwork system level).effRes_eq_simpleGraph_resistance
    (xiNetwork_loopless system rule_connected rules_loopless level)
    (xiNetwork_edges_unique system rule_connected rules_loopless rules_unique planting_nonadjacent level)
    (xiSimpleGraph_connected system rule_connected level) _ _ (xiTerminals_distinct system level)

theorem xiSimpleGraph_resistance_normalized_limit (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ rate limit : ℝ, 0 < rate ∧ 0 < limit ∧
      Filter.Tendsto (fun level => effResToBoundary (XiSimpleGraph system level)
        (Finset.univ.erase (xiNegativeTerminal system level)) (xiPositiveTerminal system level) /
          rate ^ level) Filter.atTop (nhds limit) := by
  obtain ⟨rate, limit, rate_positive, limit_positive, convergence⟩ :=
    xiNetwork_terminal_resistance_normalized_limit system rule_connected distance_positive
  refine ⟨rate, limit, rate_positive, limit_positive, ?_⟩
  convert convergence using 1
  ext level
  rw [xiNetwork_effRes_eq_simpleGraph_resistance system rule_connected rules_loopless
    rules_unique planting_nonadjacent level]

theorem xiSimpleGraph_commute_eq_mass_mul_resistance (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour)) (level : ℕ) :
    expExit (XiSimpleGraph system level) ({xiNegativeTerminal system level}ᶜ)
        (xiPositiveTerminal system level) +
      expExit (XiSimpleGraph system level) ({xiPositiveTerminal system level}ᶜ)
        (xiNegativeTerminal system level) =
      2 * (Fintype.card (XiNetwork system level).E : ℝ) *
        (XiNetwork system level).effRes (xiPositiveTerminal system level)
          (xiNegativeTerminal system level) (xiNetwork_terminal_flow system rule_connected level)
          (fun _ => 1) := by
  exact (XiNetwork system level).commute_eq_mass_mul_effRes
    (xiNetwork_loopless system rule_connected rules_loopless level)
    (xiNetwork_edges_unique system rule_connected rules_loopless rules_unique planting_nonadjacent level)
    (xiSimpleGraph_connected system rule_connected level) _ _ (xiTerminals_distinct system level)

/-- The expected terminal commute time of the actual simple random walk has
constructed geometric growth, from the original rules and the explicit simple
orientation convention. -/
theorem xiSimpleGraph_terminal_commute_growth (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ rate lower upper : ℝ, 0 < rate ∧ 0 < lower ∧ 0 < upper ∧ ∀ level,
      lower * rate ^ level ≤
        expExit (XiSimpleGraph system level) ({xiNegativeTerminal system level}ᶜ)
          (xiPositiveTerminal system level) +
        expExit (XiSimpleGraph system level) ({xiPositiveTerminal system level}ᶜ)
          (xiNegativeTerminal system level) ∧
      expExit (XiSimpleGraph system level) ({xiNegativeTerminal system level}ᶜ)
          (xiPositiveTerminal system level) +
        expExit (XiSimpleGraph system level) ({xiPositiveTerminal system level}ᶜ)
          (xiNegativeTerminal system level) ≤ upper * rate ^ level := by
  obtain ⟨mass_rate, mass_lower, mass_upper, mass_rate_positive, mass_lower_positive,
    mass_upper_positive, mass_growth⟩ := eigs_mass_growth_from_rules system rule_connected distance_positive
  obtain ⟨resistance_rate, resistance_lower, resistance_upper, resistance_rate_positive,
    resistance_lower_positive, resistance_upper_positive, resistance_growth⟩ :=
    xiNetwork_terminal_resistance_growth system rule_connected distance_positive
  refine ⟨mass_rate * resistance_rate, 2 * mass_lower * resistance_lower,
    2 * mass_upper * resistance_upper, mul_pos mass_rate_positive resistance_rate_positive,
    by positivity, by positivity, fun level => ?_⟩
  rw [xiSimpleGraph_commute_eq_mass_mul_resistance system rule_connected rules_loopless
    rules_unique planting_nonadjacent level]
  have lower_product := mul_le_mul (mass_growth level).1 (resistance_growth level).1
    (mul_nonneg resistance_lower_positive.le (pow_pos resistance_rate_positive level).le)
    (Nat.cast_nonneg (totalEdges system.toRuleData level))
  have resistance_nonneg := (XiNetwork system level).effRes_nonneg
    (xiPositiveTerminal system level) (xiNegativeTerminal system level)
    (xiNetwork_terminal_flow system rule_connected level) (fun _ => zero_le_one)
  have upper_product := mul_le_mul (mass_growth level).2 (resistance_growth level).2
    resistance_nonneg (mul_pos mass_upper_positive (pow_pos mass_rate_positive level)).le
  change _ ≤ 2 * (totalEdges system.toRuleData level : ℝ) * _ ∧
    2 * (totalEdges system.toRuleData level : ℝ) * _ ≤ _
  constructor <;> rw [mul_pow]
  · nlinarith
  · nlinarith

end EIGS
