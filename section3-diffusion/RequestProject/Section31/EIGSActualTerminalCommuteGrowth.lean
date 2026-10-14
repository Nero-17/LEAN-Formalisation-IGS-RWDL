import RequestProject.Section2ConcreteRandomWalk
import RequestProject.Section2SpectralGrowth
import RequestProject.Section31.EIGSActualTerminalResistanceDimension

/-! The actual terminal commute time, with its canonical mass-resistance
growth rate identified internally. All generations concern the original
simple graph and its two inherited original terminals. -/

namespace EIGS
open scoped Classical
noncomputable section
variable {K : ℕ}

theorem xiSimpleGraph_terminal_commute_canonical_bounds (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ level,
      lower * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius connected distancePositive) ^ level ≤
        expExit (XiSimpleGraph system level) ({xiNegativeTerminal system level}ᶜ) (xiPositiveTerminal system level) +
          expExit (XiSimpleGraph system level) ({xiPositiveTerminal system level}ᶜ) (xiNegativeTerminal system level) ∧
      expExit (XiSimpleGraph system level) ({xiNegativeTerminal system level}ᶜ) (xiPositiveTerminal system level) +
          expExit (XiSimpleGraph system level) ({xiPositiveTerminal system level}ᶜ) (xiNegativeTerminal system level) ≤
        upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius connected distancePositive) ^ level := by
  obtain ⟨massPositive, massLower, massUpper, massLowerPositive, massUpperPositive, massBounds⟩ :=
    eigs_mass_spectral_growth system connected distancePositive
  obtain ⟨resistanceLower, resistanceUpper, resistanceLowerPositive, resistanceUpperPositive, resistanceBounds⟩ :=
    xiSimpleGraph_terminal_resistance_canonical_bounds system connected loopless unique plantingNonadjacent distancePositive
  have resistancePositive := (system.resistanceSpectralRadius_positive_eigenpair connected distancePositive).1
  refine ⟨2 * massLower * resistanceLower, 2 * massUpper * resistanceUpper, by positivity, by positivity, ?_⟩
  intro level
  rw [xiSimpleGraph_commute_eq_mass_mul_resistance system connected loopless unique plantingNonadjacent level,
    xiNetwork_effRes_eq_simpleGraph_resistance system connected loopless unique plantingNonadjacent level]
  have resistanceNonnegative :=
    (mul_pos resistanceLowerPositive (pow_pos resistancePositive level)).le.trans (resistanceBounds level).1
  have lowerProduct := mul_le_mul (massBounds level).1 (resistanceBounds level).1
    (mul_pos resistanceLowerPositive (pow_pos resistancePositive level)).le
    (Nat.cast_nonneg (totalEdges system.toRuleData level))
  have upperProduct := mul_le_mul (massBounds level).2 (resistanceBounds level).2
    resistanceNonnegative (mul_pos massUpperPositive (pow_pos massPositive level)).le
  change _ ≤ 2 * (totalEdges system.toRuleData level : ℝ) * _ ∧
    2 * (totalEdges system.toRuleData level : ℝ) * _ ≤ _
  constructor <;> rw [mul_pow] <;> nlinarith

end
end EIGS

#print axioms EIGS.xiNetwork_effRes_eq_simpleGraph_resistance
#print axioms EIGS.xiSimpleGraph_commute_eq_mass_mul_resistance
#print axioms EIGS.xiSimpleGraph_terminal_commute_canonical_bounds
