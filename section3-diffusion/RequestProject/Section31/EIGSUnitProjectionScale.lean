import RequestProject.Section31.EIGSUnitProjectionIncrement

/-! Actual adjacent projections at every original index have a uniform
mass-times-resistance decay bound in terms of the actual scaled unit energy. -/

namespace EIGS

variable {K : ℕ}

theorem exists_xiUnitProjectionIncrement_scaled_bound (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ level offset
      (values : XiVtx system (level + 1 + offset) → ℝ),
      ‖xiFiniteSpeedL2 system mass (level + 1 + offset)
        (xiUnitProjectionIncrement system rulesConnected level offset values)‖ ^ 2 ≤
      constant / (mass.rate * resistanceRate) ^ (level + 1) *
        xiScaledUnitEnergy system resistanceRate normalization (level + 1 + offset) values := by
  obtain ⟨constant, constantPositive, incrementBound⟩ :=
    exists_xiUnitProjectionIncrement_native_bound system rulesConnected mass
  obtain ⟨upper, upperPositive, resistanceBound⟩ := exists_xiResistance_iterate_upper_bound
    system rulesConnected distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  refine ⟨constant * upper / normalization, div_pos (mul_pos constantPositive upperPositive) normalizationPositive, ?_⟩
  intro level offset values
  have comparison := incrementBound level offset (upper * resistanceRate ^ offset) (resistanceBound offset) values
  convert comparison using 1
  unfold xiScaledUnitEnergy
  rw [mul_pow, pow_add]
  field_simp [ne_of_gt normalizationPositive, ne_of_gt ratePositive, ne_of_gt mass.rate_positive]
  <;> ring

end EIGS
