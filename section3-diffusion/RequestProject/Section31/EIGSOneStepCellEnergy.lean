import RequestProject.Section31.EIGSHarmonicCellL2Bound
import RequestProject.Section31.EIGSRuleZeroBoundaryEnergy

/-! Actual old-skeleton-zero functions satisfy an endpoint energy estimate on
one substitution step. Descendant harmonic extension then gives a native norm
estimate with the actual mass and resistance scales. -/

namespace EIGS

open scoped BigOperators

variable {K : ℕ}

theorem exists_xiStep_endpoint_energy_bound (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ level (resistances : Fin K → ℝ)
      (resistancesPositive : ∀ colour, 0 < resistances colour) (upper : ℝ),
      (∀ colour, resistances colour ≤ upper) →
      ∀ values : XiVtx system (level + 1) → ℝ,
      (∀ vertex : XiVtx system level, values (Sum.inl vertex) = 0) →
      (∑ edge : XiEdge system.toRuleData (level + 1),
        ((values (XiTail system (level + 1) edge)) ^ 2 +
          (values (XiHead system (level + 1) edge)) ^ 2)) ≤
      constant * upper *
        ((XiNetwork system (level + 1)).potentialNetwork resistances resistancesPositive).energy values := by
  classical
  obtain ⟨constant, constantPositive, vertexBound⟩ := exists_xiStep_zero_boundary_energy_bound system rulesConnected
  refine ⟨2 * ((∑ colour : Fin K, (Fintype.card (system.rule colour).E : ℝ)) + 1) * constant,
    by positivity, ?_⟩
  intro level resistances resistancesPositive upper resistancesBounded values oldZero
  rw [xiPotentialEnergy_succ_eq_substituted system rulesConnected,
    Network.substituted_potential_energy_eq_sum, Finset.mul_sum]
  change (∑ edge : (Σ parent : XiEdge system.toRuleData level,
      (system.rule (XiCol system.toRuleData level parent)).E),
      ((values ((XiNetwork system level).substEmbed (system.ruleFamily rulesConnected) edge.1
          ((system.rule (XiCol system.toRuleData level edge.1)).tail edge.2))) ^ 2 +
        (values ((XiNetwork system level).substEmbed (system.ruleFamily rulesConnected) edge.1
          ((system.rule (XiCol system.toRuleData level edge.1)).head edge.2))) ^ 2)) ≤ _
  rw [Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro parent _
  have upperPositive : 0 < upper := (resistancesPositive system.initCol).trans_le (resistancesBounded system.initCol)
  have energyNonnegative :=
    ((system.ruleNetwork (XiCol system.toRuleData level parent)).potentialNetwork resistances resistancesPositive).energy_nonneg
      (fun vertex => values ((XiNetwork system level).substEmbed (system.ruleFamily rulesConnected) parent vertex))
  have cardinalBound : (Fintype.card (system.rule (XiCol system.toRuleData level parent)).E : ℝ) ≤
      (∑ colour : Fin K, (Fintype.card (system.rule colour).E : ℝ)) + 1 := by
    have singleBound := Finset.single_le_sum
      (f := fun colour : Fin K => (Fintype.card (system.rule colour).E : ℝ))
      (fun colour _ => Nat.cast_nonneg _) (Finset.mem_univ (XiCol system.toRuleData level parent))
    exact singleBound.trans (le_add_of_nonneg_right zero_le_one)
  calc
    _ ≤ ∑ child : (system.rule (XiCol system.toRuleData level parent)).E,
        (2 * constant * upper *
          ((system.ruleNetwork (XiCol system.toRuleData level parent)).potentialNetwork resistances resistancesPositive).energy
            (fun vertex => values ((XiNetwork system level).substEmbed (system.ruleFamily rulesConnected) parent vertex))) := by
      apply Finset.sum_le_sum
      intro child _
      have tailBound := vertexBound level resistances resistancesPositive upper resistancesBounded values oldZero parent
        ((system.rule (XiCol system.toRuleData level parent)).tail child)
      have headBound := vertexBound level resistances resistancesPositive upper resistancesBounded values oldZero parent
        ((system.rule (XiCol system.toRuleData level parent)).head child)
      linarith
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have multiplied := mul_le_mul_of_nonneg_right cardinalBound
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) constantPositive.le) upperPositive.le) energyNonnegative)
      convert multiplied using 1 <;> dsimp only [EIGSData.ruleFamily, XiNetwork] <;> ring

theorem exists_xiStep_harmonic_native_energy_bound (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (mass : XiMassParameters system) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ level offset (resistances : Fin K → ℝ)
      (resistancesPositive : ∀ colour, 0 < resistances colour) (upper : ℝ),
      (∀ colour, (system.ruleFamily rulesConnected).Psi^[offset] resistances colour ≤ upper) →
      ∀ values : XiVtx system (level + 1) → ℝ,
      (∀ vertex : XiVtx system level, values (Sum.inl vertex) = 0) →
      ‖xiFiniteSpeedL2 system mass (level + 1 + offset)
        (xiPotentialValues system rulesConnected (level + 1) offset resistances resistancesPositive values)‖ ^ 2 ≤
      constant / mass.rate ^ (level + 1) * upper *
        ((XiNetwork system (level + 1 + offset)).potentialNetwork resistances resistancesPositive).energy
          (xiPotentialValues system rulesConnected (level + 1) offset resistances resistancesPositive values) := by
  obtain ⟨massConstant, massConstantPositive, normBound⟩ :=
    exists_xiPotentialValues_native_norm_bound system rulesConnected mass
  obtain ⟨energyConstant, energyConstantPositive, endpointBound⟩ := exists_xiStep_endpoint_energy_bound system rulesConnected
  refine ⟨massConstant * energyConstant, mul_pos massConstantPositive energyConstantPositive, ?_⟩
  intro level offset resistances resistancesPositive upper resistancesBounded values oldZero
  rw [xiPotentialValues_energy]
  have endpointEstimate := endpointBound level ((system.ruleFamily rulesConnected).Psi^[offset] resistances)
    (ruleFamily_Psi_iterate_positive system rulesConnected resistances resistancesPositive offset)
    upper resistancesBounded values oldZero
  have comparison := (normBound (level + 1) offset resistances resistancesPositive values).trans
    (mul_le_mul_of_nonneg_left endpointEstimate (div_pos massConstantPositive (pow_pos mass.rate_positive _)).le)
  convert comparison using 1 <;> ring

end EIGS
