import RequestProject.Section2StarVoltageMass
import RequestProject.Section2UnitTraceComposition
import RequestProject.Section2ExitVoltage
import RequestProject.Section2StarExit

/-! A lower bound for actual star exit times, obtained from a genuine positive
child in each incident cell, its descendant mass, and the Green identity. -/

namespace EIGS

open scoped BigOperators Classical

variable {K : ℕ}

theorem xiIncidentStarDomain_voltage_mass_spectral_lower (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ lower : ℝ, 0 < lower ∧ ∀ coarse depth (center : XiVtx system coarse),
      lower * (XiSimpleGraph system coarse).degree center *
        realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ depth ≤
      ∑ vertex : XiVtx system (coarse + (1 + depth)),
        boundaryVoltageProfile (XiSimpleGraph system (coarse + (1 + depth)))
          (xiIncidentStarDomain system coarse (1 + depth) center)
          (xiForward system coarse (1 + depth) center) vertex *
        ((XiSimpleGraph system (coarse + (1 + depth))).degree vertex : ℝ) := by
  obtain ⟨lower, lower_positive, bound⟩ := xiIncident_nonstationary_voltage_mass_spectral_lower
    system rule_connected rules_loopless rules_unique planting_nonadjacent distance_positive
  refine ⟨lower, lower_positive, fun coarse depth center => ?_⟩
  rw [xiIncidentStar_boundaryVoltageProfile_eq_unitPotentialAt system rule_connected rules_loopless
    rules_unique planting_nonadjacent]
  have mass_identity := (XiNetwork system (coarse + (1 + depth))).voltage_degree_mass_eq_endpoint_sum
    (xiNetwork_loopless system rule_connected rules_loopless _)
    (xiNetwork_edges_unique system rule_connected rules_loopless rules_unique planting_nonadjacent _)
    (xiUnitPotentialAt system rule_connected coarse (coarse + (1 + depth)) (by omega)
      (fun vertex => if vertex = center then 1 else 0))
  change (∑ vertex : XiVtx system (coarse + (1 + depth)),
    xiUnitPotentialAt system rule_connected coarse (coarse + (1 + depth)) (by omega)
      (fun vertex => if vertex = center then 1 else 0) vertex *
      ((XiSimpleGraph system (coarse + (1 + depth))).degree vertex : ℝ)) =
    ∑ edge : XiEdge system.toRuleData (coarse + (1 + depth)),
      (xiUnitPotentialAt system rule_connected coarse (coarse + (1 + depth)) (by omega)
        (fun vertex => if vertex = center then 1 else 0) (XiTail system (coarse + (1 + depth)) edge) +
      xiUnitPotentialAt system rule_connected coarse (coarse + (1 + depth)) (by omega)
        (fun vertex => if vertex = center then 1 else 0) (XiHead system (coarse + (1 + depth)) edge)) at mass_identity
  rw [mass_identity]
  have decomposition := xiUnitPotentialAt_first_decomposition system rule_connected coarse depth
    (fun vertex => if vertex = center then 1 else 0)
  have mass_reindex := congrArg
    (fun fine_level : {fine_level : ℕ // coarse ≤ fine_level} =>
      ∑ edge : XiEdge system.toRuleData fine_level.val,
        (xiUnitPotentialAt system rule_connected coarse fine_level.val fine_level.property
          (fun vertex => if vertex = center then 1 else 0) (XiTail system fine_level.val edge) +
        xiUnitPotentialAt system rule_connected coarse fine_level.val fine_level.property
          (fun vertex => if vertex = center then 1 else 0) (XiHead system fine_level.val edge)))
    (show (⟨(coarse + 1) + depth, by omega⟩ : {fine_level : ℕ // coarse ≤ fine_level}) =
      ⟨coarse + (1 + depth), by omega⟩ from Subtype.ext (Nat.add_assoc coarse 1 depth))
  dsimp only at mass_reindex
  rw [← mass_reindex, decomposition]
  exact bound coarse depth center

theorem xiIncidentStarDomain_expExit_successor_spectral_lower (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ lower : ℝ, 0 < lower ∧ ∀ coarse depth (center : XiVtx system coarse),
      lower * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rule_connected distance_positive) ^ (1 + depth) ≤
      expExit (XiSimpleGraph system (coarse + (1 + depth)))
        (xiIncidentStarDomain system coarse (1 + depth) center)
        (xiForward system coarse (1 + depth) center) := by
  obtain ⟨mass_lower, mass_lower_positive, mass_bound⟩ :=
    xiIncidentStarDomain_voltage_mass_spectral_lower system rule_connected rules_loopless rules_unique
      planting_nonadjacent distance_positive
  obtain ⟨resistance_lower, _, resistance_lower_positive, _, resistance_bounds⟩ :=
    xiIncidentStarDomain_resistance_spectral_bounds system rule_connected rules_loopless rules_unique
      planting_nonadjacent distance_positive
  have mass_rate_positive := (eigs_mass_spectral_growth system rule_connected distance_positive).1
  have resistance_rate_positive :=
    (system.resistanceSpectralRadius_positive_eigenpair rule_connected distance_positive).1
  refine ⟨resistance_lower * mass_lower / realMatrixSpectralRadius (massMatrixR system.toRuleData),
    by positivity, fun coarse depth center => ?_⟩
  rw [expExit_eq_resistance_mul_voltage_mass _ (xiSimpleGraph_connected system rule_connected _)
    (xiIncidentStarDomain_complement_nonempty system coarse (1 + depth) center)
    (xiIncidentStarDomain_center_mem system coarse (1 + depth) center)]
  have degree_positive := xiSimpleGraph_degree_positive system rule_connected coarse center
  apply le_trans _ (mul_le_mul (resistance_bounds coarse (1 + depth) center).1
    (mass_bound coarse depth center) (by positivity)
    (le_of_lt (effResToBoundary_pos _ (xiSimpleGraph_connected system rule_connected _)
      (xiIncidentStarDomain_complement_nonempty system coarse (1 + depth) center)
      (xiIncidentStarDomain_center_mem system coarse (1 + depth) center))))
  apply le_of_eq
  simp only [mul_pow, pow_add, pow_one]
  field_simp [ne_of_gt degree_positive, ne_of_gt mass_rate_positive]
  <;> ring

theorem xiIncidentStarDomain_expExit_spectral_lower (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ lower : ℝ, 0 < lower ∧ ∀ coarse steps (center : XiVtx system coarse),
      lower * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rule_connected distance_positive) ^ steps ≤
      expExit (XiSimpleGraph system (coarse + steps))
        (xiIncidentStarDomain system coarse steps center) (xiForward system coarse steps center) := by
  obtain ⟨lower, lower_positive, lower_bound⟩ :=
    xiIncidentStarDomain_expExit_successor_spectral_lower system rule_connected rules_loopless rules_unique
      planting_nonadjacent distance_positive
  have time_rate_positive : 0 < realMatrixSpectralRadius (massMatrixR system.toRuleData) *
      system.resistanceSpectralRadius rule_connected distance_positive :=
    mul_pos (eigs_mass_spectral_growth system rule_connected distance_positive).1
      (system.resistanceSpectralRadius_positive_eigenpair rule_connected distance_positive).1
  refine ⟨min 1 lower, lt_min zero_lt_one lower_positive, fun coarse steps center => ?_⟩
  cases steps with
  | zero =>
      rw [pow_zero, mul_one]
      apply (min_le_left _ _).trans
      rw [expExit_recurrence (xiSimpleGraph_connected system rule_connected _)
        (xiIncidentStarDomain_complement_nonempty system coarse 0 center)
        (xiIncidentStarDomain_center_mem system coarse 0 center)]
      have nonnegative : 0 ≤ ∑ vertex : XiVtx system (coarse + 0),
          transProb (XiSimpleGraph system (coarse + 0)) (xiForward system coarse 0 center) vertex *
          expExit (XiSimpleGraph system (coarse + 0)) (xiIncidentStarDomain system coarse 0 center) vertex :=
        Finset.sum_nonneg (fun vertex _ => mul_nonneg (transProb_nonneg _ _) (expExit_nonneg _))
      linarith
  | succ depth =>
      apply (mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg time_rate_positive.le _)).trans
      change lower * _ ^ (depth + 1) ≤ _
      rw [show depth + 1 = 1 + depth by omega]
      exact lower_bound coarse depth center

end EIGS

#print axioms EIGS.xiIncidentStarDomain_voltage_mass_spectral_lower
#print axioms EIGS.xiIncidentStarDomain_expExit_successor_spectral_lower
#print axioms EIGS.xiIncidentStarDomain_expExit_spectral_lower
