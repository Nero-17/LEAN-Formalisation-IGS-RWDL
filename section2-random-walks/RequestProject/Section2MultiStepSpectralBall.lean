import RequestProject.Section2MultiStepBall
import RequestProject.Section2MetricComparison
import RequestProject.Section2ConcreteSpectralRadius

/-! A genuine mesoscopic geometric input: actual original unit-distance
balls lie in actual multi-step stars at a fixed fraction of the Perron scale. -/

namespace EIGS

open scoped BigOperators Classical

variable {K : ℕ}

theorem EIGSData.metricLengths_iterate_eigenpair (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    {lengths : Fin K → ℝ} {rate : ℝ} (rate_nonnegative : 0 ≤ rate)
    (eigenpair : (system.ruleFamily rule_connected).metricLengths lengths = rate • lengths)
    (steps : ℕ) :
    (system.ruleFamily rule_connected).metricLengths^[steps] lengths = rate ^ steps • lengths := by
  induction steps with
  | zero => simp
  | succ steps induction_hypothesis =>
    rw [Function.iterate_succ_apply', induction_hypothesis]
    ext colour
    change (system.ruleNetwork colour).weightedDistance (rate ^ steps • lengths)
      (system.plantPlus colour) (system.plantMinus colour) = _
    rw [(system.ruleNetwork colour).weightedDistance_smul lengths (pow_nonneg rate_nonnegative steps)]
    have coordinate := congrFun eigenpair colour
    change (system.ruleNetwork colour).weightedDistance lengths
      (system.plantPlus colour) (system.plantMinus colour) = rate * lengths colour at coordinate
    rw [coordinate]
    simp only [Pi.smul_apply, smul_eq_mul, pow_succ]
    ring

theorem xiSimpleGraph_ball_subset_multistep_star_of_eigenpair (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    {lengths : Fin K → ℝ} (lengths_positive : ∀ colour, 0 < lengths colour)
    {rate : ℝ} (rate_positive : 0 < rate)
    (eigenpair : (system.ruleFamily rule_connected).metricLengths lengths = rate • lengths) :
    ∃ coefficient : ℝ, 0 < coefficient ∧
      ∀ coarse steps (center : XiVtx system coarse) (radius : ℝ),
        0 < radius → radius ≤ coefficient * rate ^ steps →
        ∀ vertex : XiVtx system (coarse + steps),
          ((XiSimpleGraph system (coarse + steps)).dist
            (xiForward system coarse steps center) vertex : ℝ) < radius →
          xiIncidentStar system coarse center steps vertex := by
  classical
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  let lower := Finset.univ.inf' Finset.univ_nonempty lengths
  let upper := Finset.univ.sup' Finset.univ_nonempty lengths
  have lower_positive : 0 < lower :=
    (Finset.lt_inf'_iff _).mpr (fun colour _ => lengths_positive colour)
  have upper_positive : 0 < upper :=
    (lengths_positive system.initCol).trans_le (Finset.le_sup' lengths (Finset.mem_univ _))
  refine ⟨lower / upper, div_pos lower_positive upper_positive,
    fun coarse steps center radius radius_positive radius_bound vertex in_ball => ?_⟩
  have terminal_bounds : ∀ colour,
      upper * radius ≤ ((system.ruleFamily rule_connected).metricLengths^[steps] lengths) colour := by
    intro colour
    rw [system.metricLengths_iterate_eigenpair rule_connected rate_positive.le eigenpair]
    simp only [Pi.smul_apply, smul_eq_mul]
    have scaled_radius := mul_le_mul_of_nonneg_left radius_bound upper_positive.le
    have cancellation : upper * (lower / upper * rate ^ steps) = lower * rate ^ steps := by
      field_simp
    rw [cancellation] at scaled_radius
    have length_lower : lower ≤ lengths colour := Finset.inf'_le lengths (Finset.mem_univ colour)
    calc
      upper * radius ≤ lower * rate ^ steps := scaled_radius
      _ ≤ lengths colour * rate ^ steps :=
        mul_le_mul_of_nonneg_right length_lower (pow_nonneg rate_positive.le steps)
      _ = rate ^ steps * lengths colour := mul_comm _ _
  have metric_bound := (XiNetwork system (coarse + steps)).weightedDistance_length_bounds
    (xiSimpleGraph_connected system rule_connected _)
    (xiNetwork_loopless system rule_connected rules_loopless _)
    lower_positive.le upper_positive.le
    (fun colour => Finset.inf'_le lengths (Finset.mem_univ colour))
    (fun colour => Finset.le_sup' lengths (Finset.mem_univ colour))
    (xiForward system coarse steps center) vertex
  apply xiWeightedBall_subset_multistep_star system rule_connected coarse steps center
    (fun colour => (lengths_positive colour).le) (mul_pos upper_positive radius_positive).le
    terminal_bounds vertex
  exact metric_bound.2.trans_lt (mul_lt_mul_of_pos_left in_ball upper_positive)

theorem xiSimpleGraph_ball_subset_multistep_star_at_distanceSpectralRadius
    (system : EIGSData K) (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ coefficient : ℝ, 0 < coefficient ∧
      ∀ coarse steps (center : XiVtx system coarse) (radius : ℝ),
        0 < radius → radius ≤ coefficient * (system.distanceSpectralRadius rule_connected) ^ steps →
        ∀ vertex : XiVtx system (coarse + steps),
          ((XiSimpleGraph system (coarse + steps)).dist
            (xiForward system coarse steps center) vertex : ℝ) < radius →
          xiIncidentStar system coarse center steps vertex := by
  obtain ⟨lengths, lengths_positive, rate_positive, _, eigenpair⟩ :=
    system.metricLengths_spectral_eigenpair rule_connected rules_loopless rules_unique distance_positive
  exact xiSimpleGraph_ball_subset_multistep_star_of_eigenpair system rule_connected
    rules_loopless lengths_positive rate_positive eigenpair

end EIGS

#print axioms EIGS.EIGSData.metricLengths_iterate_eigenpair
#print axioms EIGS.xiSimpleGraph_ball_subset_multistep_star_of_eigenpair
#print axioms EIGS.xiSimpleGraph_ball_subset_multistep_star_at_distanceSpectralRadius
