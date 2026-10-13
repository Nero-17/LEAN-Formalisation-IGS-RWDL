import RequestProject.Section2MassConvergence

/-! Actual descendant proportions and consistency of the limiting cell weights. -/

namespace EIGS

open scoped BigOperators
open Filter Topology

variable {K : ℕ}

theorem chiVec_replanted_eq_mass_power (data : RuleData K) (initialColour : Fin K)
    (level : ℕ) :
    chiVec { data with ι := initialColour } level = (massMatrixR data ^ level) initialColour := by
  rw [chiVec_vecMul_pow]
  change Matrix.vecMul (chiVec { data with ι := initialColour } 0)
    (massMatrixR data ^ level) = _
  ext colour
  simp [Matrix.vecMul, dotProduct, chiVec, chiCount_zero]

theorem totalEdges_replanted_succ (data : RuleData K) (initialColour : Fin K)
    (level : ℕ) :
    (totalEdges { data with ι := initialColour } (level + 1) : ℝ) =
      ∑ colour, massMatrixR data initialColour colour *
        (totalEdges { data with ι := colour } level : ℝ) := by
  simp_rw [totalEdges_eq_sum, chiVec_replanted_eq_mass_power, pow_succ',
    Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem mass_amplitude_eigenpair_of_descendant_limits (data : RuleData K)
    {rate : ℝ} {amplitude : Fin K → ℝ} (rate_positive : 0 < rate)
    (convergence : ∀ initialColour,
      Tendsto (fun level =>
        (totalEdges { data with ι := initialColour } level : ℝ) / rate ^ level)
        atTop (nhds (amplitude initialColour))) :
    (massMatrixR data).mulVec amplitude = rate • amplitude := by
  ext initialColour
  have sum_limit := tendsto_finset_sum (Finset.univ : Finset (Fin K))
    (fun colour _ => (convergence colour).const_mul (massMatrixR data initialColour colour))
  have recurrence_limit : Tendsto (fun level =>
      (totalEdges { data with ι := initialColour } (level + 1) : ℝ) / rate ^ level)
      atTop (nhds ((massMatrixR data).mulVec amplitude initialColour)) := by
    convert sum_limit using 1
    ext level
    rw [totalEdges_replanted_succ, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro colour _
    exact mul_div_assoc _ _ _
  have shifted_limit := ((convergence initialColour).comp (tendsto_add_atTop_nat 1)).mul_const rate
  have scaled_limit : Tendsto (fun level =>
      (totalEdges { data with ι := initialColour } (level + 1) : ℝ) / rate ^ level)
      atTop (nhds (amplitude initialColour * rate)) := by
    convert shifted_limit using 1
    ext level
    dsimp only [Function.comp_apply]
    rw [pow_succ]
    field_simp
  simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using
    tendsto_nhds_unique recurrence_limit scaled_limit

theorem descendant_fraction_limit_of_normalized_counts (data : RuleData K)
    {rate : ℝ} {amplitude : Fin K → ℝ} (rate_positive : 0 < rate)
    (amplitude_positive : ∀ colour, 0 < amplitude colour)
    (convergence : ∀ initialColour,
      Tendsto (fun level =>
        (totalEdges { data with ι := initialColour } level : ℝ) / rate ^ level)
        atTop (nhds (amplitude initialColour)))
    (cellLevel : ℕ) (cellColour : Fin K) :
    Tendsto (fun level =>
      (totalEdges { data with ι := cellColour } level : ℝ) /
        (totalEdges data (level + cellLevel) : ℝ))
      atTop (nhds (amplitude cellColour / (rate ^ cellLevel * amplitude data.ι))) := by
  have root_convergence : Tendsto
      (fun level => (totalEdges data level : ℝ) / rate ^ level)
      atTop (nhds (amplitude data.ι)) := by
    simpa only using convergence data.ι
  have shifted_denominator := (root_convergence.comp
    (tendsto_add_atTop_nat cellLevel)).const_mul (rate ^ cellLevel)
  have ratio_limit := (convergence cellColour).div shifted_denominator
    (mul_pos (pow_pos rate_positive cellLevel) (amplitude_positive data.ι)).ne'
  convert ratio_limit using 1
  ext level
  dsimp only [Pi.div_apply, Function.comp_apply]
  rw [pow_add]
  field_simp

/-- Actual descendant fractions have strictly positive limits, and their
amplitudes satisfy the rule-by-rule mass consistency equation. -/
theorem eigs_descendant_fraction_limits (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ (rate : ℝ) (amplitude : Fin K → ℝ),
      0 < rate ∧ (∀ colour, 0 < amplitude colour) ∧
      (massMatrixR system.toRuleData).mulVec amplitude = rate • amplitude ∧
      ∀ cellLevel cellColour,
        Tendsto (fun level =>
          (totalEdges { system.toRuleData with ι := cellColour } level : ℝ) /
            (totalEdges system.toRuleData (level + cellLevel) : ℝ))
          atTop (nhds (amplitude cellColour /
            (rate ^ cellLevel * amplitude system.initCol))) := by
  obtain ⟨rate, amplitude, rate_positive, amplitude_positive, convergence⟩ :=
    descendant_edge_count_normalized_limits system rule_connected distance_positive
  exact ⟨rate, amplitude, rate_positive, amplitude_positive,
    mass_amplitude_eigenpair_of_descendant_limits system.toRuleData rate_positive convergence,
    descendant_fraction_limit_of_normalized_counts system.toRuleData
      rate_positive amplitude_positive convergence⟩

end EIGS
