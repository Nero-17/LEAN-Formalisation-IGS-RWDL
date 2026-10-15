import RequestProject.Section31.EIGSTwoColourActualSpectralParameters

/-! Actual Figure 3 Psi iteration limits with the displayed eigenvector.
The normalized positive Perron theorem is applied to the original rule map,
and uniqueness identifies its witness with the actual quartic-root vector.
Candidate until whole-file acceptance. -/

namespace EIGS
open Filter Topology
open scoped BigOperators
noncomputable section

theorem twoColourSystem_Psi_normalized_iteration_limit :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      Tendsto (fun level => fun colour =>
        (twoColourSystem.ruleFamily twoColourSystem_connected).Psi^[level] (fun _ => 1) colour /
          twoColourResistanceRate ^ level) atTop
        (𝓝 (amplitude • ((twoColourResistanceRatio + 1)⁻¹ • ![twoColourResistanceRatio, 1]))) := by
  let normalizedVector : Fin 2 → ℝ := (twoColourResistanceRatio + 1)⁻¹ • ![twoColourResistanceRatio, 1]
  have ratioPositive := twoColourResistanceRatio_spec.1
  have denominatorPositive : 0 < twoColourResistanceRatio + 1 := by
    linarith [twoColourResistanceRatio_spec.1]
  have positive : ∀ colour, 0 < normalizedVector colour := by
    intro colour
    fin_cases colour <;> dsimp [normalizedVector] <;> positivity
  have normalized : (∑ colour, normalizedVector colour) = 1 := by
    dsimp [normalizedVector]
    simp only [Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [ne_of_gt denominatorPositive]
  have originalPositive : ∀ colour : Fin 2, 0 < (![twoColourResistanceRatio, 1] : Fin 2 → ℝ) colour := by
    intro colour
    fin_cases colour
    · exact twoColourResistanceRatio_spec.1
    · norm_num
  have normalizedEigenpair :
      (twoColourSystem.connectedRuleSystem twoColourSystem_connected).toRenormMap.apply normalizedVector =
        twoColourResistanceRate • normalizedVector := by
    change (twoColourSystem.ruleFamily twoColourSystem_connected).Psi normalizedVector = _
    rw [twoColourSystem_Psi _ positive]
    dsimp only [normalizedVector]
    rw [example22Psi_homogeneous,
      ← twoColourSystem_Psi _ originalPositive, twoColourSystem_resistanceEigenpair]
    ext colour
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨rate, amplitude, vector, ratePositive, amplitudePositive, vectorPositive, vectorNormalized,
      vectorEigenpair, convergence⟩ :=
    (twoColourSystem.connectedRuleSystem twoColourSystem_connected).distance_positive_normalized_iterate_limit
      (by norm_num) twoColourSystem_distancePositive
  obtain ⟨uniquePair, _, unique⟩ :=
    (twoColourSystem.connectedRuleSystem twoColourSystem_connected).distance_positive_normalized_eigenpair_exists_unique
      (by norm_num) twoColourSystem_distancePositive
  have pairEquality : (vector, rate) = (normalizedVector, twoColourResistanceRate) :=
    (unique (vector, rate) ⟨vectorPositive, ratePositive, vectorNormalized, vectorEigenpair⟩).trans
      (unique (normalizedVector, twoColourResistanceRate)
        ⟨positive, zero_lt_one.trans twoColourResistanceRate_greaterThanOne, normalized, normalizedEigenpair⟩).symm
  have vectorEquality := congrArg Prod.fst pairEquality
  have rateEquality := congrArg Prod.snd pairEquality
  dsimp only at vectorEquality rateEquality
  rw [vectorEquality, rateEquality] at convergence
  refine ⟨amplitude, amplitudePositive, ?_⟩
  exact convergence

theorem twoColourSystem_Psi_consecutive_second_coordinate_ratio_limit :
    Tendsto (fun level =>
      (twoColourSystem.ruleFamily twoColourSystem_connected).Psi^[level + 1] (fun _ => 1) 1 /
        (twoColourSystem.ruleFamily twoColourSystem_connected).Psi^[level] (fun _ => 1) 1)
      atTop (𝓝 twoColourResistanceRate) := by
  obtain ⟨amplitude, amplitudePositive, convergence⟩ := twoColourSystem_Psi_normalized_iteration_limit
  have coordinate := (tendsto_pi_nhds.mp convergence) (1 : Fin 2)
  have limitPositive : 0 < (amplitude • ((twoColourResistanceRatio + 1)⁻¹ •
      (![twoColourResistanceRatio, 1] : Fin 2 → ℝ))) 1 := by
    have denominatorPositive : 0 < twoColourResistanceRatio + 1 := by
      linarith [twoColourResistanceRatio_spec.1]
    change 0 < amplitude * ((twoColourResistanceRatio + 1)⁻¹ * 1)
    exact mul_pos amplitudePositive (mul_pos (inv_pos.mpr denominatorPositive) (by norm_num))
  have ratioConvergence := ((coordinate.comp (tendsto_add_atTop_nat 1)).div coordinate limitPositive.ne').mul_const
    twoColourResistanceRate
  simp only [div_self limitPositive.ne', one_mul] at ratioConvergence
  apply ratioConvergence.congr
  intro level
  change
    ((twoColourSystem.ruleFamily twoColourSystem_connected).Psi^[level + 1] (fun _ => 1) 1 /
      twoColourResistanceRate ^ (level + 1)) /
      ((twoColourSystem.ruleFamily twoColourSystem_connected).Psi^[level] (fun _ => 1) 1 /
        twoColourResistanceRate ^ level) * twoColourResistanceRate =
    (twoColourSystem.ruleFamily twoColourSystem_connected).Psi^[level + 1] (fun _ => 1) 1 /
      (twoColourSystem.ruleFamily twoColourSystem_connected).Psi^[level] (fun _ => 1) 1
  by_cases zero : (twoColourSystem.ruleFamily twoColourSystem_connected).Psi^[level] (fun _ => 1) 1 = 0
  · simp only [zero, zero_div, div_zero, zero_mul]
  · rw [pow_succ]
    field_simp [zero, ne_of_gt (zero_lt_one.trans twoColourResistanceRate_greaterThanOne)]

end
end EIGS

#print axioms EIGS.twoColourSystem_Psi_normalized_iteration_limit
#print axioms EIGS.twoColourSystem_Psi_consecutive_second_coordinate_ratio_limit
