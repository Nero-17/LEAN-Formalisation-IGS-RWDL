import RequestProject.Section31.EIGSTwoColourActualSpectralParameters

/-! Rational certificates for the displayed actual two-colour parameters.
The quartic is supplied by the actual electrical-network identification.
The three finite iterates below use the actual rule-family Psi. Candidate. -/

namespace EIGS
open IGS.Sec33
noncomputable section
set_option maxHeartbeats 5000000

theorem twoColourResistanceRatio_numeric :
    (0.82001 : ℝ) < twoColourResistanceRatio ∧ twoColourResistanceRatio < 0.82002 := by
  have positive := twoColourResistanceRatio_spec.1
  have root := twoColourResistanceRatio_spec.2
  constructor
  · have constantPositive : (0 : ℝ) < 3 * (0.82001 : ℝ) ^ 3 +
        10 * (0.82001 : ℝ) ^ 2 + 4 * (0.82001 : ℝ) - 8 := by norm_num
    have factorPositive : 0 < 3 * twoColourResistanceRatio ^ 3 +
        (3 * (0.82001 : ℝ) + 10) * twoColourResistanceRatio ^ 2 +
        (3 * (0.82001 : ℝ) ^ 2 + 10 * (0.82001 : ℝ) + 4) * twoColourResistanceRatio +
        (3 * (0.82001 : ℝ) ^ 3 + 10 * (0.82001 : ℝ) ^ 2 + 4 * (0.82001 : ℝ) - 8) := by
      positivity
    by_contra notGreater
    have productNonpositive := mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (le_of_not_gt notGreater)) factorPositive.le
    nlinarith [productNonpositive]
  · have constantPositive : (0 : ℝ) < 3 * (0.82002 : ℝ) ^ 3 +
        10 * (0.82002 : ℝ) ^ 2 + 4 * (0.82002 : ℝ) - 8 := by norm_num
    have factorPositive : 0 < 3 * twoColourResistanceRatio ^ 3 +
        (3 * (0.82002 : ℝ) + 10) * twoColourResistanceRatio ^ 2 +
        (3 * (0.82002 : ℝ) ^ 2 + 10 * (0.82002 : ℝ) + 4) * twoColourResistanceRatio +
        (3 * (0.82002 : ℝ) ^ 3 + 10 * (0.82002 : ℝ) ^ 2 + 4 * (0.82002 : ℝ) - 8) := by
      positivity
    by_contra notLess
    have productNonnegative := mul_nonneg (sub_nonneg.mpr (le_of_not_gt notLess)) factorPositive.le
    nlinarith [productNonnegative]

theorem twoColourSystem_resistanceRate_numeric_precise :
    (1.106127 : ℝ) < twoColourSystem.resistanceSpectralRadius
      twoColourSystem_connected twoColourSystem_distancePositive ∧
    twoColourSystem.resistanceSpectralRadius
      twoColourSystem_connected twoColourSystem_distancePositive < 1.106129 := by
  have rateGreaterThanOne : 1 < twoColourSystem.resistanceSpectralRadius
      twoColourSystem_connected twoColourSystem_distancePositive := by
    rw [twoColourSystem_resistanceSpectralRadius]
    exact twoColourResistanceRate_greaterThanOne
  have root := twoColourSystem_resistancePolynomial
  have lowerSign : psiPoly (1.106127 : ℝ) < 0 := by norm_num [psiPoly]
  have upperSign : (0 : ℝ) < psiPoly 1.106129 := by norm_num [psiPoly]
  constructor
  · by_contra notGreater
    have monotone := psiPoly_strictMonoOn.monotoneOn
      (Set.mem_Ici.mpr rateGreaterThanOne.le)
      (Set.mem_Ici.mpr (by norm_num : (1 : ℝ) ≤ 1.106127)) (le_of_not_gt notGreater)
    rw [root] at monotone
    linarith
  · by_contra notLess
    have monotone := psiPoly_strictMonoOn.monotoneOn
      (Set.mem_Ici.mpr (by norm_num : (1 : ℝ) ≤ 1.106129))
      (Set.mem_Ici.mpr rateGreaterThanOne.le) (le_of_not_gt notLess)
    rw [root] at monotone
    linarith

theorem twoColourSystem_Psi_first_three_iterates :
    (twoColourSystem.ruleFamily twoColourSystem_connected).Psi^[1] (fun _ => 1) = ![1, 6 / 5] ∧
    (twoColourSystem.ruleFamily twoColourSystem_connected).Psi^[2] (fun _ => 1) = ![181 / 165, 187 / 140] ∧
    (twoColourSystem.ruleFamily twoColourSystem_connected).Psi^[3] (fun _ => 1) =
      ![188864377 / 155772540, 19567099 / 13235838] := by
  have first : (twoColourSystem.ruleFamily twoColourSystem_connected).Psi (fun _ => 1) = ![1, 6 / 5] := by
    rw [twoColourSystem_Psi _ (by intro colour; norm_num)]
    ext colour
    fin_cases colour <;> norm_num [example22Psi]
  have second : (twoColourSystem.ruleFamily twoColourSystem_connected).Psi ![1, 6 / 5] = ![181 / 165, 187 / 140] := by
    rw [twoColourSystem_Psi _ (by intro colour; fin_cases colour <;> norm_num)]
    ext colour
    fin_cases colour <;> norm_num [example22Psi]
  have third : (twoColourSystem.ruleFamily twoColourSystem_connected).Psi ![181 / 165, 187 / 140] =
      ![188864377 / 155772540, 19567099 / 13235838] := by
    rw [twoColourSystem_Psi _ (by intro colour; fin_cases colour <;> norm_num)]
    ext colour
    fin_cases colour <;> norm_num [example22Psi]
  refine ⟨?_, ?_, ?_⟩
  · exact first
  · change (twoColourSystem.ruleFamily twoColourSystem_connected).Psi
      ((twoColourSystem.ruleFamily twoColourSystem_connected).Psi (fun _ => 1)) = _
    rw [first, second]
  · change (twoColourSystem.ruleFamily twoColourSystem_connected).Psi
      ((twoColourSystem.ruleFamily twoColourSystem_connected).Psi
        ((twoColourSystem.ruleFamily twoColourSystem_connected).Psi (fun _ => 1))) = _
    rw [first, second, third]

theorem twoColourSystem_boxFormula_numeric :
    (2.4461 : ℝ) < Real.log (realMatrixSpectralRadius (massMatrixR twoColourSystem.toRuleData)) /
      Real.log (twoColourSystem.distanceSpectralRadius twoColourSystem_connected) ∧
    Real.log (realMatrixSpectralRadius (massMatrixR twoColourSystem.toRuleData)) /
      Real.log (twoColourSystem.distanceSpectralRadius twoColourSystem_connected) < 2.4462 := by
  rw [twoColourSystem_massSpectralRadius, twoColourSystem_distanceSpectralRadius]
  have logarithmSplit : Real.log (3 + Real.sqrt 6) = Real.log 2 + Real.log ((3 + Real.sqrt 6) / 2) := by
    rw [Real.log_div (by positivity) (by norm_num)]
    ring
  have lower := lt_log_halfM
  have upper := log_halfM_lt
  have logTwoLower := Real.log_two_gt_d9
  have logTwoUpper := Real.log_two_lt_d9
  constructor
  · apply (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    nlinarith
  · apply (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    nlinarith

theorem twoColourSystem_log_resistanceRate_precise :
    (0.100864 : ℝ) < Real.log (twoColourSystem.resistanceSpectralRadius
      twoColourSystem_connected twoColourSystem_distancePositive) ∧
    Real.log (twoColourSystem.resistanceSpectralRadius
      twoColourSystem_connected twoColourSystem_distancePositive) < 0.100867 := by
  obtain ⟨lower, upper⟩ := twoColourSystem_resistanceRate_numeric_precise
  have ratePositive : 0 < twoColourSystem.resistanceSpectralRadius
      twoColourSystem_connected twoColourSystem_distancePositive := by linarith
  have quotientPositive : 0 < (twoColourSystem.resistanceSpectralRadius
      twoColourSystem_connected twoColourSystem_distancePositive) ^ 55 / 256 := by positivity
  have lowerPower : (1.106127 : ℝ) ^ 55 < (twoColourSystem.resistanceSpectralRadius
      twoColourSystem_connected twoColourSystem_distancePositive) ^ 55 := by gcongr
  have upperPower : (twoColourSystem.resistanceSpectralRadius
      twoColourSystem_connected twoColourSystem_distancePositive) ^ 55 < (1.106129 : ℝ) ^ 55 := by gcongr
  norm_num at lowerPower upperPower
  have lowerLog : (0.00237 : ℝ) < Real.log ((twoColourSystem.resistanceSpectralRadius
      twoColourSystem_connected twoColourSystem_distancePositive) ^ 55 / 256) := by
    have elementary := one_sub_inv_le_log quotientPositive
    have inverseBound : 1 / ((twoColourSystem.resistanceSpectralRadius
        twoColourSystem_connected twoColourSystem_distancePositive) ^ 55 / 256) < (0.99763 : ℝ) := by
      rw [div_lt_iff₀ quotientPositive]
      nlinarith
    linarith
  have upperLog : Real.log ((twoColourSystem.resistanceSpectralRadius
      twoColourSystem_connected twoColourSystem_distancePositive) ^ 55 / 256) < (0.00249 : ℝ) := by
    have elementary := Real.log_le_sub_one_of_pos quotientPositive
    nlinarith
  have logarithmSplit : Real.log ((twoColourSystem.resistanceSpectralRadius
        twoColourSystem_connected twoColourSystem_distancePositive) ^ 55 / 256) =
      55 * Real.log (twoColourSystem.resistanceSpectralRadius
        twoColourSystem_connected twoColourSystem_distancePositive) - 8 * Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow]
    have log256 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
      rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
      norm_num
    rw [log256]
    norm_num
  have logTwoLower := Real.log_two_gt_d9
  have logTwoUpper := Real.log_two_lt_d9
  constructor <;> nlinarith

theorem twoColourSystem_resistanceDimensionFormula_numeric :
    (0.14551 : ℝ) < Real.log (twoColourSystem.resistanceSpectralRadius
      twoColourSystem_connected twoColourSystem_distancePositive) /
      Real.log (twoColourSystem.distanceSpectralRadius twoColourSystem_connected) ∧
    Real.log (twoColourSystem.resistanceSpectralRadius
      twoColourSystem_connected twoColourSystem_distancePositive) /
      Real.log (twoColourSystem.distanceSpectralRadius twoColourSystem_connected) < 0.14553 := by
  rw [twoColourSystem_distanceSpectralRadius]
  obtain ⟨lower, upper⟩ := twoColourSystem_log_resistanceRate_precise
  have logTwoLower := Real.log_two_gt_d9
  have logTwoUpper := Real.log_two_lt_d9
  constructor
  · apply (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    nlinarith
  · apply (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    nlinarith

end
end EIGS

#print axioms EIGS.twoColourResistanceRatio_numeric
#print axioms EIGS.twoColourSystem_resistanceRate_numeric_precise
#print axioms EIGS.twoColourSystem_Psi_first_three_iterates
#print axioms EIGS.twoColourSystem_boxFormula_numeric
#print axioms EIGS.twoColourSystem_resistanceDimensionFormula_numeric
