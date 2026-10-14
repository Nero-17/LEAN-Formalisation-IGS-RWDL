import RequestProject.Section31.EIGSTwoColourMatrixSpectra
import RequestProject.Section31.EIGSTwoColourResistanceFormula
import RequestProject.Section31.EIGSTwoColourDistanceSpectrum
import RequestProject.Section2ResistanceSpectralRadius
import RequestProject.Section33.TwoColourExample

/-! Canonical spectral data and rigorous scalar numerical enclosures for
the literal Figure 3 EIGS, after actual graph-to-Psi identification. These
enclosures concern formulas in actual canonical spectral parameters. They
do not assert that the currently primitive-degree full-heat theorem applies:
the actual degree matrix of this example is not primitive. Candidate. -/

namespace EIGS
noncomputable section

def twoColourResistanceRatio : ℝ := Classical.choose example212_unique_positive_root

theorem twoColourResistanceRatio_spec : 0 < twoColourResistanceRatio ∧
    3 * twoColourResistanceRatio ^ 4 + 10 * twoColourResistanceRatio ^ 3 +
      4 * twoColourResistanceRatio ^ 2 - 8 * twoColourResistanceRatio - 3 = 0 :=
  (Classical.choose_spec example212_unique_positive_root).1

theorem twoColourResistanceRatio_lower : (3 : ℝ) / 4 < twoColourResistanceRatio := by
  have positive := twoColourResistanceRatio_spec.1
  have root := twoColourResistanceRatio_spec.2
  have factorPositive : 0 < 3 * twoColourResistanceRatio ^ 3 +
      (49 / 4 : ℝ) * twoColourResistanceRatio ^ 2 +
      (211 / 16 : ℝ) * twoColourResistanceRatio + 121 / 64 := by positivity
  have identity : (twoColourResistanceRatio - 3 / 4) *
      (3 * twoColourResistanceRatio ^ 3 + (49 / 4 : ℝ) * twoColourResistanceRatio ^ 2 +
        (211 / 16 : ℝ) * twoColourResistanceRatio + 121 / 64) = 405 / 256 := by
    nlinarith [root]
  by_contra notGreater
  have productNonpositive := mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (le_of_not_gt notGreater)) factorPositive.le
  linarith

def twoColourResistanceRate : ℝ :=
  (twoColourResistanceRatio + 2) * (twoColourResistanceRatio + 1) /
    (2 * twoColourResistanceRatio + 3)

theorem twoColourResistanceRate_greaterThanOne : 1 < twoColourResistanceRate := by
  have positive := twoColourResistanceRatio_spec.1
  have lower := twoColourResistanceRatio_lower
  unfold twoColourResistanceRate
  rw [lt_div_iff₀ (by positivity : 0 < 2 * twoColourResistanceRatio + 3)]
  nlinarith

theorem twoColourSystem_resistanceEigenpair :
    (twoColourSystem.ruleFamily twoColourSystem_connected).Psi ![twoColourResistanceRatio, 1] =
      twoColourResistanceRate • ![twoColourResistanceRatio, 1] := by
  have positive : ∀ colour : Fin 2, 0 < (![twoColourResistanceRatio, 1] : Fin 2 → ℝ) colour := by
    intro colour
    fin_cases colour
    · exact twoColourResistanceRatio_spec.1
    · norm_num
  rw [twoColourSystem_Psi _ positive]
  exact (example212_eigen_iff_quartic twoColourResistanceRatio_spec.1).2 twoColourResistanceRatio_spec.2

theorem twoColourSystem_resistanceSpectralRadius :
    twoColourSystem.resistanceSpectralRadius twoColourSystem_connected twoColourSystem_distancePositive =
      twoColourResistanceRate := by
  symm
  apply twoColourSystem.resistanceSpectralRadius_eq_of_positive_eigenpair twoColourSystem_connected
    twoColourSystem_distancePositive (zero_lt_one.trans twoColourResistanceRate_greaterThanOne)
    (eigenpair := twoColourSystem_resistanceEigenpair)
  intro colour
  fin_cases colour
  · exact twoColourResistanceRatio_spec.1
  · norm_num

theorem twoColourSystem_resistancePolynomial :
    IGS.Sec33.psiPoly (twoColourSystem.resistanceSpectralRadius
      twoColourSystem_connected twoColourSystem_distancePositive) = 0 := by
  rw [twoColourSystem_resistanceSpectralRadius]
  exact IGS.Sec33.psiPoly_of_tPoly twoColourResistanceRatio_spec.1 twoColourResistanceRatio_spec.2

theorem twoColourSystem_resistanceRate_numeric :
    (1.1061 : ℝ) < twoColourSystem.resistanceSpectralRadius
      twoColourSystem_connected twoColourSystem_distancePositive ∧
    twoColourSystem.resistanceSpectralRadius
      twoColourSystem_connected twoColourSystem_distancePositive < 1.1062 := by
  apply IGS.Sec33.rPsi_mem_Ioo
  · rw [twoColourSystem_resistanceSpectralRadius]
    exact twoColourResistanceRate_greaterThanOne
  · exact twoColourSystem_resistancePolynomial

theorem twoColourSystem_finiteSpectralFormula_numeric :
    (1.1159 : ℝ) <
      2 * Real.log (realMatrixSpectralRadius (massMatrixR twoColourSystem.toRuleData) /
        finiteRealMatrixSpectralRadius (degreeMatrix twoColourSystem)) /
        Real.log (realMatrixSpectralRadius (massMatrixR twoColourSystem.toRuleData) *
          twoColourSystem.resistanceSpectralRadius twoColourSystem_connected twoColourSystem_distancePositive) ∧
    2 * Real.log (realMatrixSpectralRadius (massMatrixR twoColourSystem.toRuleData) /
        finiteRealMatrixSpectralRadius (degreeMatrix twoColourSystem)) /
        Real.log (realMatrixSpectralRadius (massMatrixR twoColourSystem.toRuleData) *
          twoColourSystem.resistanceSpectralRadius twoColourSystem_connected twoColourSystem_distancePositive) < 1.1161 := by
  rw [twoColourSystem_massSpectralRadius, twoColourSystem_degreeSpectralRadius]
  apply IGS.Sec33.twoColour_spectral_finite_numeric
  · rw [twoColourSystem_resistanceSpectralRadius]
    exact twoColourResistanceRate_greaterThanOne
  · exact twoColourSystem_resistancePolynomial

theorem twoColourSystem_typicalSpectralFormula_numeric :
    (1.8876 : ℝ) <
      2 * Real.log (realMatrixSpectralRadius (massMatrixR twoColourSystem.toRuleData)) /
        Real.log (realMatrixSpectralRadius (massMatrixR twoColourSystem.toRuleData) *
          twoColourSystem.resistanceSpectralRadius twoColourSystem_connected twoColourSystem_distancePositive) ∧
    2 * Real.log (realMatrixSpectralRadius (massMatrixR twoColourSystem.toRuleData)) /
        Real.log (realMatrixSpectralRadius (massMatrixR twoColourSystem.toRuleData) *
          twoColourSystem.resistanceSpectralRadius twoColourSystem_connected twoColourSystem_distancePositive) < 1.8878 := by
  rw [twoColourSystem_massSpectralRadius]
  apply IGS.Sec33.twoColour_spectral_infinite_numeric
  · rw [twoColourSystem_resistanceSpectralRadius]
    exact twoColourResistanceRate_greaterThanOne
  · exact twoColourSystem_resistancePolynomial

end
end EIGS

#print axioms EIGS.twoColourSystem_resistanceEigenpair
#print axioms EIGS.twoColourSystem_resistanceSpectralRadius
#print axioms EIGS.twoColourSystem_resistanceRate_numeric
#print axioms EIGS.twoColourSystem_finiteSpectralFormula_numeric
#print axioms EIGS.twoColourSystem_typicalSpectralFormula_numeric
