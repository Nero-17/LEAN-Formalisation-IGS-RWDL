import RequestProject.Outlook.CorrectedSpectrum

/-! Correction-specific audit of old boundary-spectrum consequences.
The numerical mass/distance ratio is a formal expression; no geometric
random-cluster dimension identity or walk-dimension conjecture is asserted. -/

namespace Outlook

open Matrix Reduced

theorem correctedPositiveBoundary_trace_change :
    Matrix.trace (correctedPositiveBoundary pc)-Matrix.trace (ENodd pc)=4*pc-2 := by
  simp [Matrix.trace, correctedPositiveBoundary, ENodd, Fin.sum_univ_succ]
  linear_combination (-2)*pc_sq

theorem correctedNegativeBoundary_trace_change :
    Matrix.trace (ENeven pc)-Matrix.trace (correctedNegativeBoundary pc)=4*pc-2 := by
  simp [Matrix.trace, correctedNegativeBoundary, ENeven, Fin.sum_univ_succ]
  linear_combination (-2)*pc_sq

private theorem critical_above_three_fifths : (3/5:ℝ)<pc := by
  by_contra contrary
  have bound : pc≤3/5 := le_of_not_gt contrary
  nlinarith [pc_sq, pc_pos,
    mul_nonneg (sub_nonneg.mpr bound) (show 0≤(3/5:ℝ)+pc by linarith [pc_pos])]

theorem correctedCriticalEN_old_negative_eigenvalue_removed :
    (2*(pc:ℂ)) ∉ spectrum ℂ (EIGS.complexMatrix correctedCriticalEN) := by
  intro spectral
  rcases (correctedCriticalEN_mem_spectrum_iff _).mp spectral with zero | two | green | quadratic
  · have realZero : (2*pc:ℝ)=0 := by exact_mod_cast zero
    linarith [pc_pos]
  · have realTwo : (2*pc:ℝ)=2 := by exact_mod_cast two
    linarith [pc_lt_one]
  · have realGreen : (2*pc:ℝ)=2*pc^2 := by exact_mod_cast green
    nlinarith [pc_sq, critical_above_three_fifths]
  · have realQuadratic : (2*pc)^2+(6*pc-6)*(2*pc)+8*pc-4=0 := by
      exact_mod_cast quadratic
    nlinarith [pc_sq, critical_above_three_fifths]

theorem correctedCriticalEN_two_hasEig :
    HasEig (EIGS.complexMatrix correctedCriticalEN) 2 :=
  (correctedCriticalEN_hasEig_iff_mem_spectrum 2).mpr correctedCriticalEN_two_mem_spectrum

theorem correctedCriticalEN_hasEig_norm_le (eigenvalue : ℂ)
    (eigenvalueProperty : HasEig (EIGS.complexMatrix correctedCriticalEN) eigenvalue) :
    ‖eigenvalue‖≤2 :=
  correctedCriticalEN_spectrum_norm_le eigenvalue
    ((correctedCriticalEN_hasEig_iff_mem_spectrum eigenvalue).mp eigenvalueProperty)

noncomputable def correctedFormalDegreeRatio : ℝ :=
  Real.log (specRad (EM (pc:ℂ))) /
    Real.log (specRad (EIGS.complexMatrix correctedCriticalEN))

theorem correctedFormalDegreeRatio_eq_mass_distance_ratio :
    correctedFormalDegreeRatio = Real.log (specRad (EM (pc:ℂ)))/Real.log 2 := by
  rw [correctedFormalDegreeRatio, correctedCriticalEN_specRad]

/-- Exact directional asymmetry of the displayed, uncorrected boundary matrix. -/
theorem displayedEN_two_step_red_asymmetry (p : ℝ) :
    (EN p * EN p) 0 0 - (EN p * EN p) 1 1 = 4*p^6 := by
  norm_num [Matrix.mul_apply, EN, Fin.sum_univ_succ, Fin.ext_iff]
  ring

/-- Exact directional asymmetry persists in the adopted three-entry correction. -/
theorem correctedCriticalEN_two_step_red_asymmetry :
    (correctedCriticalEN * correctedCriticalEN) 0 0 -
      (correctedCriticalEN * correctedCriticalEN) 1 1 = 4*pc^7 := by
  norm_num [Matrix.mul_apply, correctedCriticalEN, EN, Fin.sum_univ_succ, Fin.ext_iff]
  ring

theorem correctedCriticalEN_two_step_red_asymmetry_positive :
    (correctedCriticalEN * correctedCriticalEN) 1 1 <
      (correctedCriticalEN * correctedCriticalEN) 0 0 := by
  have difference := correctedCriticalEN_two_step_red_asymmetry
  have positiveDifference : 0<4*pc^7 := by have := pc_pos; positivity
  linarith
end Outlook

#print axioms Outlook.correctedPositiveBoundary_trace_change
#print axioms Outlook.correctedNegativeBoundary_trace_change
#print axioms Outlook.correctedCriticalEN_old_negative_eigenvalue_removed
#print axioms Outlook.correctedCriticalEN_two_hasEig
#print axioms Outlook.correctedCriticalEN_hasEig_norm_le
#print axioms Outlook.correctedFormalDegreeRatio_eq_mass_distance_ratio
#print axioms Outlook.displayedEN_two_step_red_asymmetry
#print axioms Outlook.correctedCriticalEN_two_step_red_asymmetry
#print axioms Outlook.correctedCriticalEN_two_step_red_asymmetry_positive
