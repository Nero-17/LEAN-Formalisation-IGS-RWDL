import RequestProject.Outlook.EigenM
import RequestProject.Outlook.CorrectedSpectrum
import RequestProject.Outlook.FourColourRuleAudit

/-! Actual finite mean-matrix spectra and a formal logarithmic ratio.
This does not identify any random-cluster geometric or degree dimension.
The boundary calculation uses only the corrected critical matrix.
The elementary log estimates below reproduce the real-variable proof from
the legacy numerical source, without importing its old EN degree ratio. -/

namespace Outlook.FourColourMeanSpectrum

open Matrix Reduced
open scoped ENNReal

set_option maxHeartbeats 3000000

private theorem actual_mass_complex :
    EIGS.complexMatrix FourColourRuleAudit.meanLiveMass = EM (pc : ℂ) := by
  rw [FourColourRuleAudit.meanLiveMass_eq_EM]
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [EIGS.complexMatrix, EM] <;> push_cast <;> ring

private theorem mass_hasEig_iff_spectrum (value : ℂ) :
    HasEig (EM (pc : ℂ)) value ↔ value ∈ spectrum ℂ (EM (pc : ℂ)) := by
  rw [hasEig_iff_det, Matrix.mem_spectrum_iff_isRoot_charpoly]
  change _ = 0 ↔ (EM (pc : ℂ)).charpoly.eval value = 0
  rw [Matrix.eval_charpoly, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

theorem actual_mean_mass_spectralRadius :
    EIGS.realMatrixSpectralRadius FourColourRuleAudit.meanLiveMass = lamM := by
  have usual : spectralRadius ℂ (EM (pc : ℂ)) = ENNReal.ofReal lamM := by
    apply le_antisymm
    · apply iSup₂_le
      intro value spectral
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal
        (hasEig_EM_norm_le value ((mass_hasEig_iff_spectrum value).mpr spectral))
    · have lower := le_iSup₂
        (f := fun value (_membership : value ∈ spectrum ℂ (EM (pc : ℂ))) =>
          (‖value‖₊ : ℝ≥0∞)) (lamM : ℂ)
        ((mass_hasEig_iff_spectrum _).mp lamM_hasEig)
      change ENNReal.ofReal lamM ≤ ⨆ value ∈ spectrum ℂ (EM (pc : ℂ)), (‖value‖₊ : ℝ≥0∞)
      rw [ENNReal.ofReal_eq_coe_nnreal lamM_pos.le]
      simpa only [Complex.nnnorm_real, Real.nnnorm_of_nonneg lamM_pos.le] using lower
  rw [EIGS.realMatrixSpectralRadius, actual_mass_complex, usual,
    ENNReal.toReal_ofReal lamM_pos.le]

theorem actual_mean_mass_spectralRadius_approx :
    |EIGS.realMatrixSpectralRadius FourColourRuleAudit.meanLiveMass - 3.7303| < 1e-4 := by
  rw [actual_mean_mass_spectralRadius]
  exact lamM_approx

theorem actual_mean_boundary_spectralRadius :
    EIGS.realMatrixSpectralRadius FourColourRuleAudit.meanLiveBoundary = 2 := by
  rw [FourColourRuleAudit.meanLiveBoundary_eq_correctedCriticalEN]
  exact correctedCriticalEN_realMatrixSpectralRadius

theorem actual_mean_logarithmic_ratios_equal :
    Real.log (EIGS.realMatrixSpectralRadius FourColourRuleAudit.meanLiveMass) /
      Real.log (EIGS.realMatrixSpectralRadius FourColourRuleAudit.meanLiveBoundary) =
    Real.log (EIGS.realMatrixSpectralRadius FourColourRuleAudit.meanLiveMass) / Real.log 2 := by
  rw [actual_mean_boundary_spectralRadius]

/-- Five-term Taylor bound for `log (1 - u)`. -/
lemma log_one_sub_taylor (u : ℝ) (h0 : 0 ≤ u) (h1 : u < 1) :
    |Real.log (1 - u) + (u + u^2/2 + u^3/3 + u^4/4 + u^5/5)| ≤ u^6/(1-u) := by
  have habs : |u| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have h := Real.abs_log_sub_add_sum_range_le habs 5
  rw [abs_of_nonneg h0] at h
  simp [Finset.sum_range_succ] at h
  have e : Real.log (1 - u) + (u + u^2/2 + u^3/3 + u^4/4 + u^5/5)
      = u + u ^ 2 / (1 + 1) + u ^ 3 / (2 + 1) + u ^ 4 / (3 + 1) + u ^ 5 / (4 + 1)
        + Real.log (1 - u) := by ring
  rw [e]
  exact h

/-- `log` of a number of the form `4(1 - u)`. -/
lemma log_four_mul (u : ℝ) (hu : u < 1) :
    Real.log (4 * (1 - u)) = 2 * Real.log 2 + Real.log (1 - u) := by
  rw [Real.log_mul (by norm_num) (by linarith), show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
  push_cast
  ring

lemma log_lamM_lb : (1.31648549 : ℝ) < Real.log lamM := by
  have hu : (0:ℝ) ≤ 0.067427875 := by norm_num
  have hu1 : (0.067427875 : ℝ) < 1 := by norm_num
  have htay := log_one_sub_taylor 0.067427875 hu hu1
  rw [abs_le] at htay
  have hnum : (0.067427875 : ℝ) + 0.067427875^2/2 + 0.067427875^3/3 + 0.067427875^4/4
      + 0.067427875^5/5 + 0.067427875^6/(1 - 0.067427875) < 0.0698089 := by norm_num
  have hlog : (1.31648549 : ℝ) < 2 * Real.log 2 + Real.log (1 - 0.067427875) := by
    have h2 := Real.log_two_gt_d9
    linarith [htay.1]
  have hmono : Real.log (4 * (1 - 0.067427875)) ≤ Real.log lamM := by
    apply Real.log_le_log (by norm_num)
    have := lamM_lb
    norm_num
    linarith
  rw [log_four_mul _ hu1] at hmono
  linarith

lemma log_lamM_ub : Real.log lamM < 1.31648573 := by
  have hu : (0:ℝ) ≤ 0.06742785 := by norm_num
  have hu1 : (0.06742785 : ℝ) < 1 := by norm_num
  have htay := log_one_sub_taylor 0.06742785 hu hu1
  rw [abs_le] at htay
  have hnum : (0.0698086 : ℝ) < 0.06742785 + 0.06742785^2/2 + 0.06742785^3/3 + 0.06742785^4/4
      + 0.06742785^5/5 - 0.06742785^6/(1 - 0.06742785) := by norm_num
  have hlog : 2 * Real.log 2 + Real.log (1 - 0.06742785) < 1.31648573 := by
    have h2 := Real.log_two_lt_d9
    linarith [htay.2]
  have hmono : Real.log lamM ≤ Real.log (4 * (1 - 0.06742785)) := by
    apply Real.log_le_log lamM_pos
    have := lamM_ub
    norm_num
    linarith
  rw [log_four_mul _ hu1] at hmono
  linarith


theorem actual_mean_logarithmic_ratio_enclosure :
    1.89928 < Real.log (EIGS.realMatrixSpectralRadius FourColourRuleAudit.meanLiveMass) /
      Real.log (EIGS.realMatrixSpectralRadius FourColourRuleAudit.meanLiveBoundary) ∧
    Real.log (EIGS.realMatrixSpectralRadius FourColourRuleAudit.meanLiveMass) /
      Real.log (EIGS.realMatrixSpectralRadius FourColourRuleAudit.meanLiveBoundary) < 1.89929 := by
  rw [actual_mean_mass_spectralRadius, actual_mean_boundary_spectralRadius]
  have positive : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have lower := Real.log_two_gt_d9
  have upper := Real.log_two_lt_d9
  constructor
  · rw [lt_div_iff₀ positive]
    nlinarith [log_lamM_lb]
  · rw [div_lt_iff₀ positive]
    nlinarith [log_lamM_ub]

theorem actual_mean_logarithmic_ratio_approx :
    |Real.log (EIGS.realMatrixSpectralRadius FourColourRuleAudit.meanLiveMass) /
      Real.log (EIGS.realMatrixSpectralRadius FourColourRuleAudit.meanLiveBoundary) - 1.8993| < 1e-4 := by
  rw [abs_lt]
  constructor <;> linarith [actual_mean_logarithmic_ratio_enclosure]

end Outlook.FourColourMeanSpectrum

#print axioms Outlook.FourColourMeanSpectrum.actual_mean_mass_spectralRadius
#print axioms Outlook.FourColourMeanSpectrum.actual_mean_mass_spectralRadius_approx
#print axioms Outlook.FourColourMeanSpectrum.actual_mean_boundary_spectralRadius
#print axioms Outlook.FourColourMeanSpectrum.actual_mean_logarithmic_ratios_equal
#print axioms Outlook.FourColourMeanSpectrum.actual_mean_logarithmic_ratio_enclosure
#print axioms Outlook.FourColourMeanSpectrum.actual_mean_logarithmic_ratio_approx
