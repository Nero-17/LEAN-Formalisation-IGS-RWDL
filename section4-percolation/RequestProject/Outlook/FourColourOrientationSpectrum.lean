import RequestProject.Outlook.FourColourOrientationCandidate
import RequestProject.Outlook.CorrectedSpectrum

/-! The spectrum of the adopted orientation correction. Reversing the green
cells changes the off-diagonal coupling of the two boundary blocks; the
characteristic polynomial is proved unchanged, rather than assumed so. -/

namespace Outlook.FourColourOrientationCandidate

open Matrix Reduced

set_option maxHeartbeats 2000000

private def orientedNegativeBoundary {R : Type*} [CommRing R] (p : R) : Matrix (Fin 3) (Fin 3) R :=
  !![4*p^2,2*p^4,0; 2*p^2,2*p^2,0; 0,0,2*p^2]

private def orientedBoundaryCoupling {R : Type*} [CommRing R] (p : R) : Matrix (Fin 3) (Fin 3) R :=
  !![0,0,2*p^5; 0,0,2*p^3; 0,0,0]

theorem orientedBoundary_det_char_eq (z : ℂ) :
    (z • (1 : Matrix (Fin 8) (Fin 8) ℂ) - EIGS.complexMatrix (candidateBoundaryMatrix pc)).det =
      (z • (1 : Matrix (Fin 8) (Fin 8) ℂ) - EIGS.complexMatrix correctedCriticalEN).det := by
  have critical : (pc : ℂ)^2 = 1 - (pc : ℂ) := by exact_mod_cast pc_sq
  have negativeIdentity :
      (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) - orientedNegativeBoundary (pc : ℂ)).det =
        (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) - correctedNegativeBoundary (pc : ℂ)).det := by
    simp [Matrix.det_fin_three, orientedNegativeBoundary, correctedNegativeBoundary]
  have blockIdentity :
      (z • (1 : Matrix (Fin 8) (Fin 8) ℂ) - EIGS.complexMatrix (candidateBoundaryMatrix pc)).submatrix
        correctedBoundaryIndex correctedBoundaryIndex =
      Matrix.fromBlocks
        (Matrix.fromBlocks
          (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) - correctedPositiveBoundary (pc : ℂ)) 0
          (-orientedBoundaryCoupling (pc : ℂ))
          (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) - orientedNegativeBoundary (pc : ℂ)))
        0 0 (z • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    ext row column
    rcases row with (row | row) | row <;>
      rcases column with (column | column) | column <;>
      fin_cases row <;> fin_cases column <;>
      norm_num [correctedBoundaryIndex, candidateBoundaryMatrix, EIGS.complexMatrix,
        correctedPositiveBoundary, orientedNegativeBoundary, orientedBoundaryCoupling,
        Matrix.fromBlocks, Matrix.one_apply, Fin.ext_iff]
  rw [← Matrix.det_submatrix_equiv_self correctedBoundaryIndex, blockIdentity,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂, negativeIdentity,
    correctedPositiveBoundary_det_char _ _ critical,
    correctedNegativeBoundary_det_char _ _ critical, correctedCriticalEN_det_char]
  simp
  ring

theorem orientedBoundary_spectrum_eq :
    spectrum ℂ (EIGS.complexMatrix (candidateBoundaryMatrix pc)) =
      spectrum ℂ (EIGS.complexMatrix correctedCriticalEN) := by
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.mem_spectrum_iff_isRoot_charpoly]
  change (EIGS.complexMatrix (candidateBoundaryMatrix pc)).charpoly.eval z = 0 ↔
    (EIGS.complexMatrix correctedCriticalEN).charpoly.eval z = 0
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
    orientedBoundary_det_char_eq]

theorem orientedBoundary_spectralRadius :
    spectralRadius ℂ (EIGS.complexMatrix (candidateBoundaryMatrix pc)) = ENNReal.ofReal 2 := by
  unfold spectralRadius
  rw [orientedBoundary_spectrum_eq]
  exact correctedCriticalEN_usual_spectralRadius

theorem actual_orientedMeanBoundary_spectralRadius :
    EIGS.realMatrixSpectralRadius candidateMeanBoundary = 2 := by
  rw [candidateMeanBoundary_eq, EIGS.realMatrixSpectralRadius, orientedBoundary_spectralRadius]
  norm_num

end Outlook.FourColourOrientationCandidate

#print axioms Outlook.FourColourOrientationCandidate.orientedBoundary_det_char_eq
#print axioms Outlook.FourColourOrientationCandidate.orientedBoundary_spectrum_eq
#print axioms Outlook.FourColourOrientationCandidate.orientedBoundary_spectralRadius
#print axioms Outlook.FourColourOrientationCandidate.actual_orientedMeanBoundary_spectralRadius
