import RequestProject.Outlook.CorrectedMatrices
import RequestProject.Section2SpectralRadius

/-! The spectrum of the user-adopted critical boundary matrix, proved afresh.
The displayed uncorrected EN and its old block formulas are not modified. -/

namespace Outlook

open Matrix Reduced
open scoped ENNReal

set_option maxHeartbeats 2000000

private theorem correctedCritical_complex_relation : (pc:ℂ)^2 = 1-(pc:ℂ) := by
  exact_mod_cast pc_sq

private theorem correctedCritical_lower : (3/5:ℝ) < pc := by
  by_contra contrary
  have bound : pc ≤ 3/5 := le_of_not_gt contrary
  nlinarith [pc_sq, pc_pos,
    mul_nonneg (sub_nonneg.mpr bound) (show 0 ≤ (3/5:ℝ)+pc by linarith [pc_pos])]

private theorem corrected_quadratic_root_norm_le_two (linearCoefficient constantCoefficient : ℝ)
    (lowerLinear : -4 < linearCoefficient) (upperLinear : linearCoefficient < 4)
    (positiveAtTwo : 0 < 4+2*linearCoefficient+constantCoefficient)
    (positiveAtMinusTwo : 0 < 4-2*linearCoefficient+constantCoefficient)
    (constantBound : constantCoefficient ≤ 4) (root : ℂ)
    (rootEquation : root^2+(linearCoefficient:ℂ)*root+(constantCoefficient:ℂ)=0) :
    ‖root‖ ≤ 2 := by
  rcases quad_root_cases linearCoefficient constantCoefficient root rootEquation with
    ⟨realRoot, rootReal, realEquation⟩ | normSquare
  · rw [rootReal, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor
    · by_contra contrary
      push_neg at contrary
      have below : realRoot < -2 := by linarith
      nlinarith [mul_pos (show (0:ℝ) < -(realRoot+2) by linarith)
        (show (0:ℝ) < -(realRoot+linearCoefficient-2) by linarith)]
    · by_contra contrary
      push_neg at contrary
      nlinarith [mul_pos (show (0:ℝ) < realRoot-2 by linarith)
        (show (0:ℝ) < realRoot+linearCoefficient+2 by linarith)]
  · nlinarith [normSquare, norm_nonneg root]
noncomputable def correctedPositiveBoundary {R : Type*} [CommRing R] (p : R) : Matrix (Fin 3) (Fin 3) R :=
  !![4*p^2, 2*p^4, 2*p^5; 2*p^2, 2*p^2, 2*p^3; 2*p^2, 0, 2*p]

noncomputable def correctedNegativeBoundary {R : Type*} [CommRing R] (p : R) : Matrix (Fin 3) (Fin 3) R :=
  !![4*p^2, 2*p^4, 2*p^5; 2*p^2, 2*p^2, 2*p^3; 0, 0, 2*p^2]

def correctedBoundaryIndex : ((Fin 3 ⊕ Fin 3) ⊕ Fin 2) ≃ Fin 8 where
  toFun := Sum.elim (Sum.elim
    (fun index => ⟨2*index.val, by omega⟩)
    (fun index => ⟨2*index.val+1, by omega⟩))
    (fun index => ⟨index.val+6, by omega⟩)
  invFun := ![Sum.inl (Sum.inl 0), Sum.inl (Sum.inr 0), Sum.inl (Sum.inl 1), Sum.inl (Sum.inr 1),
    Sum.inl (Sum.inl 2), Sum.inl (Sum.inr 2), Sum.inr 0, Sum.inr 1]
  left_inv := by
    intro index
    rcases index with (index | index) | index <;> fin_cases index <;> rfl
  right_inv := by
    intro index
    fin_cases index <;> rfl

theorem correctedPositiveBoundary_det_char {R : Type*} [CommRing R] (p z : R)
    (critical : p^2 = 1-p) :
    (z • (1 : Matrix (Fin 3) (Fin 3) R) - correctedPositiveBoundary p).det =
      (z-2) * (z-2*p^2)^2 := by
  simp [Matrix.det_fin_three, correctedPositiveBoundary]
  linear_combination (-2*z^2 + (-4*p^5-4*p^3+8*p^2)*z+8*p^5-8*p^4) * critical

theorem correctedNegativeBoundary_det_char {R : Type*} [CommRing R] (p z : R)
    (critical : p^2 = 1-p) :
    (z • (1 : Matrix (Fin 3) (Fin 3) R) - correctedNegativeBoundary p).det =
      (z-2*p^2) * (z^2+(6*p-6)*z+8*p-4) := by
  simp [Matrix.det_fin_three, correctedNegativeBoundary]
  linear_combination ((z-2*p^2)*(-6*z-4*p^4+4*p^3+4*p-4)) * critical

theorem correctedCriticalEN_det_char (z : ℂ) :
    (z • (1 : Matrix (Fin 8) (Fin 8) ℂ) - EIGS.complexMatrix correctedCriticalEN).det =
      z^2 * (z-2) * (z-2*(pc:ℂ)^2)^3 *
        (z^2+(6*(pc:ℂ)-6)*z+8*(pc:ℂ)-4) := by
  have blockIdentity :
      (z • (1 : Matrix (Fin 8) (Fin 8) ℂ) - EIGS.complexMatrix correctedCriticalEN).submatrix
        correctedBoundaryIndex correctedBoundaryIndex =
      Matrix.fromBlocks
        (Matrix.fromBlocks
          (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) - correctedPositiveBoundary (pc:ℂ)) 0 0
          (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) - correctedNegativeBoundary (pc:ℂ)))
        0 0 (z • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    ext row column
    rcases row with (row | row) | row <;>
      rcases column with (column | column) | column <;>
      fin_cases row <;> fin_cases column <;>
      norm_num [correctedBoundaryIndex, correctedCriticalEN, EN, EIGS.complexMatrix,
        correctedPositiveBoundary, correctedNegativeBoundary, Matrix.fromBlocks, Matrix.one_apply, Fin.ext_iff]
  rw [← Matrix.det_submatrix_equiv_self correctedBoundaryIndex, blockIdentity,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁,
    correctedPositiveBoundary_det_char _ _ correctedCritical_complex_relation,
    correctedNegativeBoundary_det_char _ _ correctedCritical_complex_relation]
  simp
  ring

theorem correctedCriticalEN_mem_spectrum_iff (z : ℂ) :
    z ∈ spectrum ℂ (EIGS.complexMatrix correctedCriticalEN) ↔
      z=0 ∨ z=2 ∨ z=2*(pc:ℂ)^2 ∨ z^2+(6*(pc:ℂ)-6)*z+8*(pc:ℂ)-4=0 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  change (EIGS.complexMatrix correctedCriticalEN).charpoly.eval z = 0 ↔ _
  rw [Matrix.eval_charpoly, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
    correctedCriticalEN_det_char]
  simp only [mul_eq_zero, pow_eq_zero_iff (by decide : (2:ℕ)≠0),
    pow_eq_zero_iff (by decide : (3:ℕ)≠0), sub_eq_zero]
  tauto

theorem correctedCriticalEN_spectrum_norm_le (z : ℂ)
    (spectral : z ∈ spectrum ℂ (EIGS.complexMatrix correctedCriticalEN)) : ‖z‖ ≤ 2 := by
  rcases (correctedCriticalEN_mem_spectrum_iff z).mp spectral with zero | two | green | quadratic
  · simp [zero]
  · simp [two]
  · rw [green]
    have realIdentity : (2:ℂ)*(pc:ℂ)^2 = ((2*pc^2:ℝ):ℂ) := by push_cast; ring
    rw [realIdentity, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [pc_sq, pc_pos]
  · apply corrected_quadratic_root_norm_le_two (6*pc-6) (8*pc-4) (by linarith [correctedCritical_lower])
      (by linarith [pc_lt_one]) (by linarith [correctedCritical_lower]) (by linarith [pc_lt_one])
      (by linarith [pc_lt_one]) z
    push_cast
    linear_combination quadratic

theorem correctedCriticalEN_two_mem_spectrum :
    (2:ℂ) ∈ spectrum ℂ (EIGS.complexMatrix correctedCriticalEN) :=
  (correctedCriticalEN_mem_spectrum_iff 2).mpr (Or.inr (Or.inl rfl))

theorem correctedCriticalEN_usual_spectralRadius :
    spectralRadius ℂ (EIGS.complexMatrix correctedCriticalEN) = ENNReal.ofReal 2 := by
  apply le_antisymm
  · apply iSup₂_le
    intro eigenvalue spectral
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (correctedCriticalEN_spectrum_norm_le eigenvalue spectral)
  · have lower := le_iSup₂
      (f := fun value (_membership : value ∈ spectrum ℂ (EIGS.complexMatrix correctedCriticalEN)) =>
        (‖value‖₊ : ℝ≥0∞)) (2:ℂ) correctedCriticalEN_two_mem_spectrum
    norm_num at lower ⊢
    exact lower

theorem correctedCriticalEN_realMatrixSpectralRadius :
    EIGS.realMatrixSpectralRadius correctedCriticalEN = 2 := by
  rw [EIGS.realMatrixSpectralRadius, correctedCriticalEN_usual_spectralRadius]
  norm_num

theorem correctedCriticalEN_hasEig_iff_mem_spectrum (z : ℂ) :
    HasEig (EIGS.complexMatrix correctedCriticalEN) z ↔
      z ∈ spectrum ℂ (EIGS.complexMatrix correctedCriticalEN) := by
  rw [hasEig_iff_det, Matrix.mem_spectrum_iff_isRoot_charpoly]
  change _=0 ↔ (EIGS.complexMatrix correctedCriticalEN).charpoly.eval z=0
  rw [Matrix.eval_charpoly, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

theorem correctedCriticalEN_isGreatest :
    IsGreatest {radius : ℝ | ∃ eigenvalue : ℂ,
      HasEig (EIGS.complexMatrix correctedCriticalEN) eigenvalue ∧ ‖eigenvalue‖=radius} 2 := by
  constructor
  · exact ⟨2, (correctedCriticalEN_hasEig_iff_mem_spectrum 2).mpr
      correctedCriticalEN_two_mem_spectrum, by norm_num⟩
  · rintro radius ⟨eigenvalue, eigenvalueProperty, rfl⟩
    exact correctedCriticalEN_spectrum_norm_le eigenvalue
      ((correctedCriticalEN_hasEig_iff_mem_spectrum eigenvalue).mp eigenvalueProperty)

theorem correctedCriticalEN_specRad : specRad (EIGS.complexMatrix correctedCriticalEN)=2 :=
  specRad_eq_of_isGreatest correctedCriticalEN_isGreatest
end Outlook

#print axioms Outlook.correctedPositiveBoundary_det_char
#print axioms Outlook.correctedNegativeBoundary_det_char
#print axioms Outlook.correctedCriticalEN_det_char
#print axioms Outlook.correctedCriticalEN_mem_spectrum_iff
#print axioms Outlook.correctedCriticalEN_spectrum_norm_le
#print axioms Outlook.correctedCriticalEN_usual_spectralRadius
#print axioms Outlook.correctedCriticalEN_realMatrixSpectralRadius
#print axioms Outlook.correctedCriticalEN_isGreatest
#print axioms Outlook.correctedCriticalEN_specRad
