import RequestProject.Section2MatrixPerron
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Complex.Basic

/-! The usual complex spectral radius of a nonnegative real matrix with a
strictly positive eigenvector. The eigenpair is constructed separately, rather
than assumed in the positive-matrix corollary. -/

namespace EIGS

open scoped BigOperators ENNReal

variable {K : ℕ}

noncomputable def complexMatrix (matrix : Matrix (Fin K) (Fin K) ℝ) :
    Matrix (Fin K) (Fin K) ℂ := fun row column => (matrix row column : ℂ)

noncomputable def realMatrixSpectralRadius (matrix : Matrix (Fin K) (Fin K) ℝ) : ℝ :=
  (spectralRadius ℂ (complexMatrix matrix)).toReal

theorem complex_eigenvalue_norm_le_positive_eigenvalue
    (matrix : Matrix (Fin K) (Fin K) ℝ)
    (matrix_nonnegative : ∀ row column, 0 ≤ matrix row column)
    (vector : Fin K → ℝ) (rate : ℝ)
    (vector_positive : ∀ colour, 0 < vector colour)
    (positive_eigenpair : matrix.mulVec vector = rate • vector)
    (eigenvalue : ℂ) (eigenvector : Fin K → ℂ)
    (eigenvector_nonzero : eigenvector ≠ 0)
    (complex_eigenpair : (complexMatrix matrix).mulVec eigenvector = eigenvalue • eigenvector) :
    ‖eigenvalue‖ ≤ rate := by
  classical
  obtain ⟨nonzero_coordinate, coordinate_nonzero⟩ : ∃ colour, eigenvector colour ≠ 0 := by
    by_contra none
    push_neg at none
    exact eigenvector_nonzero (funext none)
  have univ_nonempty : (Finset.univ : Finset (Fin K)).Nonempty :=
    ⟨nonzero_coordinate, Finset.mem_univ _⟩
  obtain ⟨maximum_coordinate, _, maximum_ratio⟩ := Finset.univ.exists_max_image
    (fun colour => ‖eigenvector colour‖ / vector colour) univ_nonempty
  have maximum_positive : 0 < ‖eigenvector maximum_coordinate‖ / vector maximum_coordinate :=
    (div_pos (norm_pos_iff.mpr coordinate_nonzero) (vector_positive nonzero_coordinate)).trans_le
      (maximum_ratio nonzero_coordinate (Finset.mem_univ _))
  have maximum_norm_positive : 0 < ‖eigenvector maximum_coordinate‖ := by
    have product_positive := mul_pos maximum_positive (vector_positive maximum_coordinate)
    simpa only [div_mul_cancel₀ _ (vector_positive maximum_coordinate).ne'] using product_positive
  have coordinate_bound : ∀ colour,
      ‖eigenvector colour‖ ≤
        (‖eigenvector maximum_coordinate‖ / vector maximum_coordinate) * vector colour := by
    intro colour
    exact (div_le_iff₀ (vector_positive colour)).mp
      (maximum_ratio colour (Finset.mem_univ _))
  have row_bound : ‖eigenvalue‖ * ‖eigenvector maximum_coordinate‖ ≤
      rate * ‖eigenvector maximum_coordinate‖ := by
    calc
      ‖eigenvalue‖ * ‖eigenvector maximum_coordinate‖ =
          ‖eigenvalue * eigenvector maximum_coordinate‖ := (norm_mul _ _).symm
      _ = ‖∑ column, (matrix maximum_coordinate column : ℂ) * eigenvector column‖ := by
        simpa only [Matrix.mulVec, dotProduct, complexMatrix, Pi.smul_apply, smul_eq_mul]
          using congrArg norm (congrFun complex_eigenpair maximum_coordinate).symm
      _ ≤ ∑ column, ‖(matrix maximum_coordinate column : ℂ) * eigenvector column‖ :=
        norm_sum_le _ _
      _ = ∑ column, matrix maximum_coordinate column * ‖eigenvector column‖ := by
        apply Finset.sum_congr rfl
        intro column _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (matrix_nonnegative maximum_coordinate column)]
      _ ≤ ∑ column, matrix maximum_coordinate column *
          ((‖eigenvector maximum_coordinate‖ / vector maximum_coordinate) * vector column) :=
        Finset.sum_le_sum (fun column _ =>
          mul_le_mul_of_nonneg_left (coordinate_bound column)
            (matrix_nonnegative maximum_coordinate column))
      _ = (‖eigenvector maximum_coordinate‖ / vector maximum_coordinate) *
          (rate * vector maximum_coordinate) := by
        have equation := congrFun positive_eigenpair maximum_coordinate
        simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at equation
        rw [← equation, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro column _
        ring
      _ = rate * ‖eigenvector maximum_coordinate‖ := by
        field_simp [(vector_positive maximum_coordinate).ne']
  exact le_of_mul_le_mul_right row_bound maximum_norm_positive

theorem complex_spectrum_norm_le_positive_eigenvalue
    (matrix : Matrix (Fin K) (Fin K) ℝ)
    (matrix_nonnegative : ∀ row column, 0 ≤ matrix row column)
    (vector : Fin K → ℝ) (rate : ℝ)
    (vector_positive : ∀ colour, 0 < vector colour)
    (positive_eigenpair : matrix.mulVec vector = rate • vector)
    (eigenvalue : ℂ) (spectral : eigenvalue ∈ spectrum ℂ (complexMatrix matrix)) :
    ‖eigenvalue‖ ≤ rate := by
  have operator_spectral : eigenvalue ∈ spectrum ℂ (complexMatrix matrix).toLin' := by
    simpa only [Matrix.spectrum_toLin'] using spectral
  obtain ⟨eigenvector, eigenvector_property⟩ :=
    (Module.End.HasEigenvalue.of_mem_spectrum operator_spectral).exists_hasEigenvector
  exact complex_eigenvalue_norm_le_positive_eigenvalue matrix matrix_nonnegative vector rate
    vector_positive positive_eigenpair eigenvalue eigenvector eigenvector_property.2
      eigenvector_property.apply_eq_smul

theorem positive_eigenvalue_mem_complex_spectrum (colours_positive : 0 < K)
    (matrix : Matrix (Fin K) (Fin K) ℝ) (vector : Fin K → ℝ) (rate : ℝ)
    (vector_positive : ∀ colour, 0 < vector colour)
    (positive_eigenpair : matrix.mulVec vector = rate • vector) :
    (rate : ℂ) ∈ spectrum ℂ (complexMatrix matrix) := by
  have eigenvector_nonzero : (fun colour => (vector colour : ℂ)) ≠ 0 := by
    intro zero_vector
    have coordinate_zero := congrFun zero_vector ⟨0, colours_positive⟩
    change (vector ⟨0, colours_positive⟩ : ℂ) = 0 at coordinate_zero
    have real_zero : vector ⟨0, colours_positive⟩ = 0 := by exact_mod_cast coordinate_zero
    exact (vector_positive ⟨0, colours_positive⟩).ne' real_zero
  have complex_eigenpair : (complexMatrix matrix).mulVec (fun colour => (vector colour : ℂ)) =
      (rate : ℂ) • (fun colour => (vector colour : ℂ)) := by
    ext row
    have equation := congrFun positive_eigenpair row
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at equation ⊢
    simpa only [complexMatrix, ← Complex.ofReal_mul, ← Complex.ofReal_sum] using
      congrArg Complex.ofReal equation
  have eigenvector_property : Module.End.HasEigenvector (complexMatrix matrix).toLin' (rate : ℂ)
      (fun colour => (vector colour : ℂ)) :=
    ⟨Module.End.mem_eigenspace_iff.mpr complex_eigenpair, eigenvector_nonzero⟩
  simpa only [Matrix.spectrum_toLin'] using
    (Module.End.hasEigenvalue_of_hasEigenvector eigenvector_property).mem_spectrum

theorem spectralRadius_eq_positive_eigenvalue (colours_positive : 0 < K)
    (matrix : Matrix (Fin K) (Fin K) ℝ)
    (matrix_nonnegative : ∀ row column, 0 ≤ matrix row column)
    (vector : Fin K → ℝ) (rate : ℝ)
    (vector_positive : ∀ colour, 0 < vector colour) (rate_nonnegative : 0 ≤ rate)
    (positive_eigenpair : matrix.mulVec vector = rate • vector) :
    spectralRadius ℂ (complexMatrix matrix) = ENNReal.ofReal rate := by
  apply le_antisymm
  · apply iSup₂_le
    intro eigenvalue spectral
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (complex_spectrum_norm_le_positive_eigenvalue matrix
      matrix_nonnegative vector rate vector_positive positive_eigenpair eigenvalue spectral)
  · have spectral := positive_eigenvalue_mem_complex_spectrum colours_positive matrix
      vector rate vector_positive positive_eigenpair
    have lower := le_iSup₂ (f := fun value (_membership : value ∈ spectrum ℂ (complexMatrix matrix)) =>
      (‖value‖₊ : ℝ≥0∞)) (rate : ℂ) spectral
    rw [← ENNReal.ofReal_coe_nnreal] at lower
    simpa only [coe_nnnorm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg rate_nonnegative] using lower

theorem realMatrixSpectralRadius_eq_positive_eigenvalue (colours_positive : 0 < K)
    (matrix : Matrix (Fin K) (Fin K) ℝ)
    (matrix_nonnegative : ∀ row column, 0 ≤ matrix row column)
    (vector : Fin K → ℝ) (rate : ℝ)
    (vector_positive : ∀ colour, 0 < vector colour) (rate_nonnegative : 0 ≤ rate)
    (positive_eigenpair : matrix.mulVec vector = rate • vector) :
    realMatrixSpectralRadius matrix = rate := by
  rw [realMatrixSpectralRadius, spectralRadius_eq_positive_eigenvalue colours_positive matrix
    matrix_nonnegative vector rate vector_positive rate_nonnegative positive_eigenpair,
    ENNReal.toReal_ofReal rate_nonnegative]

theorem positive_matrix_spectralRadius_eigenpair (colours_positive : 0 < K)
    (matrix : Matrix (Fin K) (Fin K) ℝ)
    (matrix_positive : ∀ row column, 0 < matrix row column) :
    ∃ vector : Fin K → ℝ, (∀ colour, 0 < vector colour) ∧
      0 < realMatrixSpectralRadius matrix ∧ (∑ colour, vector colour) = 1 ∧
      matrix.mulVec vector = realMatrixSpectralRadius matrix • vector := by
  obtain ⟨vector, rate, vector_positive, rate_positive, normalized, eigenpair⟩ :=
    positive_matrix_eigenpair colours_positive matrix matrix_positive
  have spectral_eq := realMatrixSpectralRadius_eq_positive_eigenvalue colours_positive matrix
    (fun row column => (matrix_positive row column).le) vector rate vector_positive
      rate_positive.le eigenpair
  exact ⟨vector, vector_positive, spectral_eq.symm ▸ rate_positive, normalized,
    spectral_eq.symm ▸ eigenpair⟩

end EIGS

#print axioms EIGS.spectralRadius_eq_positive_eigenvalue
#print axioms EIGS.positive_matrix_spectralRadius_eigenpair
