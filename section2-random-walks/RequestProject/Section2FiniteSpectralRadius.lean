import RequestProject.Section2SpectralRadius
import RequestProject.Section2FinitePerron

/-! The same usual complex spectral radius on any nonempty finite state type,
including the actual incoming/outgoing colour states of the degree matrix. -/

namespace EIGS

open scoped BigOperators ENNReal

noncomputable def finiteComplexMatrix {index : Type*} [Fintype index] [DecidableEq index]
    (matrix : Matrix index index ℝ) : Matrix index index ℂ :=
  fun row column => (matrix row column : ℂ)

noncomputable def finiteRealMatrixSpectralRadius {index : Type*} [Fintype index] [DecidableEq index]
    (matrix : Matrix index index ℝ) : ℝ := (spectralRadius ℂ (finiteComplexMatrix matrix)).toReal

theorem finite_spectralRadius_eq_positive_eigenvalue {index : Type*} [Fintype index]
    [DecidableEq index] [Nonempty index] (matrix : Matrix index index ℝ)
    (matrix_nonnegative : ∀ row column, 0 ≤ matrix row column)
    (vector : index → ℝ) (rate : ℝ) (vector_positive : ∀ row, 0 < vector row)
    (rate_nonnegative : 0 ≤ rate) (eigenpair : matrix.mulVec vector = rate • vector) :
    spectralRadius ℂ (finiteComplexMatrix matrix) = ENNReal.ofReal rate := by
  let indexing : index ≃ Fin (Fintype.card index) := Fintype.equivFin index
  let reindexed := Matrix.reindexAlgEquiv ℝ ℝ indexing matrix
  have reindexed_eigenpair : reindexed.mulVec (vector ∘ indexing.symm) =
      rate • (vector ∘ indexing.symm) := by
    ext row
    change (∑ column, matrix (indexing.symm row) (indexing.symm column) *
      vector (indexing.symm column)) = rate * vector (indexing.symm row)
    rw [indexing.symm.sum_comp
      (fun column => matrix (indexing.symm row) column * vector column)]
    exact congrFun eigenpair (indexing.symm row)
  have complex_reindex : complexMatrix reindexed =
      Matrix.reindexAlgEquiv ℂ ℂ indexing (finiteComplexMatrix matrix) := rfl
  have spectra_eq := AlgEquiv.spectrum_eq (Matrix.reindexAlgEquiv ℂ ℂ indexing)
    (finiteComplexMatrix matrix)
  have radius_eq : spectralRadius ℂ (complexMatrix reindexed) =
      spectralRadius ℂ (finiteComplexMatrix matrix) := by
    unfold spectralRadius
    rw [complex_reindex, spectra_eq]
  exact radius_eq.symm.trans (spectralRadius_eq_positive_eigenvalue Fintype.card_pos reindexed
    (fun row column => matrix_nonnegative (indexing.symm row) (indexing.symm column))
    (vector ∘ indexing.symm) rate (fun row => vector_positive (indexing.symm row))
    rate_nonnegative reindexed_eigenpair)

theorem finiteRealMatrixSpectralRadius_eq_positive_eigenvalue {index : Type*} [Fintype index]
    [DecidableEq index] [Nonempty index] (matrix : Matrix index index ℝ)
    (matrix_nonnegative : ∀ row column, 0 ≤ matrix row column)
    (vector : index → ℝ) (rate : ℝ) (vector_positive : ∀ row, 0 < vector row)
    (rate_nonnegative : 0 ≤ rate) (eigenpair : matrix.mulVec vector = rate • vector) :
    finiteRealMatrixSpectralRadius matrix = rate := by
  rw [finiteRealMatrixSpectralRadius, finite_spectralRadius_eq_positive_eigenvalue matrix
    matrix_nonnegative vector rate vector_positive rate_nonnegative eigenpair,
    ENNReal.toReal_ofReal rate_nonnegative]

theorem primitive_matrix_spectralRadius_eigenpair_finite {index : Type*} [Fintype index]
    [DecidableEq index] [Nonempty index] (matrix : Matrix index index ℝ)
    (primitive : matrix.IsPrimitive) :
    ∃ vector : index → ℝ, (∀ row, 0 < vector row) ∧
      0 < finiteRealMatrixSpectralRadius matrix ∧ (∑ row, vector row) = 1 ∧
      matrix.mulVec vector = finiteRealMatrixSpectralRadius matrix • vector := by
  obtain ⟨vector, rate, vector_positive, rate_positive, normalized, eigenpair⟩ :=
    primitive_matrix_eigenpair_finite matrix primitive
  have spectral_eq := finiteRealMatrixSpectralRadius_eq_positive_eigenvalue matrix primitive.nonneg
    vector rate vector_positive rate_positive.le eigenpair
  exact ⟨vector, vector_positive, spectral_eq.symm ▸ rate_positive, normalized,
    spectral_eq.symm ▸ eigenpair⟩

end EIGS

#print axioms EIGS.finite_spectralRadius_eq_positive_eigenvalue
#print axioms EIGS.primitive_matrix_spectralRadius_eigenpair_finite
