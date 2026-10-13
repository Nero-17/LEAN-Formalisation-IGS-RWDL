import RequestProject.Section2MatrixPerron
import Mathlib.LinearAlgebra.Matrix.Reindex

namespace EIGS

open scoped BigOperators

/-- Perron existence for a primitive matrix on any nonempty finite index type. -/
theorem primitive_matrix_eigenpair_finite {index : Type*} [Fintype index]
    [DecidableEq index] [Nonempty index] (matrix : Matrix index index ℝ)
    (primitive : matrix.IsPrimitive) :
    ∃ (vector : index → ℝ) (rate : ℝ),
      (∀ row, 0 < vector row) ∧ 0 < rate ∧ (∑ row, vector row) = 1 ∧
        matrix.mulVec vector = rate • vector := by
  let indexing : index ≃ Fin (Fintype.card index) := Fintype.equivFin index
  let reindexing := Matrix.reindexAlgEquiv ℝ ℝ indexing
  have reindexed_primitive : (reindexing matrix).IsPrimitive := by
    refine ⟨fun row column => primitive.nonneg (indexing.symm row) (indexing.symm column), ?_⟩
    obtain ⟨exponent, exponent_positive, power_positive⟩ := primitive.exists_pos_pow
    refine ⟨exponent, exponent_positive, fun row column => ?_⟩
    have power_eq : reindexing matrix ^ exponent = reindexing (matrix ^ exponent) :=
      (map_pow reindexing matrix exponent).symm
    rw [power_eq]
    exact power_positive (indexing.symm row) (indexing.symm column)
  obtain ⟨vector, rate, vector_positive, rate_positive, normalized, eigenpair⟩ :=
    primitive_matrix_eigenpair Fintype.card_pos (reindexing matrix) reindexed_primitive
  refine ⟨vector ∘ indexing, rate, fun row => vector_positive (indexing row), rate_positive,
    ?_, ?_⟩
  · exact (indexing.sum_comp vector).trans normalized
  · ext row
    have coordinate_eigen := congrFun eigenpair (indexing row)
    change (∑ column, matrix row column * vector (indexing column)) =
      rate * vector (indexing row)
    have sum_eq := indexing.sum_comp
      (fun column => matrix row (indexing.symm column) * vector column)
    simp only [Equiv.symm_apply_apply] at sum_eq
    rw [sum_eq]
    simpa only [reindexing, Matrix.mulVec, dotProduct, Matrix.reindexAlgEquiv_apply,
      Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Pi.smul_apply, smul_eq_mul] using coordinate_eigen

end EIGS
