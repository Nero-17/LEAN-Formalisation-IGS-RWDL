import RequestProject.NonlinearPerronUnique
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

/-! Positive-matrix Perron existence from the proved Thomson compact argument. -/

namespace EIGS

open scoped BigOperators

variable {K : ℕ}

noncomputable def matrixRenormMap (matrix : Matrix (Fin K) (Fin K) ℝ)
    (matrix_nonneg : ∀ row column, 0 ≤ matrix row column) : RenormMap K where
  coord := fun row =>
    { F := Unit
      nonempty := inferInstance
      w := fun _ column => matrix row column
      w_nonneg := fun _ column => matrix_nonneg row column }

@[simp] theorem matrixRenormMap_apply (matrix : Matrix (Fin K) (Fin K) ℝ)
    (matrix_nonneg : ∀ row column, 0 ≤ matrix row column) (vector : Fin K → ℝ) :
    (matrixRenormMap matrix matrix_nonneg).apply vector = matrix.mulVec vector := by
  ext row
  simp [matrixRenormMap, RenormMap.apply, ThomsonData.eval, ThomsonData.energy,
    Matrix.mulVec, dotProduct]

theorem matrixRenormMap_strongly_positive
    (matrix : Matrix (Fin K) (Fin K) ℝ)
    (matrix_positive : ∀ row column, 0 < matrix row column) :
    ∀ vector : Fin K → ℝ, 0 ≤ vector → vector ≠ 0 →
      ∀ row, 0 < (matrixRenormMap matrix (fun row column =>
        (matrix_positive row column).le)).apply vector row := by
  have matrix_nonneg : ∀ row column, 0 ≤ matrix row column :=
    fun row column => (matrix_positive row column).le
  intro vector vector_nonneg vector_nonzero row
  obtain ⟨column, column_positive⟩ : ∃ column, 0 < vector column := by
    by_contra no_positive
    apply vector_nonzero
    ext column
    exact le_antisymm (le_of_not_gt (not_exists.mp no_positive column)) (vector_nonneg column)
  rw [matrixRenormMap_apply]
  exact lt_of_lt_of_le (mul_pos (matrix_positive row column) column_positive)
    (Finset.single_le_sum (fun index _ => mul_nonneg (matrix_nonneg row index)
      (vector_nonneg index)) (Finset.mem_univ column))

theorem positive_matrix_eigenpair (colours_positive : 0 < K)
    (matrix : Matrix (Fin K) (Fin K) ℝ)
    (matrix_positive : ∀ row column, 0 < matrix row column) :
    ∃ (vector : Fin K → ℝ) (rate : ℝ),
      (∀ colour, 0 < vector colour) ∧ 0 < rate ∧ (∑ colour, vector colour) = 1 ∧
        matrix.mulVec vector = rate • vector := by
  simpa only [matrixRenormMap_apply] using
    RenormMap.positive_eigenpair_of_strongly_positive
      (matrixRenormMap matrix (fun row column => (matrix_positive row column).le)) colours_positive
        (matrixRenormMap_strongly_positive matrix matrix_positive)

/-- Primitivity supplies a positive Perron eigenvector without an eigenpair
existence assumption. Positivity of a power and uniqueness of its normalized
positive eigenvector force the original matrix to preserve that ray. -/
theorem primitive_matrix_eigenpair (colours_positive : 0 < K)
    (matrix : Matrix (Fin K) (Fin K) ℝ) (primitive : matrix.IsPrimitive) :
    ∃ (vector : Fin K → ℝ) (rate : ℝ),
      (∀ colour, 0 < vector colour) ∧ 0 < rate ∧ (∑ colour, vector colour) = 1 ∧
        matrix.mulVec vector = rate • vector := by
  obtain ⟨exponent, exponent_positive, power_positive⟩ := primitive.exists_pos_pow
  obtain ⟨vector, power_rate, vector_positive, power_rate_positive, normalized, power_eigen⟩ :=
    positive_matrix_eigenpair colours_positive (matrix ^ exponent) power_positive
  have row_positive : ∀ row, ∃ column, 0 < matrix row column := by
    intro row
    by_contra no_positive
    have row_zero : ∀ column, matrix row column = 0 := fun column =>
      le_antisymm (le_of_not_gt (not_exists.mp no_positive column)) (primitive.nonneg row column)
    obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero exponent_positive.ne'
    have contradiction := power_positive row row
    simp [pow_succ', Matrix.mul_apply, row_zero] at contradiction
  have image_positive : ∀ row, 0 < matrix.mulVec vector row := by
    intro row
    obtain ⟨column, entry_positive⟩ := row_positive row
    exact lt_of_lt_of_le (mul_pos entry_positive (vector_positive column))
      (Finset.single_le_sum (fun index _ => mul_nonneg (primitive.nonneg row index)
        (vector_positive index).le) (Finset.mem_univ column))
  have image_eigen : (matrix ^ exponent).mulVec (matrix.mulVec vector) =
      power_rate • matrix.mulVec vector := by
    rw [Matrix.mulVec_mulVec, pow_mul_comm', ← Matrix.mulVec_mulVec, power_eigen,
      Matrix.mulVec_smul]
  let rate : ℝ := ∑ row, matrix.mulVec vector row
  have rate_positive : 0 < rate := Finset.sum_pos
    (fun row _ => image_positive row) ⟨⟨0, colours_positive⟩, Finset.mem_univ _⟩
  have image_normalized : (∑ row, (rate⁻¹ • matrix.mulVec vector) row) = 1 := by
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ rate_positive.ne'
  have normalized_eigen : (matrix ^ exponent).mulVec (rate⁻¹ • matrix.mulVec vector) =
      power_rate • (rate⁻¹ • matrix.mulVec vector) := by
    rw [Matrix.mulVec_smul, image_eigen, smul_comm]
  have same_vector : rate⁻¹ • matrix.mulVec vector = vector :=
    RenormMap.positive_eigenvector_unique_of_strongly_positive
      (matrixRenormMap (matrix ^ exponent) (fun row column => (power_positive row column).le))
      colours_positive
        (matrixRenormMap_strongly_positive (matrix ^ exponent) power_positive)
        (fun row => mul_pos (inv_pos.mpr rate_positive) (image_positive row))
        vector_positive image_normalized normalized
        (by simpa only [matrixRenormMap_apply] using normalized_eigen)
        (by simpa only [matrixRenormMap_apply] using power_eigen)
  refine ⟨vector, rate, vector_positive, rate_positive, normalized, ?_⟩
  have scaled := congrArg (fun values : Fin K → ℝ => rate • values) same_vector
  simpa only [smul_smul, mul_inv_cancel₀ rate_positive.ne', one_smul] using scaled

end EIGS
