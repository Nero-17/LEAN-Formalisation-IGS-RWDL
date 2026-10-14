import RequestProject.Section31.FiniteMarkovCommonColumnContraction
import RequestProject.Section2FiniteSpectralRadius

/-! The actual stochastic conjugate of a primitive nonnegative matrix.
The positive eigenvector is obtained from the accepted finite Perron theorem;
its stochastic rows and positive-power common column are proved internally.
No normalized-power convergence is an input. Candidate source. -/

namespace EIGS
open scoped BigOperators
noncomputable section
variable {State : Type*} [Fintype State] [DecidableEq State]

def perronMarkovMatrix (matrix : Matrix State State ℝ) (vector : State → ℝ)
    (rate : ℝ) : Matrix State State ℝ :=
  fun first second => matrix first second * vector second / (rate * vector first)

theorem perronMarkovMatrix_nonnegative (matrix : Matrix State State ℝ) (vector : State → ℝ)
    (rate : ℝ) (nonnegative : ∀ first second, 0 ≤ matrix first second)
    (vectorPositive : ∀ state, 0 < vector state) (ratePositive : 0 < rate)
    (first second : State) :
    0 ≤ perronMarkovMatrix matrix vector rate first second :=
  div_nonneg (mul_nonneg (nonnegative first second) (vectorPositive second).le)
    (mul_pos ratePositive (vectorPositive first)).le

theorem perronMarkovMatrix_row_sum (matrix : Matrix State State ℝ) (vector : State → ℝ)
    (rate : ℝ) (vectorPositive : ∀ state, 0 < vector state) (ratePositive : 0 < rate)
    (eigenpair : matrix.mulVec vector = rate • vector) (first : State) :
    ∑ second, perronMarkovMatrix matrix vector rate first second = 1 := by
  have coordinate := congrFun eigenpair first
  change (∑ second, matrix first second * vector second) = rate * vector first at coordinate
  simp only [perronMarkovMatrix, ← Finset.sum_div, coordinate]
  exact div_self (mul_pos ratePositive (vectorPositive first)).ne'

theorem perronMarkovMatrix_power (matrix : Matrix State State ℝ) (vector : State → ℝ)
    (rate : ℝ) (vectorPositive : ∀ state, 0 < vector state) (ratePositive : 0 < rate)
    (power : ℕ) (first second : State) :
    ((perronMarkovMatrix matrix vector rate) ^ power) first second =
      (matrix ^ power) first second * vector second / (rate ^ power * vector first) := by
  induction power generalizing first second with
  | zero =>
      by_cases same : first = second
      · subst second
        simp [Matrix.one_apply, (vectorPositive first).ne']
      · simp [Matrix.one_apply, same]
  | succ power induction =>
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      simp only [induction, perronMarkovMatrix]
      calc
        (∑ middle, ((matrix ^ power) first middle * vector middle /
            (rate ^ power * vector first)) *
            (matrix middle second * vector second / (rate * vector middle))) =
            ∑ middle, ((matrix ^ power) first middle * matrix middle second) *
              vector second / (rate ^ (power + 1) * vector first) := by
          apply Finset.sum_congr rfl
          intro middle _
          field_simp [(vectorPositive middle).ne', (vectorPositive first).ne', ratePositive.ne', pow_succ]
          <;> ring
        _ = (∑ middle, (matrix ^ power) first middle * matrix middle second) *
            vector second / (rate ^ (power + 1) * vector first) := by
          rw [← Finset.sum_div, ← Finset.sum_mul]

theorem primitive_matrix_markov_common_column [Nonempty State]
    (matrix : Matrix State State ℝ) (primitive : matrix.IsPrimitive) :
    ∃ vector : State → ℝ, (∀ state, 0 < vector state) ∧ (∑ state, vector state) = 1 ∧
      matrix.mulVec vector = finiteRealMatrixSpectralRadius matrix • vector ∧
      (∀ first second, 0 ≤ perronMarkovMatrix matrix vector
        (finiteRealMatrixSpectralRadius matrix) first second) ∧
      (∀ first, ∑ second, perronMarkovMatrix matrix vector
        (finiteRealMatrixSpectralRadius matrix) first second = 1) ∧
      ∃ power : ℕ, 0 < power ∧ ∃ anchor commonMass, 0 < commonMass ∧ commonMass < 1 ∧
        ∀ first, commonMass ≤
          ((perronMarkovMatrix matrix vector (finiteRealMatrixSpectralRadius matrix)) ^ power)
            first anchor := by
  obtain ⟨vector, vectorPositive, ratePositive, normalized, eigenpair⟩ :=
    primitive_matrix_spectralRadius_eigenpair_finite matrix primitive
  refine ⟨vector, vectorPositive, normalized, eigenpair,
    perronMarkovMatrix_nonnegative matrix vector _ primitive.nonneg vectorPositive ratePositive,
    perronMarkovMatrix_row_sum matrix vector _ vectorPositive ratePositive eigenpair, ?_⟩
  obtain ⟨power, powerPositive, powerPositiveEntries⟩ := primitive.exists_pos_pow
  refine ⟨power, powerPositive, ?_⟩
  apply finite_positive_matrix_common_column
  intro first second
  rw [perronMarkovMatrix_power matrix vector _ vectorPositive ratePositive]
  exact div_pos (mul_pos (powerPositiveEntries first second) (vectorPositive second))
    (mul_pos (pow_pos ratePositive power) (vectorPositive first))

end
end EIGS

#print axioms EIGS.perronMarkovMatrix_nonnegative
#print axioms EIGS.perronMarkovMatrix_row_sum
#print axioms EIGS.perronMarkovMatrix_power
#print axioms EIGS.primitive_matrix_markov_common_column
