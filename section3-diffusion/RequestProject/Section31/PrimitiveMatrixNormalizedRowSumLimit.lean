import RequestProject.Section31.PrimitivePerronMarkovConjugacy
import RequestProject.Section31.FiniteMarkovPowerConvergence

/-! Actual normalized row-sum convergence of an arbitrary finite primitive
matrix. The proof constructs its stochastic conjugate and uses the proved
Doeblin convergence, rather than assuming Perron power convergence.
Candidate source. -/

namespace EIGS
open Filter Topology
open scoped BigOperators
noncomputable section
variable {State : Type*} [Fintype State] [DecidableEq State] [Nonempty State]

theorem primitive_matrix_normalized_row_sum_limit (matrix : Matrix State State ℝ)
    (primitive : matrix.IsPrimitive) :
    ∃ vector : State → ℝ, ∃ coefficient : ℝ,
      (∀ state, 0 < vector state) ∧ (∑ state, vector state) = 1 ∧
      matrix.mulVec vector = finiteRealMatrixSpectralRadius matrix • vector ∧
      0 < coefficient ∧ ∀ first,
        Tendsto (fun power : ℕ => (∑ second, (matrix ^ power) first second) /
          (finiteRealMatrixSpectralRadius matrix) ^ power)
          atTop (𝓝 (coefficient * vector first)) := by
  obtain ⟨vector, vectorPositive, normalized, eigenpair, kernelNonnegative, kernelRowSum,
    block, blockPositive, anchor, commonMass, commonMassPositive, commonMassSmall, commonColumn⟩ :=
    primitive_matrix_markov_common_column matrix primitive
  have ratePositive : 0 < finiteRealMatrixSpectralRadius matrix := by
    obtain ⟨_, _, positive, _⟩ := primitive_matrix_spectralRadius_eigenpair_finite matrix primitive
    exact positive
  obtain ⟨coefficient, coefficientLower, convergence⟩ :=
    finiteMarkov_power_convergence_of_common_power
      (perronMarkovMatrix matrix vector (finiteRealMatrixSpectralRadius matrix))
      kernelNonnegative kernelRowSum block blockPositive anchor commonMass
      commonMassPositive commonMassSmall commonColumn (fun state => 1 / vector state)
  have minimumPositive : 0 < finiteVectorMinimum (fun state => 1 / vector state) := by
    obtain ⟨state, _, valueEquality⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun state => 1 / vector state)
    change 0 < Finset.univ.inf' Finset.univ_nonempty (fun state => 1 / vector state)
    rw [valueEquality]
    exact one_div_pos.mpr (vectorPositive state)
  refine ⟨vector, coefficient, vectorPositive, normalized, eigenpair,
    minimumPositive.trans_le coefficientLower, ?_⟩
  intro first
  have rowIdentity (power : ℕ) :
      vector first * (((perronMarkovMatrix matrix vector
        (finiteRealMatrixSpectralRadius matrix)) ^ power).mulVec
          (fun state => 1 / vector state)) first =
      (∑ second, (matrix ^ power) first second) /
        (finiteRealMatrixSpectralRadius matrix) ^ power := by
    simp only [Matrix.mulVec, dotProduct]
    simp_rw [perronMarkovMatrix_power matrix vector _ vectorPositive ratePositive]
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro second _
    field_simp [(vectorPositive first).ne', (vectorPositive second).ne', ratePositive.ne'] <;> ring
  have actual := (convergence first).const_mul (vector first)
  simpa only [rowIdentity, mul_comm] using actual

end
end EIGS

#print axioms EIGS.primitive_matrix_normalized_row_sum_limit
