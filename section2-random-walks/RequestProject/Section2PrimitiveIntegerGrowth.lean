import RequestProject.Section2FiniteSpectralRadius
import RequestProject.Section1Vertices

/-! Primitivity of the actual integer degree matrix forces its spectral radius
to exceed one. A positive integer matrix power has every entry at least one;
summing the normalized Perron eigenvector equation gives a power of the
spectral radius at least the number of states. No degree-growth target or
spectral lower bound is an input. -/

namespace EIGS

open scoped BigOperators Classical
noncomputable section

theorem primitive_integer_matrix_spectralRadius_gt_one
    {index : Type*} [Fintype index] [DecidableEq index] [Nonempty index]
    (matrix : Matrix index index ℝ) (primitive : matrix.IsPrimitive)
    (integerEntries : ∀ row column, ∃ value : ℕ, matrix row column = (value : ℝ))
    (atLeastTwoStates : 2 ≤ Fintype.card index) :
    1 < finiteRealMatrixSpectralRadius matrix := by
  let naturalMatrix : Matrix index index ℕ := fun row column =>
    Classical.choose (integerEntries row column)
  have naturalMatrixEquality : naturalMatrix.map (Nat.castRingHom ℝ) = matrix := by
    ext row column
    exact (Classical.choose_spec (integerEntries row column)).symm
  have naturalPowerEquality : ∀ exponent : ℕ,
      (naturalMatrix ^ exponent).map (Nat.castRingHom ℝ) = matrix ^ exponent := by
    intro exponent
    induction exponent with
    | zero => simp
    | succ exponent induction =>
        rw [pow_succ, Matrix.map_mul, induction, naturalMatrixEquality, pow_succ]
  obtain ⟨exponent, exponentPositive, powerPositive⟩ := primitive.exists_pos_pow
  have powerAtLeastOne : ∀ row column, (1 : ℝ) ≤ (matrix ^ exponent) row column := by
    intro row column
    have equality := congrFun (congrFun (naturalPowerEquality exponent) row) column
    change ((naturalMatrix ^ exponent) row column : ℝ) = (matrix ^ exponent) row column at equality
    have positive : 0 < (naturalMatrix ^ exponent) row column := by
      exact_mod_cast (equality.symm ▸ powerPositive row column)
    rw [← equality]
    exact_mod_cast positive
  obtain ⟨vector, vectorPositive, ratePositive, normalized, eigenpair⟩ :=
    primitive_matrix_spectralRadius_eigenpair_finite matrix primitive
  have powerEigenpair : ∀ exponent : ℕ, (matrix ^ exponent).mulVec vector =
      finiteRealMatrixSpectralRadius matrix ^ exponent • vector := by
    intro exponent
    induction exponent with
    | zero => simp
    | succ exponent induction =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, induction, Matrix.mulVec_smul, eigenpair]
        simp only [smul_smul, pow_succ]
  have rowBound : ∀ row, (1 : ℝ) ≤
      finiteRealMatrixSpectralRadius matrix ^ exponent * vector row := by
    intro row
    have coordinate := congrFun (powerEigenpair exponent) row
    change (∑ column, (matrix ^ exponent) row column * vector column) =
      finiteRealMatrixSpectralRadius matrix ^ exponent * vector row at coordinate
    rw [← coordinate, ← normalized]
    apply Finset.sum_le_sum
    intro column _
    exact le_mul_of_one_le_left (vectorPositive column).le (powerAtLeastOne row column)
  have summed := Finset.sum_le_sum (fun row (_ : row ∈ Finset.univ) => rowBound row)
  rw [← Finset.mul_sum, normalized, mul_one] at summed
  have cardinalBound : (Fintype.card index : ℝ) ≤
      finiteRealMatrixSpectralRadius matrix ^ exponent := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using summed
  have twoStatesReal : (2 : ℝ) ≤ (Fintype.card index : ℝ) := by
    exact_mod_cast atLeastTwoStates
  have twoBound : (2 : ℝ) ≤ finiteRealMatrixSpectralRadius matrix ^ exponent :=
    twoStatesReal.trans cardinalBound
  by_contra notGreater
  have powerLeOne : finiteRealMatrixSpectralRadius matrix ^ exponent ≤ 1 :=
    pow_le_one₀ ratePositive.le (le_of_not_gt notGreater)
  linarith

theorem degree_spectralRadius_gt_one_of_primitive {K : ℕ} (system : EIGSData K)
    (primitiveDegree : (degreeMatrix system).IsPrimitive) :
    1 < finiteRealMatrixSpectralRadius (degreeMatrix system) := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  apply primitive_integer_matrix_spectralRadius_gt_one (degreeMatrix system) primitiveDegree
  · intro row column
    cases row <;> cases column <;> exact ⟨_, rfl⟩
  · have coloursPositive : 0 < K :=
      (Nat.zero_le system.initCol.val).trans_lt system.initCol.isLt
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega

end
end EIGS

#print axioms EIGS.primitive_integer_matrix_spectralRadius_gt_one
#print axioms EIGS.degree_spectralRadius_gt_one_of_primitive
