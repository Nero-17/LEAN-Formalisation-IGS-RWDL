import RequestProject.Section31.EIGSTwoColourRuleGraph
import RequestProject.Section2FiniteSpectralRadius

/-! Actual mass and oriented-degree spectra of Figure 3. The degree matrix
is reducible, despite having a strictly positive eigenvector with eigenvalue
2. No primitive-degree hypothesis is invented for this example. Candidate. -/

namespace EIGS
open scoped BigOperators Classical
noncomputable section

def twoColourDegreeMatrix : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  Sum.elim
    (fun row => Sum.elim (fun column => (!![(1 : ℝ), 1; 0, 2]) row column) (fun _ => 0))
    (fun row => Sum.elim (fun _ => 0) (fun column => (!![(1 : ℝ), 1; 1, 1]) row column))

theorem twoColourSystem_degreeMatrix : degreeMatrix twoColourSystem = twoColourDegreeMatrix := by
  ext row column
  cases row with
  | inl row =>
    cases column with
    | inl column =>
      fin_cases row <;> fin_cases column <;>
        simp only [degreeMatrix, twoColourDegreeMatrix, Sum.elim_inl, Sum.elim_inr,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;> norm_cast <;> decide
    | inr column =>
      fin_cases row <;> fin_cases column <;>
        simp only [degreeMatrix, twoColourDegreeMatrix, Sum.elim_inl, Sum.elim_inr,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;> norm_cast <;> decide
  | inr row =>
    cases column with
    | inl column =>
      fin_cases row <;> fin_cases column <;>
        simp only [degreeMatrix, twoColourDegreeMatrix, Sum.elim_inl, Sum.elim_inr,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;> norm_cast <;> decide
    | inr column =>
      fin_cases row <;> fin_cases column <;>
        simp only [degreeMatrix, twoColourDegreeMatrix, Sum.elim_inl, Sum.elim_inr,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;> norm_cast <;> decide

def twoColourPaperDegreeIndex : Fin 4 → Fin 2 ⊕ Fin 2 :=
  ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1]

theorem twoColourSystem_paperDegreeMatrix (row column : Fin 4) :
    degreeMatrix twoColourSystem (twoColourPaperDegreeIndex row) (twoColourPaperDegreeIndex column) =
      (!![(1 : ℝ), 0, 1, 0; 0, 1, 0, 1; 0, 0, 2, 0; 0, 1, 0, 1]) row column := by
  rw [twoColourSystem_degreeMatrix]
  fin_cases row <;> fin_cases column <;> norm_num [twoColourPaperDegreeIndex, twoColourDegreeMatrix]

theorem twoColourSystem_massSpectralRadius :
    realMatrixSpectralRadius (massMatrixR twoColourSystem.toRuleData) = 3 + Real.sqrt 6 := by
  apply realMatrixSpectralRadius_eq_positive_eigenvalue (by norm_num)
    (massMatrixR twoColourSystem.toRuleData) (massMatrixR_nonneg _) ![Real.sqrt 6, 2]
    (3 + Real.sqrt 6)
  · intro colour
    fin_cases colour <;> norm_num <;> positivity
  · positivity
  · rw [twoColourSystem_massMatrixR]
    ext colour
    fin_cases colour <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]

theorem twoColourSystem_degreeSpectralRadius :
    finiteRealMatrixSpectralRadius (degreeMatrix twoColourSystem) = 2 := by
  apply finiteRealMatrixSpectralRadius_eq_positive_eigenvalue
    (degreeMatrix twoColourSystem) (degreeMatrix_nonneg _) (fun _ => 1) 2
  · intro state
    norm_num
  · norm_num
  · rw [twoColourSystem_degreeMatrix]
    ext state
    cases state with
    | inl colour =>
      fin_cases colour <;>
        norm_num [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_succ, twoColourDegreeMatrix]
    | inr colour =>
      fin_cases colour <;>
        norm_num [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_succ, twoColourDegreeMatrix]

theorem twoColourDegreeMatrix_pow_out_in_zero (power : ℕ) (first second : Fin 2) :
    (twoColourDegreeMatrix ^ power) (Sum.inl first) (Sum.inr second) = 0 := by
  induction power generalizing first second with
  | zero => simp
  | succ power induction =>
    rw [pow_succ, Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [induction, zero_mul, Finset.sum_const_zero, add_zero]
    simp [twoColourDegreeMatrix]

theorem twoColourSystem_degree_not_primitive : ¬ (degreeMatrix twoColourSystem).IsPrimitive := by
  intro primitive
  obtain ⟨power, powerPositive, allEntriesPositive⟩ := primitive.exists_pos_pow
  have impossible := allEntriesPositive (Sum.inl 0) (Sum.inr 0)
  rw [twoColourSystem_degreeMatrix, twoColourDegreeMatrix_pow_out_in_zero] at impossible
  exact (lt_irrefl (0 : ℝ)) impossible

end
end EIGS

#print axioms EIGS.twoColourSystem_paperDegreeMatrix
#print axioms EIGS.twoColourSystem_massSpectralRadius
#print axioms EIGS.twoColourSystem_degreeSpectralRadius
#print axioms EIGS.twoColourSystem_degree_not_primitive
