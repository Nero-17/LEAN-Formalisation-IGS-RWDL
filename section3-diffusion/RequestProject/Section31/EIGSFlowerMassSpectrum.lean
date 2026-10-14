import RequestProject.Section31.EIGSFlowerRuleGraph
import RequestProject.Section2SpectralRadius

/-! Mass spectral radius computed from the actual rule-edge type. -/

namespace EIGS
noncomputable section
open scoped Classical BigOperators

theorem flowerSystem_massMatrix (branches segments : ℕ) :
    massMatrix (flowerSystem branches segments).toRuleData =
      fun _ _ => branches * segments := by
  funext row column
  have rowZero : row = 0 := Subsingleton.elim _ _
  have columnZero : column = 0 := Subsingleton.elim _ _
  subst row
  subst column
  simp [massMatrix, EIGSData.toRuleData, flowerSystem, flowerGraph]

theorem flowerSystem_massMatrixR (branches segments : ℕ) :
    massMatrixR (flowerSystem branches segments).toRuleData =
      fun _ _ => (branches : ℝ) * (segments : ℝ) := by
  funext row column
  simp only [massMatrixR, flowerSystem_massMatrix, Nat.cast_mul]

theorem flowerSystem_massSpectralRadius (branches segments : ℕ) :
    realMatrixSpectralRadius (massMatrixR (flowerSystem branches segments).toRuleData) =
      (branches : ℝ) * (segments : ℝ) := by
  apply realMatrixSpectralRadius_eq_positive_eigenvalue (by norm_num)
    _ (massMatrixR_nonneg _) (fun _ => 1) _ (fun _ => zero_lt_one)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  funext colour
  have colourZero : colour = 0 := Subsingleton.elim _ _
  subst colour
  simp [flowerSystem_massMatrixR, Matrix.mulVec, dotProduct]

end
end EIGS

#print axioms EIGS.flowerSystem_massMatrix
#print axioms EIGS.flowerSystem_massMatrixR
#print axioms EIGS.flowerSystem_massSpectralRadius
