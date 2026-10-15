import RequestProject.Section31.EIGSUVFlowerModel
import RequestProject.Section2SpectralRadius

/-! The mass matrix of the genuine unequal-path flower is computed
from its literal disjoint sum of edge types. -/

namespace EIGS
noncomputable section
open scoped Classical BigOperators

theorem uvFlowerSystem_massMatrix (firstLength secondLength : ℕ) :
    massMatrix (uvFlowerSystem firstLength secondLength).toRuleData =
      fun _ _ => firstLength + secondLength := by
  funext row column
  have rowZero : row = 0 := Subsingleton.elim _ _
  have columnZero : column = 0 := Subsingleton.elim _ _
  subst row
  subst column
  simp [massMatrix, EIGSData.toRuleData, uvFlowerSystem, uvFlowerRuleGraph, UVFlowerEdge]

theorem uvFlowerSystem_massMatrixR (firstLength secondLength : ℕ) :
    massMatrixR (uvFlowerSystem firstLength secondLength).toRuleData =
      fun _ _ => (firstLength : ℝ) + secondLength := by
  funext row column
  simp only [massMatrixR, uvFlowerSystem_massMatrix, Nat.cast_add]

theorem uvFlowerSystem_massSpectralRadius (firstLength secondLength : ℕ) :
    realMatrixSpectralRadius (massMatrixR (uvFlowerSystem firstLength secondLength).toRuleData) =
      (firstLength : ℝ) + secondLength := by
  apply realMatrixSpectralRadius_eq_positive_eigenvalue (by norm_num)
    _ (massMatrixR_nonneg _) (fun _ => 1) _ (fun _ => zero_lt_one)
      (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  funext colour
  have colourZero : colour = 0 := Subsingleton.elim _ _
  subst colour
  simp [uvFlowerSystem_massMatrixR, Matrix.mulVec, dotProduct]

end
end EIGS

#print axioms EIGS.uvFlowerSystem_massMatrix
#print axioms EIGS.uvFlowerSystem_massMatrixR
#print axioms EIGS.uvFlowerSystem_massSpectralRadius
