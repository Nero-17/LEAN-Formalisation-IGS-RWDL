import RequestProject.Section31.EIGSUVFlowerUnitFlow

/-! The normalized position on each of the two actual flower paths.
Both paths agree at the planting vertices, despite their different lengths. -/

namespace EIGS
noncomputable section
open scoped Classical

def uvFlowerPathFraction (length : ℕ) : Bool ⊕ Fin (length - 1) → ℝ
  | Sum.inl endpoint => if endpoint then 1 else 0
  | Sum.inr vertex => ((vertex.val : ℝ) + 1) / (length : ℝ)

def uvFlowerFraction (firstLength secondLength : ℕ) : UVFlowerVertex firstLength secondLength → ℝ
  | Sum.inl endpoint => if endpoint then 1 else 0
  | Sum.inr (Sum.inl vertex) => ((vertex.val : ℝ) + 1) / (firstLength : ℝ)
  | Sum.inr (Sum.inr vertex) => ((vertex.val : ℝ) + 1) / (secondLength : ℝ)

theorem uvFlowerPathFraction_point (length : ℕ) (positive : 0 < length)
    (position : Fin (length + 1)) :
    uvFlowerPathFraction length (uvFlowerPathPoint length position) = (position.val : ℝ) / (length : ℝ) := by
  have lengthNonzero : (length : ℝ) ≠ 0 := (Nat.cast_pos.mpr positive).ne'
  unfold uvFlowerPathPoint
  split_ifs with first last
  · simp [uvFlowerPathFraction, first]
  · simp [uvFlowerPathFraction, last, lengthNonzero]
  · simp only [uvFlowerPathFraction, Fin.val_mk]
    rw [Nat.cast_sub (show 1 ≤ position.val by omega)]
    push_cast
    ring

@[simp] theorem uvFlowerFraction_left (firstLength secondLength : ℕ)
    (vertex : Bool ⊕ Fin (firstLength - 1)) :
    uvFlowerFraction firstLength secondLength (uvFlowerLeftEmbedding firstLength secondLength vertex) =
      uvFlowerPathFraction firstLength vertex := by
  cases vertex with
  | inl endpoint => cases endpoint <;> rfl
  | inr vertex => rfl

@[simp] theorem uvFlowerFraction_right (firstLength secondLength : ℕ)
    (vertex : Bool ⊕ Fin (secondLength - 1)) :
    uvFlowerFraction firstLength secondLength (uvFlowerRightEmbedding firstLength secondLength vertex) =
      uvFlowerPathFraction secondLength vertex := by
  cases vertex with
  | inl endpoint => cases endpoint <;> rfl
  | inr vertex => rfl

theorem uvFlowerPathFraction_increment (length : ℕ) (positive : 0 < length) (edge : Fin length) :
    uvFlowerPathFraction length (uvFlowerPathHead length edge) -
      uvFlowerPathFraction length (uvFlowerPathTail length edge) = 1 / (length : ℝ) := by
  rw [uvFlowerPathHead_eq_point, uvFlowerPathTail_eq_point,
    uvFlowerPathFraction_point length positive, uvFlowerPathFraction_point length positive]
  simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

theorem uvFlowerFraction_edge (firstLength secondLength : ℕ)
    (firstPositive : 0 < firstLength) (secondPositive : 0 < secondLength)
    (edge : UVFlowerEdge firstLength secondLength) :
    uvFlowerFraction firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).tail edge) -
      uvFlowerFraction firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).head edge) =
        Sum.elim (fun _ => 1 / (firstLength : ℝ)) (fun _ => -(1 / (secondLength : ℝ))) edge := by
  cases edge with
  | inl edge =>
      simpa only [uvFlowerRuleGraph, Sum.elim_inl, uvFlowerFraction_left] using
        uvFlowerPathFraction_increment firstLength firstPositive edge
  | inr edge =>
      have increment := uvFlowerPathFraction_increment secondLength secondPositive edge
      simp only [uvFlowerRuleGraph, Sum.elim_inr, uvFlowerFraction_right]
      linarith

end
end EIGS

#print axioms EIGS.uvFlowerPathFraction_point
#print axioms EIGS.uvFlowerFraction_left
#print axioms EIGS.uvFlowerFraction_right
#print axioms EIGS.uvFlowerPathFraction_increment
#print axioms EIGS.uvFlowerFraction_edge
