import RequestProject.Section31.EIGSUVFlowerRuleGeometry
import RequestProject.Section2FiniteSpectralRadius

/-! Actual endpoint incidence counts of the genuine unequal-path
flower. The reversed first path and forward second path give N = 1
entrywise, hence the degree rate is exactly two and N is primitive. -/

namespace EIGS
noncomputable section
open scoped Classical BigOperators

@[simp] theorem uvFlowerPathTail_eq_source (length : ℕ) (edge : Fin length) :
    uvFlowerPathTail length edge = Sum.inl false ↔ edge.val = 0 := by
  constructor
  · intro equality
    have heights := congrArg (uvFlowerPathHeight length) equality
    rw [uvFlowerPathTail_height] at heights
    simpa only [uvFlowerPathHeight] using heights
  · intro equality
    simp [uvFlowerPathTail, equality]

@[simp] theorem uvFlowerPathHead_eq_sink (length : ℕ) (edge : Fin length) :
    uvFlowerPathHead length edge = Sum.inl true ↔ edge.val + 1 = length := by
  constructor
  · intro equality
    have heights := congrArg (uvFlowerPathHeight length) equality
    rw [uvFlowerPathHead_height] at heights
    simpa only [uvFlowerPathHeight] using heights
  · intro equality
    simp [uvFlowerPathHead, equality]

@[simp] theorem uvFlowerPathHead_ne_source (length : ℕ) (edge : Fin length) :
    uvFlowerPathHead length edge ≠ Sum.inl false := by
  intro equality
  have heights := congrArg (uvFlowerPathHeight length) equality
  rw [uvFlowerPathHead_height] at heights
  change edge.val + 1 = 0 at heights
  omega

@[simp] theorem uvFlowerPathTail_ne_sink (length : ℕ) (edge : Fin length) :
    uvFlowerPathTail length edge ≠ Sum.inl true := by
  intro equality
  have heights := congrArg (uvFlowerPathHeight length) equality
  rw [uvFlowerPathTail_height] at heights
  change edge.val = length at heights
  have bound := edge.isLt
  omega

@[simp] theorem uvFlowerLeftEmbedding_eq_endpoint (firstLength secondLength : ℕ)
    (vertex : Bool ⊕ Fin (firstLength - 1)) (endpoint : Bool) :
    uvFlowerLeftEmbedding firstLength secondLength vertex = Sum.inl endpoint ↔
      vertex = Sum.inl endpoint := by
  cases vertex <;> simp [uvFlowerLeftEmbedding]

@[simp] theorem uvFlowerRightEmbedding_eq_endpoint (firstLength secondLength : ℕ)
    (vertex : Bool ⊕ Fin (secondLength - 1)) (endpoint : Bool) :
    uvFlowerRightEmbedding firstLength secondLength vertex = Sum.inl endpoint ↔
      vertex = Sum.inl endpoint := by
  cases vertex <;> simp [uvFlowerRightEmbedding]

theorem uvFlowerSystem_endpoint_degree_counts (firstLength secondLength : ℕ)
    (firstPositive : 0 < firstLength) (secondPositive : 0 < secondLength) :
    ruleTailDeg (uvFlowerSystem firstLength secondLength) 0 (Sum.inl false) 0 = 1 ∧
    ruleHeadDeg (uvFlowerSystem firstLength secondLength) 0 (Sum.inl false) 0 = 1 ∧
    ruleTailDeg (uvFlowerSystem firstLength secondLength) 0 (Sum.inl true) 0 = 1 ∧
    ruleHeadDeg (uvFlowerSystem firstLength secondLength) 0 (Sum.inl true) 0 = 1 := by
  have zeroStep {length : ℕ} (positive : 0 < length) (edge : Fin length) :
      edge.val = 0 ↔ edge = (⟨0, positive⟩ : Fin length) := by
    rw [Fin.ext_iff]
  have lastStep {length : ℕ} (positive : 0 < length) (edge : Fin length) :
      edge.val + 1 = length ↔ edge = (⟨length - 1, by omega⟩ : Fin length) := by
    rw [Fin.ext_iff]
    simp only [Fin.val_mk]
    omega
  have sourceTail : (Finset.univ.filter (fun edge : UVFlowerEdge firstLength secondLength =>
      (uvFlowerRuleGraph firstLength secondLength).tail edge = Sum.inl false)) =
        {Sum.inr (⟨0, secondPositive⟩ : Fin secondLength)} := by
    ext edge
    cases edge <;> simp [uvFlowerRuleGraph, Fin.ext_iff]
  have sourceHead : (Finset.univ.filter (fun edge : UVFlowerEdge firstLength secondLength =>
      (uvFlowerRuleGraph firstLength secondLength).head edge = Sum.inl false)) =
        {Sum.inl (⟨0, firstPositive⟩ : Fin firstLength)} := by
    ext edge
    cases edge <;> simp [uvFlowerRuleGraph, Fin.ext_iff]
  have sinkTail : (Finset.univ.filter (fun edge : UVFlowerEdge firstLength secondLength =>
      (uvFlowerRuleGraph firstLength secondLength).tail edge = Sum.inl true)) =
        {Sum.inl (⟨firstLength - 1, by omega⟩ : Fin firstLength)} := by
    ext edge
    cases edge <;> simp [uvFlowerRuleGraph, Fin.ext_iff] <;> omega
  have sinkHead : (Finset.univ.filter (fun edge : UVFlowerEdge firstLength secondLength =>
      (uvFlowerRuleGraph firstLength secondLength).head edge = Sum.inl true)) =
        {Sum.inr (⟨secondLength - 1, by omega⟩ : Fin secondLength)} := by
    ext edge
    cases edge <;> simp [uvFlowerRuleGraph, Fin.ext_iff] <;> omega
  have tailCount (endpoint : Bool) :
      ruleTailDeg (uvFlowerSystem firstLength secondLength) 0 (Sum.inl endpoint) 0 =
        (Finset.univ.filter (fun edge : UVFlowerEdge firstLength secondLength =>
          (uvFlowerRuleGraph firstLength secondLength).tail edge = Sum.inl endpoint)).card := by
    simp [ruleTailDeg, uvFlowerSystem, uvFlowerRuleGraph]
  have headCount (endpoint : Bool) :
      ruleHeadDeg (uvFlowerSystem firstLength secondLength) 0 (Sum.inl endpoint) 0 =
        (Finset.univ.filter (fun edge : UVFlowerEdge firstLength secondLength =>
          (uvFlowerRuleGraph firstLength secondLength).head edge = Sum.inl endpoint)).card := by
    simp [ruleHeadDeg, uvFlowerSystem, uvFlowerRuleGraph]
  rw [tailCount false, headCount false, tailCount true, headCount true,
    sourceTail, sourceHead, sinkTail, sinkHead]
  simp

theorem uvFlowerSystem_degreeMatrix (firstLength secondLength : ℕ)
    (firstPositive : 0 < firstLength) (secondPositive : 0 < secondLength) :
    degreeMatrix (uvFlowerSystem firstLength secondLength) = fun _ _ => (1 : ℝ) := by
  have counts := uvFlowerSystem_endpoint_degree_counts firstLength secondLength firstPositive secondPositive
  funext row column
  cases row with
  | inl row =>
    cases column with
    | inl column =>
      have rowZero : row = 0 := Subsingleton.elim _ _
      have columnZero : column = 0 := Subsingleton.elim _ _
      subst row
      subst column
      change (ruleTailDeg (uvFlowerSystem firstLength secondLength) 0 (Sum.inl false) 0 : ℝ) = 1
      exact_mod_cast counts.1
    | inr column =>
      have rowZero : row = 0 := Subsingleton.elim _ _
      have columnZero : column = 0 := Subsingleton.elim _ _
      subst row
      subst column
      change (ruleHeadDeg (uvFlowerSystem firstLength secondLength) 0 (Sum.inl false) 0 : ℝ) = 1
      exact_mod_cast counts.2.1
  | inr row =>
    cases column with
    | inl column =>
      have rowZero : row = 0 := Subsingleton.elim _ _
      have columnZero : column = 0 := Subsingleton.elim _ _
      subst row
      subst column
      change (ruleTailDeg (uvFlowerSystem firstLength secondLength) 0 (Sum.inl true) 0 : ℝ) = 1
      exact_mod_cast counts.2.2.1
    | inr column =>
      have rowZero : row = 0 := Subsingleton.elim _ _
      have columnZero : column = 0 := Subsingleton.elim _ _
      subst row
      subst column
      change (ruleHeadDeg (uvFlowerSystem firstLength secondLength) 0 (Sum.inl true) 0 : ℝ) = 1
      exact_mod_cast counts.2.2.2

theorem uvFlowerSystem_degreeMatrix_primitive (firstLength secondLength : ℕ)
    (firstPositive : 0 < firstLength) (secondPositive : 0 < secondLength) :
    (degreeMatrix (uvFlowerSystem firstLength secondLength)).IsPrimitive := by
  rw [uvFlowerSystem_degreeMatrix firstLength secondLength firstPositive secondPositive]
  refine ⟨fun _ _ => by norm_num, 1, by omega, ?_⟩
  intro row column
  norm_num

theorem uvFlowerSystem_degree_positive_eigenpair (firstLength secondLength : ℕ)
    (firstPositive : 0 < firstLength) (secondPositive : 0 < secondLength) :
    (degreeMatrix (uvFlowerSystem firstLength secondLength)).mulVec (fun _ => (1 : ℝ)) =
      (2 : ℝ) • (fun _ : Fin 1 ⊕ Fin 1 => (1 : ℝ)) := by
  rw [uvFlowerSystem_degreeMatrix firstLength secondLength firstPositive secondPositive]
  funext row
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

theorem uvFlowerSystem_degreeSpectralRadius (firstLength secondLength : ℕ)
    (firstPositive : 0 < firstLength) (secondPositive : 0 < secondLength) :
    finiteRealMatrixSpectralRadius (degreeMatrix (uvFlowerSystem firstLength secondLength)) = 2 := by
  exact finiteRealMatrixSpectralRadius_eq_positive_eigenvalue
    _ (degreeMatrix_nonneg _) (fun _ => 1) 2 (fun _ => zero_lt_one) (by norm_num)
    (uvFlowerSystem_degree_positive_eigenpair firstLength secondLength firstPositive secondPositive)

end
end EIGS

#print axioms EIGS.uvFlowerSystem_endpoint_degree_counts
#print axioms EIGS.uvFlowerSystem_degreeMatrix
#print axioms EIGS.uvFlowerSystem_degreeMatrix_primitive
#print axioms EIGS.uvFlowerSystem_degree_positive_eigenpair
#print axioms EIGS.uvFlowerSystem_degreeSpectralRadius
