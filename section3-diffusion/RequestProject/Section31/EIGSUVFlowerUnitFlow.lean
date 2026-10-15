import RequestProject.Section31.EIGSUVFlowerModel
import RequestProject.Section31.EIGSFlowerUnitFlow

/-! An actual terminal unit flow on the genuine unequal-path flower.
The legacy Flower module is used only for the finite telescoping identity.
The first path is oriented backwards in the new literal model. -/

namespace EIGS
noncomputable section
open scoped Classical BigOperators
set_option maxHeartbeats 2200000

def uvFlowerPathPoint (length : ℕ) (position : Fin (length + 1)) : Bool ⊕ Fin (length - 1) :=
  if first : position.val = 0 then Sum.inl false
  else if last : position.val = length then Sum.inl true
  else Sum.inr ⟨position.val - 1, by have bound := position.isLt; omega⟩

theorem uvFlowerPathTail_eq_point (length : ℕ) (edge : Fin length) :
    uvFlowerPathTail length edge = uvFlowerPathPoint length edge.castSucc := by
  have notLast : edge.val ≠ length := Nat.ne_of_lt edge.isLt
  by_cases first : edge.val = 0 <;>
    simp [uvFlowerPathTail, uvFlowerPathPoint, first, notLast]

theorem uvFlowerPathHead_eq_point (length : ℕ) (edge : Fin length) :
    uvFlowerPathHead length edge = uvFlowerPathPoint length edge.succ := by
  have lengthNonzero : length ≠ 0 := by have bound := edge.isLt; omega
  have notFirst : edge.val + 1 ≠ 0 := by omega
  by_cases last : edge.val + 1 = length <;>
    simp [uvFlowerPathHead, uvFlowerPathPoint, notFirst, last, lengthNonzero]

@[simp] theorem uvFlowerPathPoint_zero (length : ℕ) :
    uvFlowerPathPoint length 0 = Sum.inl false := by
  simp [uvFlowerPathPoint]

@[simp] theorem uvFlowerPathPoint_last (length : ℕ) (positive : 0 < length) :
    uvFlowerPathPoint length (Fin.last length) = Sum.inl true := by
  simp [uvFlowerPathPoint, Nat.ne_of_gt positive]

def uvFlowerUnitCurrent (firstLength secondLength : ℕ) : UVFlowerEdge firstLength secondLength → ℝ :=
  Sum.elim (fun _ => -(secondLength : ℝ) / ((firstLength : ℝ) + secondLength))
    (fun _ => (firstLength : ℝ) / ((firstLength : ℝ) + secondLength))

theorem uvFlowerUnitCurrent_isUnitFlow (firstLength secondLength : ℕ)
    (firstPositive : 0 < firstLength) (secondPositive : 0 < secondLength) :
    ((uvFlowerSystem firstLength secondLength).ruleNetwork 0).IsUnitFlow
      (Sum.inl false) (Sum.inl true) (uvFlowerUnitCurrent firstLength secondLength) := by
  intro vertex
  have denominatorNonzero : (firstLength : ℝ) + secondLength ≠ 0 :=
    (add_pos (Nat.cast_pos.mpr firstPositive) (Nat.cast_pos.mpr secondPositive)).ne'
  have terminalsDistinct : (Sum.inl false : UVFlowerVertex firstLength secondLength) ≠ Sum.inl true := by
    intro equality
    have impossible := Sum.inl.inj equality
    cases impossible
  have leftSummand (edge : Fin firstLength) :
      (if (uvFlowerRuleGraph firstLength secondLength).tail (Sum.inl edge) = vertex
        then uvFlowerUnitCurrent firstLength secondLength (Sum.inl edge) else 0) -
      (if (uvFlowerRuleGraph firstLength secondLength).head (Sum.inl edge) = vertex
        then uvFlowerUnitCurrent firstLength secondLength (Sum.inl edge) else 0) =
      ((secondLength : ℝ) / ((firstLength : ℝ) + secondLength)) *
        ((if uvFlowerLeftEmbedding firstLength secondLength (uvFlowerPathTail firstLength edge) = vertex
          then (1 : ℝ) else 0) -
        (if uvFlowerLeftEmbedding firstLength secondLength (uvFlowerPathHead firstLength edge) = vertex
          then (1 : ℝ) else 0)) := by
    simp only [uvFlowerRuleGraph, uvFlowerUnitCurrent, Sum.elim_inl]
    split_ifs <;> ring
  have rightSummand (edge : Fin secondLength) :
      (if (uvFlowerRuleGraph firstLength secondLength).tail (Sum.inr edge) = vertex
        then uvFlowerUnitCurrent firstLength secondLength (Sum.inr edge) else 0) -
      (if (uvFlowerRuleGraph firstLength secondLength).head (Sum.inr edge) = vertex
        then uvFlowerUnitCurrent firstLength secondLength (Sum.inr edge) else 0) =
      ((firstLength : ℝ) / ((firstLength : ℝ) + secondLength)) *
        ((if uvFlowerRightEmbedding firstLength secondLength (uvFlowerPathTail secondLength edge) = vertex
          then (1 : ℝ) else 0) -
        (if uvFlowerRightEmbedding firstLength secondLength (uvFlowerPathHead secondLength edge) = vertex
          then (1 : ℝ) else 0)) := by
    simp only [uvFlowerRuleGraph, uvFlowerUnitCurrent, Sum.elim_inr]
    split_ifs <;> ring
  have leftTelescopes :
      (∑ edge : Fin firstLength,
        ((if uvFlowerLeftEmbedding firstLength secondLength (uvFlowerPathTail firstLength edge) = vertex
          then (1 : ℝ) else 0) -
        (if uvFlowerLeftEmbedding firstLength secondLength (uvFlowerPathHead firstLength edge) = vertex
          then (1 : ℝ) else 0))) =
      (if vertex = Sum.inl false then (1 : ℝ) else 0) -
        (if vertex = Sum.inl true then (1 : ℝ) else 0) := by
    have telescoped := finite_chain_boundary_sum firstLength
      (fun position => if uvFlowerLeftEmbedding firstLength secondLength
        (uvFlowerPathPoint firstLength position) = vertex then (1 : ℝ) else 0)
    simpa only [← uvFlowerPathTail_eq_point, ← uvFlowerPathHead_eq_point, uvFlowerPathPoint_zero,
      uvFlowerPathPoint_last firstLength firstPositive, uvFlowerLeftEmbedding, eq_comm] using telescoped
  have rightTelescopes :
      (∑ edge : Fin secondLength,
        ((if uvFlowerRightEmbedding firstLength secondLength (uvFlowerPathTail secondLength edge) = vertex
          then (1 : ℝ) else 0) -
        (if uvFlowerRightEmbedding firstLength secondLength (uvFlowerPathHead secondLength edge) = vertex
          then (1 : ℝ) else 0))) =
      (if vertex = Sum.inl false then (1 : ℝ) else 0) -
        (if vertex = Sum.inl true then (1 : ℝ) else 0) := by
    have telescoped := finite_chain_boundary_sum secondLength
      (fun position => if uvFlowerRightEmbedding firstLength secondLength
        (uvFlowerPathPoint secondLength position) = vertex then (1 : ℝ) else 0)
    simpa only [← uvFlowerPathTail_eq_point, ← uvFlowerPathHead_eq_point, uvFlowerPathPoint_zero,
      uvFlowerPathPoint_last secondLength secondPositive, uvFlowerRightEmbedding, eq_comm] using telescoped
  change (∑ edge : UVFlowerEdge firstLength secondLength,
      if (uvFlowerRuleGraph firstLength secondLength).tail edge = vertex
        then uvFlowerUnitCurrent firstLength secondLength edge else 0) -
    (∑ edge : UVFlowerEdge firstLength secondLength,
      if (uvFlowerRuleGraph firstLength secondLength).head edge = vertex
        then uvFlowerUnitCurrent firstLength secondLength edge else 0) =
    if vertex = Sum.inl false then 1 else if vertex = Sum.inl true then -1 else 0
  rw [← Finset.sum_sub_distrib, Fintype.sum_sum_type]
  simp_rw [leftSummand, rightSummand, ← Finset.mul_sum, leftTelescopes, rightTelescopes]
  rw [← add_mul, ← add_div]
  have coefficient : (secondLength : ℝ) + firstLength = (firstLength : ℝ) + secondLength := add_comm _ _
  rw [coefficient, div_self denominatorNonzero, one_mul]
  by_cases atSource : vertex = Sum.inl false
  · simp [atSource, terminalsDistinct]
  · by_cases atSink : vertex = Sum.inl true <;>
      simp [atSource, atSink, terminalsDistinct, terminalsDistinct.symm]

def uvFlowerTerminalFlow (firstLength secondLength : ℕ)
    (firstPositive : 0 < firstLength) (secondPositive : 0 < secondLength) :
    ((uvFlowerSystem firstLength secondLength).ruleNetwork 0).Flow (Sum.inl false) (Sum.inl true) :=
  ⟨uvFlowerUnitCurrent firstLength secondLength,
    uvFlowerUnitCurrent_isUnitFlow firstLength secondLength firstPositive secondPositive⟩

theorem uvFlowerUnitCurrent_energy (firstLength secondLength : ℕ)
    (firstPositive : 0 < firstLength) (secondPositive : 0 < secondLength) :
    ((uvFlowerSystem firstLength secondLength).ruleNetwork 0).energyNetwork
      (uvFlowerUnitCurrent firstLength secondLength) (fun _ => 1) =
        (firstLength : ℝ) * secondLength / ((firstLength : ℝ) + secondLength) := by
  have denominatorNonzero : (firstLength : ℝ) + secondLength ≠ 0 :=
    (add_pos (Nat.cast_pos.mpr firstPositive) (Nat.cast_pos.mpr secondPositive)).ne'
  change (∑ edge : UVFlowerEdge firstLength secondLength,
    (1 : ℝ) * (uvFlowerUnitCurrent firstLength secondLength edge) ^ 2) = _
  rw [Fintype.sum_sum_type]
  simp only [uvFlowerUnitCurrent, Sum.elim_inl, Sum.elim_inr, one_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [denominatorNonzero] <;> ring

end
end EIGS

#print axioms EIGS.uvFlowerPathTail_eq_point
#print axioms EIGS.uvFlowerPathHead_eq_point
#print axioms EIGS.uvFlowerUnitCurrent_isUnitFlow
#print axioms EIGS.uvFlowerTerminalFlow
#print axioms EIGS.uvFlowerUnitCurrent_energy
