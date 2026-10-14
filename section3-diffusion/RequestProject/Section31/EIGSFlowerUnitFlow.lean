import RequestProject.Section31.EIGSFlowerRuleGraph
import RequestProject.Section31.DirichletThomson
import Mathlib.Algebra.BigOperators.Fin

/-! An actual unit terminal flow on the parallel-chain flower. The sign
of each branch current follows its chosen orientation. Kirchhoff's law
is proved by telescoping the endpoint indicators along each chain. -/

namespace EIGS
open scoped Classical BigOperators
noncomputable section

theorem finite_chain_boundary_sum (count : ℕ) (value : Fin (count + 1) → ℝ) :
    (∑ index : Fin count, (value index.castSucc - value index.succ)) =
      value 0 - value (Fin.last count) := by
  have first := Fin.sum_univ_castSucc value
  have second := Fin.sum_univ_succ value
  rw [Finset.sum_sub_distrib]
  linarith

def flowerCurrent (branches segments : ℕ) (edge : Fin branches × Fin segments) : ℝ :=
  if edge.1.val = 0 then -(1 / (branches : ℝ)) else 1 / (branches : ℝ)

theorem flowerCurrent_isUnitFlow (branches segments : ℕ)
    (branchesPositive : 0 < branches) (segmentsPositive : 0 < segments) :
    ((flowerSystem branches segments).ruleNetwork 0).IsUnitFlow
      (Sum.inl false) (Sum.inl true) (flowerCurrent branches segments) := by
  intro vertex
  have branchesNonzero : (branches : ℝ) ≠ 0 := (Nat.cast_pos.mpr branchesPositive).ne'
  have terminalsDistinct : (Sum.inl false : Bool ⊕ (Fin branches × Fin (segments - 1))) ≠ Sum.inl true := by
    intro equality
    have impossible := Sum.inl.inj equality
    cases impossible
  have summandIdentity (edge : Fin branches × Fin segments) :
      (if (flowerGraph branches segments).tail edge = vertex then flowerCurrent branches segments edge else 0) -
        (if (flowerGraph branches segments).head edge = vertex then flowerCurrent branches segments edge else 0) =
      (1 / (branches : ℝ)) *
        ((if flowerEdgeStart branches segments edge = vertex then (1 : ℝ) else 0) -
          (if flowerEdgeEnd branches segments edge = vertex then (1 : ℝ) else 0)) := by
    by_cases backwards : edge.1.val = 0 <;>
      simp only [flowerGraph, flowerCurrent, backwards, ↓reduceIte] <;>
      split_ifs <;> ring
  have branchTelescopes (branch : Fin branches) :
      (∑ position : Fin segments,
        ((if flowerEdgeStart branches segments (branch, position) = vertex then (1 : ℝ) else 0) -
        (if flowerEdgeEnd branches segments (branch, position) = vertex then (1 : ℝ) else 0))) =
      (if vertex = Sum.inl false then (1 : ℝ) else 0) -
        (if vertex = Sum.inl true then (1 : ℝ) else 0) := by
    have telescoped := finite_chain_boundary_sum segments
      (fun position : Fin (segments + 1) =>
        if flowerPoint branches segments branch position = vertex then (1 : ℝ) else 0)
    simpa [flowerEdgeStart, flowerEdgeEnd, flowerPoint, Nat.ne_of_gt segmentsPositive, eq_comm] using telescoped
  change (∑ edge : Fin branches × Fin segments,
      if (flowerGraph branches segments).tail edge = vertex then flowerCurrent branches segments edge else 0) -
    (∑ edge : Fin branches × Fin segments,
      if (flowerGraph branches segments).head edge = vertex then flowerCurrent branches segments edge else 0) =
    if vertex = Sum.inl false then 1 else if vertex = Sum.inl true then -1 else 0
  rw [← Finset.sum_sub_distrib]
  simp_rw [summandIdentity]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  simp_rw [branchTelescopes]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, div_mul_cancel₀ _ branchesNonzero, one_mul]
  by_cases atSource : vertex = Sum.inl false
  · have notSink : vertex ≠ Sum.inl true := fun equality => terminalsDistinct (atSource.symm.trans equality)
    simp [atSource, notSink]
  · by_cases atSink : vertex = Sum.inl true <;> simp [atSource, atSink]

def flowerTerminalFlow (branches segments : ℕ)
    (branchesPositive : 0 < branches) (segmentsPositive : 0 < segments) :
    ((flowerSystem branches segments).ruleNetwork 0).Flow (Sum.inl false) (Sum.inl true) :=
  ⟨flowerCurrent branches segments,
    flowerCurrent_isUnitFlow branches segments branchesPositive segmentsPositive⟩

theorem flowerCurrent_energy (branches segments : ℕ) (branchesPositive : 0 < branches) :
    ((flowerSystem branches segments).ruleNetwork 0).energyNetwork
      (flowerCurrent branches segments) (fun _ => 1) = (segments : ℝ) / (branches : ℝ) := by
  have branchesNonzero : (branches : ℝ) ≠ 0 := (Nat.cast_pos.mpr branchesPositive).ne'
  have currentSquare (edge : Fin branches × Fin segments) :
      (flowerCurrent branches segments edge) ^ 2 = (1 / (branches : ℝ)) ^ 2 := by
    unfold flowerCurrent
    split_ifs <;> ring
  change (∑ edge : Fin branches × Fin segments, 1 * (flowerCurrent branches segments edge) ^ 2) = _
  simp_rw [one_mul, currentSquare]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_mul]
  field_simp [branchesNonzero]
  <;> ring

end
end EIGS

#print axioms EIGS.finite_chain_boundary_sum
#print axioms EIGS.flowerCurrent_isUnitFlow
#print axioms EIGS.flowerTerminalFlow
#print axioms EIGS.flowerCurrent_energy
