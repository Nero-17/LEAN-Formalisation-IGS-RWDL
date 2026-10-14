import RequestProject.Section31.EIGSFlowerRuleGraph
import RequestProject.Section2FiniteSpectralRadius

/-! The chosen orientation gives a strictly positive actual degree
matrix whenever there are at least two branches. Four explicit endpoint
edges supply its four positive entries. -/

namespace EIGS
noncomputable section
open scoped Classical

theorem flowerSystem_degreeMatrix_positive (branches segments : ℕ)
    (branchesAtLeastTwo : 2 ≤ branches) (segmentsAtLeastTwo : 2 ≤ segments)
    (first second : Fin 1 ⊕ Fin 1) :
    0 < degreeMatrix (flowerSystem branches segments) first second := by
  rcases first with first | first <;> rcases second with second | second <;>
    have firstZero : first = 0 := Subsingleton.elim _ _ <;>
    have secondZero : second = 0 := Subsingleton.elim _ _ <;>
    subst first <;> subst second
  · change 0 < (ruleTailDeg (flowerSystem branches segments) 0 (Sum.inl false) 0 : ℝ)
    apply Nat.cast_pos.mpr
    apply Finset.card_pos.mpr
    refine ⟨(⟨1, by omega⟩, ⟨0, by omega⟩), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simp [flowerSystem, flowerGraph, flowerEdgeStart, flowerPoint]
  · change 0 < (ruleHeadDeg (flowerSystem branches segments) 0 (Sum.inl false) 0 : ℝ)
    apply Nat.cast_pos.mpr
    apply Finset.card_pos.mpr
    refine ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simp [flowerSystem, flowerGraph, flowerEdgeStart, flowerPoint]
  · change 0 < (ruleTailDeg (flowerSystem branches segments) 0 (Sum.inl true) 0 : ℝ)
    apply Nat.cast_pos.mpr
    apply Finset.card_pos.mpr
    refine ⟨(⟨0, by omega⟩, ⟨segments - 1, by omega⟩), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    have lastStep : segments - 1 + 1 = segments := by omega
    simp [flowerSystem, flowerGraph, flowerEdgeEnd, flowerPoint, lastStep, show segments ≠ 0 by omega]
  · change 0 < (ruleHeadDeg (flowerSystem branches segments) 0 (Sum.inl true) 0 : ℝ)
    apply Nat.cast_pos.mpr
    apply Finset.card_pos.mpr
    refine ⟨(⟨1, by omega⟩, ⟨segments - 1, by omega⟩), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    have lastStep : segments - 1 + 1 = segments := by omega
    simp [flowerSystem, flowerGraph, flowerEdgeEnd, flowerPoint, lastStep, show segments ≠ 0 by omega]

theorem flowerSystem_degreeMatrix_primitive (branches segments : ℕ)
    (branchesAtLeastTwo : 2 ≤ branches) (segmentsAtLeastTwo : 2 ≤ segments) :
    (degreeMatrix (flowerSystem branches segments)).IsPrimitive := by
  refine ⟨fun first second =>
    (flowerSystem_degreeMatrix_positive branches segments branchesAtLeastTwo segmentsAtLeastTwo first second).le,
      1, by omega, ?_⟩
  intro first second
  rw [pow_one]
  exact flowerSystem_degreeMatrix_positive branches segments branchesAtLeastTwo segmentsAtLeastTwo first second

end
end EIGS

#print axioms EIGS.flowerSystem_degreeMatrix_positive
#print axioms EIGS.flowerSystem_degreeMatrix_primitive
