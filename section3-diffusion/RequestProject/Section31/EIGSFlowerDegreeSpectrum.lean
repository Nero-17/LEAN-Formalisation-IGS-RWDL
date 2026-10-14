import RequestProject.Section31.EIGSFlowerDegreeCounts
import RequestProject.Section2FiniteSpectralRadius

/-! The degree spectral value is computed from actual endpoint counts. -/

namespace EIGS
noncomputable section
open scoped Classical BigOperators

theorem flowerSystem_endpoint_degree_counts (branches segments : ℕ)
    (branchesPositive : 0 < branches) (segmentsPositive : 0 < segments) :
    ruleTailDeg (flowerSystem branches segments) 0 (Sum.inl false) 0 = branches - 1 ∧
    ruleHeadDeg (flowerSystem branches segments) 0 (Sum.inl false) 0 = 1 ∧
    ruleTailDeg (flowerSystem branches segments) 0 (Sum.inl true) 0 = 1 ∧
    ruleHeadDeg (flowerSystem branches segments) 0 (Sum.inl true) 0 = branches - 1 := by
  have zeroStep (position : Fin segments) : position.val = 0 ↔
      position = (⟨0, segmentsPositive⟩ : Fin segments) :=
    (@Fin.ext_iff segments position ⟨0, segmentsPositive⟩).symm
  have lastStep (position : Fin segments) : position.val + 1 = segments ↔
      position = (⟨segments - 1, by omega⟩ : Fin segments) := by
    rw [Fin.ext_iff]
    simp only [Fin.val_mk]
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (Finset.univ.filter (fun edge : Fin branches × Fin segments =>
      (flowerGraph branches segments).tail edge = Sum.inl false ∧ (0 : Fin 1) = 0)).card = branches - 1
    simp only [eq_self_iff_true, and_true, flowerGraph_source_tail_iff]
    simp_rw [zeroStep]
    rw [flower_filtered_edges_count branches segments (fun branch : Fin branches => branch.val ≠ 0)
      ⟨0, segmentsPositive⟩, flower_other_branches_count branches branchesPositive]
  · change (Finset.univ.filter (fun edge : Fin branches × Fin segments =>
      (flowerGraph branches segments).head edge = Sum.inl false ∧ (0 : Fin 1) = 0)).card = 1
    simp only [eq_self_iff_true, and_true, flowerGraph_source_head_iff]
    simp_rw [zeroStep]
    rw [flower_filtered_edges_count branches segments (fun branch : Fin branches => branch.val = 0)
      ⟨0, segmentsPositive⟩, flower_first_branch_count branches branchesPositive]
  · change (Finset.univ.filter (fun edge : Fin branches × Fin segments =>
      (flowerGraph branches segments).tail edge = Sum.inl true ∧ (0 : Fin 1) = 0)).card = 1
    simp only [eq_self_iff_true, and_true, flowerGraph_sink_tail_iff branches segments segmentsPositive]
    simp_rw [lastStep]
    rw [flower_filtered_edges_count branches segments (fun branch : Fin branches => branch.val = 0)
      ⟨segments - 1, by omega⟩, flower_first_branch_count branches branchesPositive]
  · change (Finset.univ.filter (fun edge : Fin branches × Fin segments =>
      (flowerGraph branches segments).head edge = Sum.inl true ∧ (0 : Fin 1) = 0)).card = branches - 1
    simp only [eq_self_iff_true, and_true, flowerGraph_sink_head_iff branches segments segmentsPositive]
    simp_rw [lastStep]
    rw [flower_filtered_edges_count branches segments (fun branch : Fin branches => branch.val ≠ 0)
      ⟨segments - 1, by omega⟩, flower_other_branches_count branches branchesPositive]

theorem flowerSystem_degree_positive_eigenpair (branches segments : ℕ)
    (branchesPositive : 0 < branches) (segmentsPositive : 0 < segments) :
    (degreeMatrix (flowerSystem branches segments)).mulVec (fun _ : Fin 1 ⊕ Fin 1 => (1 : ℝ)) =
      (branches : ℝ) • (fun _ : Fin 1 ⊕ Fin 1 => (1 : ℝ)) := by
  have counts := flowerSystem_endpoint_degree_counts branches segments branchesPositive segmentsPositive
  funext state
  rcases state with colour | colour <;>
    have colourZero : colour = 0 := Subsingleton.elim _ _ <;> subst colour
  all_goals
    simp only [Matrix.mulVec, dotProduct, mul_one, Fintype.sum_sum_type,
      Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul]
  · change (ruleTailDeg (flowerSystem branches segments) 0 (Sum.inl false) 0 : ℝ) +
      (ruleHeadDeg (flowerSystem branches segments) 0 (Sum.inl false) 0 : ℝ) = (branches : ℝ)
    rw [counts.1, counts.2.1]
    norm_num [Nat.cast_sub (show 1 ≤ branches by omega)]
  · change (ruleTailDeg (flowerSystem branches segments) 0 (Sum.inl true) 0 : ℝ) +
      (ruleHeadDeg (flowerSystem branches segments) 0 (Sum.inl true) 0 : ℝ) = (branches : ℝ)
    rw [counts.2.2.1, counts.2.2.2]
    norm_num [Nat.cast_sub (show 1 ≤ branches by omega)]

theorem flowerSystem_degreeSpectralRadius (branches segments : ℕ)
    (branchesPositive : 0 < branches) (segmentsPositive : 0 < segments) :
    finiteRealMatrixSpectralRadius (degreeMatrix (flowerSystem branches segments)) = (branches : ℝ) := by
  exact finiteRealMatrixSpectralRadius_eq_positive_eigenvalue
    (degreeMatrix (flowerSystem branches segments)) (degreeMatrix_nonneg _)
    (fun _ => 1) (branches : ℝ) (fun _ => zero_lt_one) (Nat.cast_nonneg _)
    (flowerSystem_degree_positive_eigenpair branches segments branchesPositive segmentsPositive)

end
end EIGS

#print axioms EIGS.flowerSystem_endpoint_degree_counts
#print axioms EIGS.flowerSystem_degree_positive_eigenpair
#print axioms EIGS.flowerSystem_degreeSpectralRadius
