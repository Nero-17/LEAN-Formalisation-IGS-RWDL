import RequestProject.Section31.EIGSRecentVertexIncidence
import RequestProject.Section31.EIGSPositiveDegreeAddressCollar

/-! Actual collar/incidence estimates from a positive normalized degree eigenpair.
The original address measure and oriented rule graphs are unchanged. Candidate. -/

namespace EIGS
open MeasureTheory Filter Matrix
open scoped Classical BigOperators Topology ENNReal
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem exists_xiRecentVertex_incidence_bound_of_positive_degree_data (system : EIGSData K)
    (degreeData : XiPositiveDegreeSpectralData system) :
    ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ coarse width (vertex : XiVtx system (coarse + width)),
      (∀ old : XiVtx system coarse, xiForward system coarse width old ≠ vertex) →
      (xiVertexIncidenceCount system (coarse + width) vertex : ℝ) ≤
        coefficient * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ width := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  let weights := degreeData.vector
  have weightsPositive := degreeData.positive
  have ratePositive := zero_lt_one.trans degreeData.rate_gt_one
  have normalized := degreeData.normalized
  have eigenpair := degreeData.eigenpair
  obtain ⟨minimumState, _, minimumBound⟩ := Finset.univ.exists_min_image weights Finset.univ_nonempty
  let birthBound : ℝ := 1 + 2 * ∑ colour : Fin K, (Fintype.card (system.rule colour).E : ℝ)
  have birthBoundPositive : 0 < birthBound := by dsimp only [birthBound]; positivity
  have weightsAtMostOne (state : Fin K ⊕ Fin K) : weights state ≤ 1 := by
    rw [← normalized]
    exact Finset.single_le_sum (fun other _ => (weightsPositive other).le) (Finset.mem_univ _)
  have weightedAtMostIncidence (level : ℕ) (vertex : XiVtx system level) :
      (∑ state, degVec system level vertex state * weights state) ≤
        (xiVertexIncidenceCount system level vertex : ℝ) := by
    rw [xiVertexIncidenceCount_eq_degree_state_sum]
    apply Finset.sum_le_sum
    intro state _
    have nonnegative : 0 ≤ degVec system level vertex state := by cases state <;> exact Nat.cast_nonneg _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (weightsAtMostOne state) nonnegative
  have oldWeighted (level : ℕ) (vertex : XiVtx system level) :
      (∑ state, degVec system (level + 1) (Sum.inl vertex) state * weights state) =
        finiteRealMatrixSpectralRadius (degreeMatrix system) *
          (∑ state, degVec system level vertex state * weights state) := by
    rw [degVec_inl]
    change Matrix.vecMul (degVec system level vertex) (degreeMatrix system) ⬝ᵥ weights = _
    rw [← Matrix.dotProduct_mulVec, eigenpair]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro state _
    ring
  have recentWeighted : ∀ coarse width (vertex : XiVtx system (coarse + width)),
      (∀ old : XiVtx system coarse, xiForward system coarse width old ≠ vertex) →
      (∑ state, degVec system (coarse + width) vertex state * weights state) ≤
        birthBound * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ width := by
    intro coarse width
    induction width with
    | zero =>
      intro vertex noOld
      exact (noOld vertex rfl).elim
    | succ width induction =>
      intro vertex noOld
      cases vertex with
      | inl previous =>
        have previousNoOld : ∀ old : XiVtx system coarse, xiForward system coarse width old ≠ previous :=
          fun old equality => noOld old (congrArg Sum.inl equality)
        change (∑ state, degVec system ((coarse + width) + 1) (Sum.inl previous) state * weights state) ≤ _
        rw [oldWeighted]
        exact (mul_le_mul_of_nonneg_left (induction previous previousNoOld) ratePositive.le).trans_eq
          (by rw [pow_succ]; ring)
      | inr privateVertex =>
        have birthIncidence := xiPrivateVertex_incidence_bound system (coarse + width) privateVertex.1 privateVertex.2
        have ruleBound : 2 * (Fintype.card (system.rule (XiCol system.toRuleData (coarse + width) privateVertex.1)).E : ℝ) ≤
            birthBound := by
          have term := Finset.single_le_sum
            (fun colour _ => Nat.cast_nonneg (α := ℝ) (Fintype.card (system.rule colour).E))
            (Finset.mem_univ (XiCol system.toRuleData (coarse + width) privateVertex.1))
          dsimp only [birthBound]
          linarith
        have atBirth := (weightedAtMostIncidence _ _).trans (birthIncidence.trans ruleBound)
        exact atBirth.trans (by
          have powerAtLeastOne : 1 ≤ finiteRealMatrixSpectralRadius (degreeMatrix system) ^ (width + 1) :=
            one_le_pow₀ degreeData.rate_gt_one.le
          simpa only [mul_one] using mul_le_mul_of_nonneg_left powerAtLeastOne birthBoundPositive.le)
  refine ⟨birthBound / weights minimumState, div_pos birthBoundPositive (weightsPositive _), ?_⟩
  intro coarse width vertex noOld
  have minimumWeighted : weights minimumState * (xiVertexIncidenceCount system (coarse + width) vertex : ℝ) ≤
      ∑ state, degVec system (coarse + width) vertex state * weights state := by
    rw [xiVertexIncidenceCount_eq_degree_state_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro state _
    have nonnegative : 0 ≤ degVec system (coarse + width) vertex state := by cases state <;> exact Nat.cast_nonneg _
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (minimumBound state (Finset.mem_univ _)) nonnegative
  have bound := minimumWeighted.trans (recentWeighted coarse width vertex noOld)
  calc
    _ ≤ birthBound * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ width / weights minimumState :=
      (le_div_iff₀ (weightsPositive minimumState)).mpr (by simpa only [mul_comm] using bound)
    _ = _ := by ring

theorem exists_xiNoncollar_endpoint_incidence_bound_of_positive_degree_data (system : EIGSData K)
    (degreeData : XiPositiveDegreeSpectralData system) :
    ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ coarse width (address : XiEdgeAddress system),
      address ∉ xiAddressEndpointCollar system coarse width →
      (xiVertexIncidenceCount system (coarse + width)
        (XiTail system (coarse + width) (xiAddressEdge system (coarse + width) address)) : ℝ) +
      (xiVertexIncidenceCount system (coarse + width)
        (XiHead system (coarse + width) (xiAddressEdge system (coarse + width) address)) : ℝ) ≤
          coefficient * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ width := by
  obtain ⟨coefficient, coefficientPositive, recentBound⟩ := exists_xiRecentVertex_incidence_bound_of_positive_degree_data system degreeData
  refine ⟨2 * coefficient, by positivity, ?_⟩
  intro coarse width address avoids
  have tailNoOld : ∀ old : XiVtx system coarse, xiForward system coarse width old ≠
      XiTail system (coarse + width) (xiAddressEdge system (coarse + width) address) := by
    intro old equality
    apply avoids
    refine ⟨old, ?_⟩
    unfold xiAddressStarWeight xiEdgeStarMultiplicity
    rw [equality]
    split_ifs <;> norm_num at *
  have headNoOld : ∀ old : XiVtx system coarse, xiForward system coarse width old ≠
      XiHead system (coarse + width) (xiAddressEdge system (coarse + width) address) := by
    intro old equality
    apply avoids
    refine ⟨old, ?_⟩
    unfold xiAddressStarWeight xiEdgeStarMultiplicity
    rw [equality]
    split_ifs <;> norm_num at *
  exact (add_le_add (recentBound coarse width _ tailNoOld)
    (recentBound coarse width _ headNoOld)).trans_eq (by ring)

end
end EIGS

#print axioms EIGS.exists_xiRecentVertex_incidence_bound_of_positive_degree_data
#print axioms EIGS.exists_xiNoncollar_endpoint_incidence_bound_of_positive_degree_data

