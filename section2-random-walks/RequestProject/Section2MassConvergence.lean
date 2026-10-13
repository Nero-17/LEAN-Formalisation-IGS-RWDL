import RequestProject.Section2MassGrowth
import RequestProject.NonlinearConvergence

/-! Colour-resolved mass convergence for the actual substitution edge sets. -/

namespace EIGS

open scoped BigOperators
open Filter Topology

variable {K : ℕ}

theorem RenormMap.positive_iterate_normalized_limit (renormalization : RenormMap K)
    (colours_positive : 0 < K)
    (strongly_positive : ∀ vector : Fin K → ℝ, 0 ≤ vector → vector ≠ 0 →
      ∀ colour, 0 < renormalization.apply vector colour)
    {reference : Fin K → ℝ} {rate : ℝ}
    (reference_positive : ∀ colour, 0 < reference colour) (rate_positive : 0 < rate)
    (reference_normalized : (∑ colour, reference colour) = 1)
    (eigenpair : renormalization.apply reference = rate • reference)
    (initial : Fin K → ℝ) (initial_positive : ∀ colour, 0 < initial colour) :
    ∃ limit : ℝ, 0 < limit ∧
      Tendsto (fun level => fun colour =>
        renormalization.apply^[level] initial colour / rate ^ level)
        atTop (nhds (limit • reference)) := by
  classical
  have colours_nonempty : (Finset.univ : Finset (Fin K)).Nonempty :=
    ⟨⟨0, colours_positive⟩, Finset.mem_univ _⟩
  let lower_ratio : ℝ := Finset.univ.inf' colours_nonempty
    (fun colour => initial colour / reference colour)
  let lower_reference : ℝ := Finset.univ.inf' colours_nonempty reference
  let upper_ratio : ℝ := ∑ colour, initial colour / reference colour
  have lower_ratio_positive : 0 < lower_ratio :=
    (Finset.lt_inf'_iff _).mpr (fun colour _ =>
      div_pos (initial_positive colour) (reference_positive colour))
  have lower_reference_positive : 0 < lower_reference :=
    (Finset.lt_inf'_iff _).mpr (fun colour _ => reference_positive colour)
  have upper_ratio_positive : 0 < upper_ratio := Finset.sum_pos
    (fun colour _ => div_pos (initial_positive colour) (reference_positive colour))
      colours_nonempty
  have initial_lower : lower_ratio • reference ≤ initial := by
    intro colour
    exact (le_div_iff₀ (reference_positive colour)).mp
      (Finset.inf'_le _ (Finset.mem_univ colour))
  have initial_upper : initial ≤ upper_ratio • reference := by
    intro colour
    exact (div_le_iff₀ (reference_positive colour)).mp
      (Finset.single_le_sum (fun index _ =>
        (div_pos (initial_positive index) (reference_positive index)).le)
          (Finset.mem_univ colour))
  let sequence : ℕ → (Fin K → ℝ) := fun level colour =>
    renormalization.apply^[level] initial colour / rate ^ level
  have recurrence (level : ℕ) :
      renormalization.apply (sequence level) = rate • sequence (level + 1) := by
    have sequence_eq : sequence level =
        (rate ^ level)⁻¹ • renormalization.apply^[level] initial := by
      ext colour
      simp only [sequence, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [sequence_eq, renormalization.apply_smul _
      (inv_nonneg.mpr (pow_nonneg rate_positive.le level))]
    ext colour
    simp only [sequence, Pi.smul_apply, smul_eq_mul, Function.iterate_succ_apply']
    rw [pow_succ]
    field_simp
  have bounds (level : ℕ) (colour : Fin K) :
      lower_ratio * lower_reference ≤ sequence level colour ∧
        sequence level colour ≤ upper_ratio := by
    have lower_iterate := renormalization.smul_eigen_le_iterate
      (fun index => (reference_positive index).le) rate_positive.le eigenpair
      lower_ratio_positive.le initial_lower level colour
    have upper_iterate := renormalization.iterate_le_smul_eigen rate_positive.le eigenpair
      upper_ratio_positive.le (fun index => (initial_positive index).le)
      initial_upper level colour
    have reference_lower : lower_reference ≤ reference colour :=
      Finset.inf'_le _ (Finset.mem_univ colour)
    have reference_upper : reference colour ≤ 1 := by
      rw [← reference_normalized]
      exact Finset.single_le_sum (fun index _ => (reference_positive index).le)
        (Finset.mem_univ colour)
    constructor
    · apply (le_div_iff₀ (pow_pos rate_positive level)).mpr
      change (lower_ratio * rate ^ level) * reference colour ≤ _ at lower_iterate
      calc
        (lower_ratio * lower_reference) * rate ^ level =
            (lower_ratio * rate ^ level) * lower_reference := by ring
        _ ≤ (lower_ratio * rate ^ level) * reference colour :=
          mul_le_mul_of_nonneg_left reference_lower (by positivity)
        _ ≤ _ := lower_iterate
    · apply (div_le_iff₀ (pow_pos rate_positive level)).mpr
      change _ ≤ (upper_ratio * rate ^ level) * reference colour at upper_iterate
      exact upper_iterate.trans
        (mul_le_of_le_one_right (by positivity) reference_upper)
  exact renormalization.normalized_sequence_converges colours_positive strongly_positive
    reference_positive rate_positive reference_normalized eigenpair sequence recurrence
    (mul_pos lower_ratio_positive lower_reference_positive) bounds

theorem chiVec_normalized_limit_of_positive_matrix (data : RuleData K)
    (matrix_positive : ∀ first second, 0 < massMatrixR data first second)
    {reference : Fin K → ℝ} {rate : ℝ}
    (reference_positive : ∀ colour, 0 < reference colour) (rate_positive : 0 < rate)
    (reference_normalized : (∑ colour, reference colour) = 1)
    (eigenpair : (massMatrixR data).transpose.mulVec reference = rate • reference) :
    ∃ limit : ℝ, 0 < limit ∧
      Tendsto (fun level => fun colour => chiVec data level colour / rate ^ level)
        atTop (nhds (limit • reference)) := by
  classical
  let renormalization := matrixRenormMap (massMatrixR data).transpose
    (fun first second => (matrix_positive second first).le)
  have first_positive (colour : Fin K) : 0 < chiVec data 1 colour := by
    rw [show 1 = 0 + 1 from rfl, chiVec_succ]
    simpa [Matrix.vecMul, dotProduct, chiVec, chiCount_zero] using
      matrix_positive data.ι colour
  have recurrence (level : ℕ) : renormalization.apply (chiVec data level) =
      chiVec data (level + 1) := by
    rw [matrixRenormMap_apply, chiVec_succ]
    ext colour
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.transpose_apply, mul_comm]
  have shifted_iterate (level : ℕ) :
      renormalization.apply^[level] (chiVec data 1) = chiVec data (level + 1) := by
    induction level with
    | zero => rfl
    | succ level induction_hypothesis =>
      rw [Function.iterate_succ_apply', induction_hypothesis, recurrence]
  obtain ⟨limit, limit_positive, convergence⟩ :=
    renormalization.positive_iterate_normalized_limit
      (lt_of_le_of_lt (Nat.zero_le data.ι.val) data.ι.isLt)
      (matrixRenormMap_strongly_positive _ (fun first second => matrix_positive second first))
      reference_positive rate_positive reference_normalized
      (by simpa only [renormalization, matrixRenormMap_apply] using eigenpair)
      (chiVec data 1) first_positive
  refine ⟨limit / rate, div_pos limit_positive rate_positive, ?_⟩
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply tendsto_pi_nhds.mpr
  intro colour
  have coordinate_limit := (tendsto_pi_nhds.mp convergence colour).div_const rate
  simpa only [shifted_iterate, pow_succ, div_div, Pi.smul_apply, smul_eq_mul,
    mul_div_assoc, div_mul_eq_mul_div] using coordinate_limit

/-- Replacing the initial colour counts exactly the descendants of one edge of
that colour. The rate and limiting colour distribution are common to all cells. -/
theorem descendant_colour_count_normalized_limits (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ (rate : ℝ) (reference amplitude : Fin K → ℝ),
      0 < rate ∧ (∀ colour, 0 < reference colour) ∧
      (∑ colour, reference colour) = 1 ∧ (∀ colour, 0 < amplitude colour) ∧
      ∀ initialColour,
        Tendsto (fun level => fun colour =>
          chiVec { system.toRuleData with ι := initialColour } level colour / rate ^ level)
          atTop (nhds (amplitude initialColour • reference)) := by
  have matrix_positive := massMatrixR_positive system rule_connected distance_positive
  obtain ⟨reference, rate, reference_positive, rate_positive, reference_normalized, eigenpair⟩ :=
    positive_matrix_eigenpair
      (lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt)
      (massMatrixR system.toRuleData).transpose
      (fun first second => matrix_positive second first)
  have individual_limit (initialColour : Fin K) : ∃ limit : ℝ, 0 < limit ∧
      Tendsto (fun level => fun colour =>
        chiVec { system.toRuleData with ι := initialColour } level colour / rate ^ level)
        atTop (nhds (limit • reference)) :=
    chiVec_normalized_limit_of_positive_matrix
      { system.toRuleData with ι := initialColour } matrix_positive reference_positive
      rate_positive reference_normalized eigenpair
  choose amplitude amplitude_positive convergence using individual_limit
  exact ⟨rate, reference, amplitude, rate_positive, reference_positive,
    reference_normalized, amplitude_positive, convergence⟩

theorem totalEdges_normalized_limit_of_colour_limit (data : RuleData K)
    {reference : Fin K → ℝ} {rate limit : ℝ}
    (reference_normalized : (∑ colour, reference colour) = 1)
    (convergence : Tendsto
      (fun level => fun colour => chiVec data level colour / rate ^ level)
      atTop (nhds (limit • reference))) :
    Tendsto (fun level => (totalEdges data level : ℝ) / rate ^ level)
      atTop (nhds limit) := by
  have sum_limit := tendsto_finset_sum (Finset.univ : Finset (Fin K))
    (fun colour _ => tendsto_pi_nhds.mp convergence colour)
  simpa only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, reference_normalized,
    mul_one, ← Finset.sum_div, ← totalEdges_eq_sum] using sum_limit

theorem descendant_edge_count_normalized_limits (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ (rate : ℝ) (amplitude : Fin K → ℝ),
      0 < rate ∧ (∀ colour, 0 < amplitude colour) ∧ ∀ initialColour,
        Tendsto (fun level =>
          (totalEdges { system.toRuleData with ι := initialColour } level : ℝ) / rate ^ level)
          atTop (nhds (amplitude initialColour)) := by
  obtain ⟨rate, reference, amplitude, rate_positive, reference_positive,
    reference_normalized, amplitude_positive, convergence⟩ :=
    descendant_colour_count_normalized_limits system rule_connected distance_positive
  exact ⟨rate, amplitude, rate_positive, amplitude_positive, fun initialColour =>
    totalEdges_normalized_limit_of_colour_limit
      { system.toRuleData with ι := initialColour } reference_normalized
      (convergence initialColour)⟩

end EIGS
