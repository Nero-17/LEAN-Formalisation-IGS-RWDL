import RequestProject.Section31.EIGSVertexMassAsymptotics
import RequestProject.Section31.EIGSEdgeAddressMeasure
import RequestProject.Section2StarVolume

/-! Actual vertex-count amplitudes from actual colour counts and vertex births. -/

namespace EIGS

open Filter Topology
open scoped BigOperators Classical

noncomputable section

variable {K : ℕ}

theorem rule_edge_card_ge_two (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour)) (colour : Fin K) :
    2 ≤ Fintype.card (system.rule colour).E := by
  obtain ⟨interior⟩ := rule_interior_nonempty system ruleConnected plantingNonadjacent colour
  have vertexLower : 3 ≤ Fintype.card (system.rule colour).V :=
    Nat.succ_le_of_lt (Fintype.two_lt_card_iff.mpr
      ⟨system.plantPlus colour, system.plantMinus colour, interior.val,
        system.plant_ne colour, interior.property.1.symm, interior.property.2.symm⟩)
  have vertexUpper := (ruleConnected colour).card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at vertexUpper
  have edgeUpper := (system.ruleNetwork colour).simpleGraph_edge_card_le
  change (ruleSG system colour).edgeFinset.card ≤ Fintype.card (system.rule colour).E at edgeUpper
  omega

theorem XiMassParameters.rate_ge_two (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (mass : XiMassParameters system) : 2 ≤ mass.rate := by
  obtain ⟨minimumColour, _, minimumCondition⟩ := Finset.exists_min_image
    Finset.univ mass.amplitude ⟨system.initCol, Finset.mem_univ _⟩
  have cardinalLower : (2 : ℝ) ≤ Fintype.card (system.rule minimumColour).E := by
    exact_mod_cast rule_edge_card_ge_two system ruleConnected plantingNonadjacent minimumColour
  have weightedLower : 2 * mass.amplitude minimumColour ≤
      mass.rate * mass.amplitude minimumColour := by
    calc
      _ ≤ (Fintype.card (system.rule minimumColour).E : ℝ) * mass.amplitude minimumColour :=
        mul_le_mul_of_nonneg_right cardinalLower (mass.amplitude_positive _).le
      _ = ∑ edge : (system.rule minimumColour).E, mass.amplitude minimumColour := by simp
      _ ≤ ∑ edge : (system.rule minimumColour).E,
          mass.amplitude ((system.rule minimumColour).col edge) :=
        Finset.sum_le_sum (fun edge _ => minimumCondition _ (Finset.mem_univ _))
      _ = _ := mass.sum_rule_amplitudes minimumColour
  nlinarith [mass.amplitude_positive minimumColour]

theorem xiEdge_colour_weight_sum (data : RuleData K) (level : ℕ) (weight : Fin K → ℝ) :
    (∑ edge : XiEdge data level, weight (XiCol data level edge)) =
      ∑ colour, chiVec data level colour * weight colour := by
  symm
  simp only [chiVec, chiCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro edge _
  simp

theorem xiInteriorBirthCount_normalized_limit (system : EIGSData K)
    {rate : ℝ} {reference : Fin K → ℝ} {amplitude : ℝ}
    (rateGreaterThanOne : 1 < rate) (initialColour : Fin K)
    (colourConvergence : Tendsto (fun level => fun colour =>
      chiVec {system.toRuleData with ι := initialColour} level colour / rate ^ level)
      atTop (𝓝 (amplitude • reference))) :
    Tendsto (fun level => (xiInteriorBirthCount system initialColour level : ℝ) / rate ^ level)
      atTop (𝓝 (amplitude * (∑ colour, reference colour *
        (xiRuleInteriorCount system colour : ℝ)) / (rate - 1))) := by
  have birthConvergence := tendsto_finset_sum (Finset.univ : Finset (Fin K))
    (fun colour _ => (tendsto_pi_nhds.mp colourConvergence colour).mul_const
      (xiRuleInteriorCount system colour : ℝ))
  have weightedBirthConvergence :
      Tendsto (fun level =>
        (∑ edge : XiEdge {system.toRuleData with ι := initialColour} level,
          (xiRuleInteriorCount system
            (XiCol {system.toRuleData with ι := initialColour} level edge) : ℝ)) / rate ^ level)
        atTop (𝓝 (amplitude * ∑ colour, reference colour * (xiRuleInteriorCount system colour : ℝ))) := by
    convert birthConvergence using 1
    · ext level
      rw [xiEdge_colour_weight_sum {system.toRuleData with ι := initialColour} level
        (fun colour => (xiRuleInteriorCount system colour : ℝ)), Finset.sum_div]
      apply Finset.sum_congr rfl
      intro colour _
      ring
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_assoc]
  simpa only [xiInteriorBirthCount, Nat.cast_sum] using
    normalized_partial_sum_tendsto rateGreaterThanOne weightedBirthConvergence

theorem xiVertex_count_normalized_limit (system : EIGSData K)
    {rate : ℝ} {reference : Fin K → ℝ} {amplitude : ℝ}
    (rateGreaterThanOne : 1 < rate) (initialColour : Fin K)
    (colourConvergence : Tendsto (fun level => fun colour =>
      chiVec {system.toRuleData with ι := initialColour} level colour / rate ^ level)
      atTop (𝓝 (amplitude • reference))) :
    Tendsto (fun level => (Fintype.card (XiVtx {system with initCol := initialColour} level) : ℝ) /
      rate ^ level) atTop (𝓝 (amplitude *
        ((∑ colour, reference colour * (xiRuleInteriorCount system colour : ℝ)) / (rate - 1)))) := by
  have inverseNonnegative : 0 ≤ rate⁻¹ := inv_nonneg.mpr (zero_le_one.trans rateGreaterThanOne.le)
  have inverseLessThanOne : rate⁻¹ < 1 :=
    (inv_lt_one₀ (zero_lt_one.trans rateGreaterThanOne)).mpr rateGreaterThanOne
  have initialVertexLimit : Tendsto (fun level : ℕ => (2 : ℝ) / rate ^ level) atTop (𝓝 0) := by
    simpa only [inv_pow, div_eq_mul_inv, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one inverseNonnegative inverseLessThanOne).const_mul (2 : ℝ)
  have birthLimit := xiInteriorBirthCount_normalized_limit system rateGreaterThanOne initialColour colourConvergence
  convert initialVertexLimit.add birthLimit using 1
  · ext level
    rw [xiVtx_card_eq_two_add_interior_births, Nat.cast_add, Nat.cast_ofNat, add_div]
    rfl
  · simp only [zero_add, mul_div_assoc]

end
end EIGS


#print axioms EIGS.rule_edge_card_ge_two
#print axioms EIGS.XiMassParameters.rate_ge_two
#print axioms EIGS.xiEdge_colour_weight_sum
#print axioms EIGS.xiInteriorBirthCount_normalized_limit
#print axioms EIGS.xiVertex_count_normalized_limit
