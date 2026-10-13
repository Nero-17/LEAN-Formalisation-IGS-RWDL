import RequestProject.Section31.EIGSDiscreteTraceConvergence

/-! Normalized actual resistance iterates converge along every prescribed
positive Perron ray. This removes dependence on separate eigenvector choices. -/

namespace EIGS

open Filter Topology

variable {K : ℕ}

theorem exists_normalized_resistance_limit_of_positive_eigenpair (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour) :
    ∃ normalization : ℝ, 0 < normalization ∧
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (nhds (normalization • resistanceVector)) := by
  classical
  have coloursPositive : 0 < K := lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt
  have vectorSumPositive : 0 < ∑ colour, resistanceVector colour :=
    (vectorPositive system.initCol).trans_le
      (Finset.single_le_sum (fun colour _ => (vectorPositive colour).le) (Finset.mem_univ system.initCol))
  have normalizedPositive : ∀ colour, 0 < resistanceVector colour / ∑ index, resistanceVector index :=
    fun colour => div_pos (vectorPositive colour) vectorSumPositive
  have normalizedSum : (∑ colour, resistanceVector colour / ∑ index, resistanceVector index) = 1 := by
    rw [← Finset.sum_div, div_self vectorSumPositive.ne']
  have vectorEigenpair : (system.connectedRuleSystem rulesConnected).toRenormMap.apply resistanceVector =
      resistanceRate • resistanceVector := funext renormalizationEigenpair
  have normalizedIdentity : (fun colour => resistanceVector colour / ∑ index, resistanceVector index) =
      (∑ index, resistanceVector index)⁻¹ • resistanceVector := by
    funext colour
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have normalizedEigenpair : (system.connectedRuleSystem rulesConnected).toRenormMap.apply
      (fun colour => resistanceVector colour / ∑ index, resistanceVector index) =
      resistanceRate • (fun colour => resistanceVector colour / ∑ index, resistanceVector index) := by
    rw [normalizedIdentity, (system.connectedRuleSystem rulesConnected).toRenormMap.apply_smul _
      (inv_pos.2 vectorSumPositive).le, vectorEigenpair, smul_smul, smul_smul, mul_comm]
  obtain ⟨normalizedLimit, limitPositive, convergence⟩ :=
    (system.connectedRuleSystem rulesConnected).toRenormMap.iterate_normalized_limit_of_strongly_positive
      coloursPositive ((system.connectedRuleSystem rulesConnected).renorm_strongly_positive distancePositive)
      normalizedPositive ratePositive normalizedSum normalizedEigenpair
  refine ⟨normalizedLimit / (∑ colour, resistanceVector colour), div_pos limitPositive vectorSumPositive, ?_⟩
  have limitIdentity : normalizedLimit • (fun colour => resistanceVector colour / ∑ index, resistanceVector index) =
      (normalizedLimit / (∑ colour, resistanceVector colour)) • resistanceVector := by
    funext colour
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [limitIdentity] at convergence
  exact convergence

end EIGS
