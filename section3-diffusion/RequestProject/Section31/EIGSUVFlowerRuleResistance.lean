import RequestProject.Section31.EIGSUVFlowerFraction

/-! Exact resistance of the actual unequal-path flower rule. The lower
bound is proved for every terminal unit flow using its affine potential. -/

namespace EIGS
noncomputable section
open scoped Classical BigOperators
set_option maxHeartbeats 2200000

def uvFlowerRuleResistance (firstLength secondLength : ℕ) : ℝ :=
  (firstLength : ℝ) * secondLength / ((firstLength : ℝ) + secondLength)

def uvFlowerTerminalPotential (firstLength secondLength : ℕ)
    (vertex : UVFlowerVertex firstLength secondLength) : ℝ :=
  uvFlowerRuleResistance firstLength secondLength * (1 - uvFlowerFraction firstLength secondLength vertex)

theorem uvFlowerTerminalPotential_difference (firstLength secondLength : ℕ)
    (firstPositive : 0 < firstLength) (secondPositive : 0 < secondLength)
    (edge : UVFlowerEdge firstLength secondLength) :
    uvFlowerTerminalPotential firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).tail edge) -
      uvFlowerTerminalPotential firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).head edge) =
        uvFlowerUnitCurrent firstLength secondLength edge := by
  have firstNonzero : (firstLength : ℝ) ≠ 0 := (Nat.cast_pos.mpr firstPositive).ne'
  have secondNonzero : (secondLength : ℝ) ≠ 0 := (Nat.cast_pos.mpr secondPositive).ne'
  have denominatorNonzero : (firstLength : ℝ) + secondLength ≠ 0 :=
    (add_pos (Nat.cast_pos.mpr firstPositive) (Nat.cast_pos.mpr secondPositive)).ne'
  have difference :
      uvFlowerTerminalPotential firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).tail edge) -
        uvFlowerTerminalPotential firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).head edge) =
      -uvFlowerRuleResistance firstLength secondLength *
        (uvFlowerFraction firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).tail edge) -
          uvFlowerFraction firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).head edge)) := by
    unfold uvFlowerTerminalPotential
    ring
  rw [difference, uvFlowerFraction_edge firstLength secondLength firstPositive secondPositive]
  cases edge <;> simp only [uvFlowerRuleResistance, uvFlowerUnitCurrent, Sum.elim_inl, Sum.elim_inr] <;>
    field_simp [firstNonzero, secondNonzero, denominatorNonzero] <;> ring

theorem uvFlowerTerminalPotential_energy (firstLength secondLength : ℕ)
    (firstPositive : 0 < firstLength) (secondPositive : 0 < secondLength) :
    (((uvFlowerSystem firstLength secondLength).ruleNetwork 0).potentialNetwork
      (fun _ => 1) (fun _ => zero_lt_one)).energy
      (uvFlowerTerminalPotential firstLength secondLength) = uvFlowerRuleResistance firstLength secondLength := by
  change (∑ edge : UVFlowerEdge firstLength secondLength, (1 : ℝ)⁻¹ *
    (uvFlowerTerminalPotential firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).tail edge) -
      uvFlowerTerminalPotential firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).head edge)) ^ 2) = _
  simp_rw [uvFlowerTerminalPotential_difference firstLength secondLength firstPositive secondPositive, inv_one]
  exact uvFlowerUnitCurrent_energy firstLength secondLength firstPositive secondPositive

theorem uvFlowerFlow_energy_lower (firstLength secondLength : ℕ)
    (firstPositive : 0 < firstLength) (secondPositive : 0 < secondLength)
    (current : ((uvFlowerSystem firstLength secondLength).ruleNetwork 0).Flow (Sum.inl false) (Sum.inl true)) :
    uvFlowerRuleResistance firstLength secondLength ≤
      ((uvFlowerSystem firstLength secondLength).ruleNetwork 0).energyNetwork current.val (fun _ => 1) := by
  have terminalsDistinct : (Sum.inl false : UVFlowerVertex firstLength secondLength) ≠ Sum.inl true := by
    intro equality
    have impossible := Sum.inl.inj equality
    cases impossible
  have bound := Network.potential_difference_sq_le_flow_energy_mul_potential_energy
    ((uvFlowerSystem firstLength secondLength).ruleNetwork 0) (fun _ => 1) (fun _ => zero_lt_one)
    (Sum.inl false) (Sum.inl true) terminalsDistinct current (uvFlowerTerminalPotential firstLength secondLength)
  have terminals : uvFlowerTerminalPotential firstLength secondLength (Sum.inl false) -
      uvFlowerTerminalPotential firstLength secondLength (Sum.inl true) =
        uvFlowerRuleResistance firstLength secondLength := by
    simp [uvFlowerTerminalPotential, uvFlowerFraction]
  rw [uvFlowerTerminalPotential_energy firstLength secondLength firstPositive secondPositive, terminals] at bound
  have resistancePositive : 0 < uvFlowerRuleResistance firstLength secondLength := by
    unfold uvFlowerRuleResistance
    exact div_pos (mul_pos (Nat.cast_pos.mpr firstPositive) (Nat.cast_pos.mpr secondPositive))
      (add_pos (Nat.cast_pos.mpr firstPositive) (Nat.cast_pos.mpr secondPositive))
  nlinarith

theorem uvFlowerRule_effRes_one (firstLength secondLength : ℕ)
    (firstPositive : 0 < firstLength) (secondPositive : 0 < secondLength)
    (flowExists : Nonempty (((uvFlowerSystem firstLength secondLength).ruleNetwork 0).Flow
      (Sum.inl false) (Sum.inl true))) :
    ((uvFlowerSystem firstLength secondLength).ruleNetwork 0).effRes (Sum.inl false) (Sum.inl true)
      flowExists (fun _ => 1) = uvFlowerRuleResistance firstLength secondLength := by
  apply le_antisymm
  · have bound := ((uvFlowerSystem firstLength secondLength).ruleNetwork 0).effRes_le_energy
      (Sum.inl false) (Sum.inl true) flowExists (fun _ => zero_le_one)
      (uvFlowerTerminalFlow firstLength secondLength firstPositive secondPositive)
    change _ ≤ ((uvFlowerSystem firstLength secondLength).ruleNetwork 0).energyNetwork
      (uvFlowerUnitCurrent firstLength secondLength) (fun _ => 1) at bound
    rw [uvFlowerUnitCurrent_energy firstLength secondLength firstPositive secondPositive] at bound
    exact bound
  · exact ((uvFlowerSystem firstLength secondLength).ruleNetwork 0).le_effRes _ _ flowExists
      (fun current => uvFlowerFlow_energy_lower firstLength secondLength firstPositive secondPositive current)

theorem uvFlowerRule_effRes (firstLength secondLength : ℕ)
    (firstPositive : 0 < firstLength) (secondPositive : 0 < secondLength)
    (flowExists : Nonempty (((uvFlowerSystem firstLength secondLength).ruleNetwork 0).Flow
      (Sum.inl false) (Sum.inl true)))
    (resistances : Fin 1 → ℝ) (nonnegative : 0 ≤ resistances) :
    ((uvFlowerSystem firstLength secondLength).ruleNetwork 0).effRes (Sum.inl false) (Sum.inl true)
      flowExists resistances = uvFlowerRuleResistance firstLength secondLength * resistances 0 := by
  have resistancesEquality : resistances = resistances 0 • (fun _ : Fin 1 => (1 : ℝ)) := by
    funext colour
    have colourZero : colour = 0 := Subsingleton.elim _ _
    simp [colourZero]
  conv_lhs => rw [resistancesEquality]
  rw [Network.effRes_smul _ _ _ _ _ (nonnegative 0),
    uvFlowerRule_effRes_one firstLength secondLength firstPositive secondPositive]
  ring

end
end EIGS

#print axioms EIGS.uvFlowerTerminalPotential_difference
#print axioms EIGS.uvFlowerTerminalPotential_energy
#print axioms EIGS.uvFlowerFlow_energy_lower
#print axioms EIGS.uvFlowerRule_effRes_one
#print axioms EIGS.uvFlowerRule_effRes
