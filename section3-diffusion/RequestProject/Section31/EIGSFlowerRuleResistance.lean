import RequestProject.Section31.EIGSFlowerUnitFlow
import RequestProject.Section31.EIGSFlowerRuleConnectivity

/-! The resistance of the actual parallel-chain rule, obtained from a
unit flow and the height potential on its unchanged oriented edges. -/

namespace EIGS
noncomputable section
open scoped Classical BigOperators

theorem flowerHeightPotential_energy (branches segments : ℕ) :
    (((flowerSystem branches segments).ruleNetwork 0).potentialNetwork
      (fun _ => 1) (fun _ => zero_lt_one)).energy
      (fun vertex => (flowerHeight branches segments vertex : ℝ)) =
        (branches : ℝ) * (segments : ℝ) := by
  have edgeEnergy (edge : Fin branches × Fin segments) :
      ((flowerHeight branches segments ((flowerGraph branches segments).tail edge) : ℝ) -
        (flowerHeight branches segments ((flowerGraph branches segments).head edge) : ℝ)) ^ 2 = 1 := by
    rcases flowerGraph_edge_height branches segments edge with heights | heights <;>
      rw [heights.1, heights.2] <;> push_cast <;> ring
  change (∑ edge : Fin branches × Fin segments,
    (1 : ℝ)⁻¹ *
      ((flowerHeight branches segments ((flowerGraph branches segments).tail edge) : ℝ) -
        (flowerHeight branches segments ((flowerGraph branches segments).head edge) : ℝ)) ^ 2) = _
  simp_rw [inv_one, one_mul, edgeEnergy]
  simp [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]

theorem flowerFlow_energy_lower (branches segments : ℕ)
    (branchesPositive : 0 < branches) (segmentsPositive : 0 < segments)
    (current : ((flowerSystem branches segments).ruleNetwork 0).Flow
      (Sum.inl false) (Sum.inl true)) :
    (segments : ℝ) / (branches : ℝ) ≤
      ((flowerSystem branches segments).ruleNetwork 0).energyNetwork current.val (fun _ => 1) := by
  have branchesRealPositive : 0 < (branches : ℝ) := Nat.cast_pos.mpr branchesPositive
  have segmentsRealPositive : 0 < (segments : ℝ) := Nat.cast_pos.mpr segmentsPositive
  have terminalsDistinct : (Sum.inl false : Bool ⊕ (Fin branches × Fin (segments - 1))) ≠ Sum.inl true := by
    intro equality
    have impossible := Sum.inl.inj equality
    cases impossible
  have bound := ((flowerSystem branches segments).ruleNetwork 0).
    potential_difference_sq_le_flow_energy_mul_potential_energy
      (fun _ => 1) (fun _ => zero_lt_one) (Sum.inl false) (Sum.inl true)
      terminalsDistinct current (fun vertex => (flowerHeight branches segments vertex : ℝ))
  rw [flowerHeightPotential_energy] at bound
  simp only [flowerHeight, Bool.false_eq_true, ↓reduceIte, Nat.cast_zero, zero_sub,
    neg_sq] at bound
  apply (div_le_iff₀ branchesRealPositive).2
  nlinarith

theorem flowerRule_effRes_one (branches segments : ℕ)
    (branchesPositive : 0 < branches) (segmentsPositive : 0 < segments)
    (flowExists : Nonempty (((flowerSystem branches segments).ruleNetwork 0).Flow
      (Sum.inl false) (Sum.inl true))) :
    ((flowerSystem branches segments).ruleNetwork 0).effRes (Sum.inl false) (Sum.inl true)
      flowExists (fun _ => 1) = (segments : ℝ) / (branches : ℝ) := by
  apply le_antisymm
  · have bound := ((flowerSystem branches segments).ruleNetwork 0).effRes_le_energy
      (Sum.inl false) (Sum.inl true) flowExists (fun _ => zero_le_one)
        (flowerTerminalFlow branches segments branchesPositive segmentsPositive)
    simpa only [flowerTerminalFlow, flowerCurrent_energy] using bound
  · exact ((flowerSystem branches segments).ruleNetwork 0).le_effRes _ _ flowExists
      (fun current => flowerFlow_energy_lower branches segments branchesPositive segmentsPositive current)

theorem flowerRule_effRes (branches segments : ℕ)
    (branchesPositive : 0 < branches) (segmentsPositive : 0 < segments)
    (flowExists : Nonempty (((flowerSystem branches segments).ruleNetwork 0).Flow
      (Sum.inl false) (Sum.inl true)))
    (resistances : Fin 1 → ℝ) (resistancesNonnegative : 0 ≤ resistances) :
    ((flowerSystem branches segments).ruleNetwork 0).effRes (Sum.inl false) (Sum.inl true)
      flowExists resistances = (segments : ℝ) / (branches : ℝ) * resistances 0 := by
  have resistancesEquality : resistances = resistances 0 • (fun _ : Fin 1 => (1 : ℝ)) := by
    funext colour
    have colourZero : colour = 0 := Subsingleton.elim _ _
    simp [colourZero]
  conv_lhs => rw [resistancesEquality]
  rw [Network.effRes_smul _ _ _ _ _ (resistancesNonnegative 0),
    flowerRule_effRes_one branches segments branchesPositive segmentsPositive]
  ring

theorem flowerSystem_Psi (branches segments : ℕ)
    (branchesPositive : 0 < branches) (segmentsAtLeastTwo : 2 ≤ segments)
    (resistances : Fin 1 → ℝ) (resistancesNonnegative : 0 ≤ resistances) :
    ((flowerSystem branches segments).ruleFamily
      (flowerSystem_connected branches segments branchesPositive segmentsAtLeastTwo)).Psi
        resistances = fun _ => (segments : ℝ) / (branches : ℝ) * resistances 0 := by
  funext colour
  have colourZero : colour = 0 := Subsingleton.elim _ _
  subst colour
  exact flowerRule_effRes branches segments branchesPositive (by omega)
    _ resistances resistancesNonnegative

end
end EIGS

#print axioms EIGS.flowerHeightPotential_energy
#print axioms EIGS.flowerFlow_energy_lower
#print axioms EIGS.flowerRule_effRes_one
#print axioms EIGS.flowerRule_effRes
#print axioms EIGS.flowerSystem_Psi
