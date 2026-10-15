import RequestProject.Section31.EIGSLocallyFiniteRuleGraphs
import RequestProject.Section31.DirichletThomson
import Mathlib.Algebra.BigOperators.Fin

/-! Exact unit currents and terminal potentials for the actual six-edge
Laakso and canonical Xi rules. The Thomson lower bound is proved against
every unit flow, rather than assuming the displayed resistance values. -/

namespace EIGS
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 2200000

def locallyFiniteRuleResistance (canonical : Bool) : ℝ :=
  if canonical then 11 / 4 else 3

def locallyFiniteUnitCurrent (canonical : Bool) : Fin 6 → ℝ :=
  if canonical then ![1, 3 / 4, 1, 1 / 4, 1 / 4, -(1 / 4)]
  else ![1, 1 / 2, 1 / 2, 1 / 2, 1 / 2, 1]

def locallyFiniteTerminalPotential (canonical : Bool) (vertex : Fin 6) : ℝ :=
  if canonical then
    match vertex.val with
    | 0 => 11 / 4
    | 1 => 7 / 4
    | 2 => 3 / 2
    | 3 => 5 / 4
    | 4 => 1
    | _ => 0
  else
    match vertex.val with
    | 0 => 3
    | 1 => 2
    | 2 => 3 / 2
    | 3 => 3 / 2
    | 4 => 1
    | _ => 0

theorem locallyFiniteUnitCurrent_isUnitFlow (canonical : Bool) :
    ((locallyFiniteRuleSystem canonical).ruleNetwork 0).IsUnitFlow (0 : Fin 6) (5 : Fin 6)
      (locallyFiniteUnitCurrent canonical) := by
  change ∀ vertex : Fin 6, (∑ edge : Fin 6, if (locallyFiniteRuleGraph canonical).tail edge = vertex
      then locallyFiniteUnitCurrent canonical edge else 0) -
    (∑ edge : Fin 6, if (locallyFiniteRuleGraph canonical).head edge = vertex
      then locallyFiniteUnitCurrent canonical edge else 0) =
    if vertex = (0 : Fin 6) then 1 else if vertex = (5 : Fin 6) then -1 else 0
  intro vertex
  simp only [Fin.ext_iff]
  cases canonical <;> fin_cases vertex <;>
    norm_num [locallyFiniteUnitCurrent, locallyFiniteRuleGraph, Fin.sum_univ_succ, Fin.val_natCast, Matrix.cons_val_succ] <;> simp only [Fin.ext_iff] <;> norm_num

def locallyFiniteTerminalFlow (canonical : Bool) :
    ((locallyFiniteRuleSystem canonical).ruleNetwork 0).Flow (0 : Fin 6) (5 : Fin 6) :=
  ⟨locallyFiniteUnitCurrent canonical, locallyFiniteUnitCurrent_isUnitFlow canonical⟩

theorem locallyFiniteUnitCurrent_energy (canonical : Bool) :
    ((locallyFiniteRuleSystem canonical).ruleNetwork 0).energyNetwork
      (locallyFiniteUnitCurrent canonical) (fun _ => 1) = locallyFiniteRuleResistance canonical := by
  change (∑ edge : Fin 6, (1 : ℝ) * (locallyFiniteUnitCurrent canonical edge) ^ 2) = _
  cases canonical <;>
    norm_num [locallyFiniteUnitCurrent, locallyFiniteRuleResistance, Fin.sum_univ_succ]

theorem locallyFiniteTerminalPotential_energy (canonical : Bool) :
    (((locallyFiniteRuleSystem canonical).ruleNetwork 0).potentialNetwork
      (fun _ => 1) (fun _ => zero_lt_one)).energy
      (locallyFiniteTerminalPotential canonical) = locallyFiniteRuleResistance canonical := by
  change (∑ edge : Fin 6, (1 : ℝ)⁻¹ *
    (locallyFiniteTerminalPotential canonical ((locallyFiniteRuleGraph canonical).tail edge) -
      locallyFiniteTerminalPotential canonical ((locallyFiniteRuleGraph canonical).head edge)) ^ 2) = _
  cases canonical <;>
    norm_num [locallyFiniteTerminalPotential, locallyFiniteRuleResistance, Fin.sum_univ_succ, Matrix.cons_val_succ]

theorem locallyFiniteFlow_energy_lower (canonical : Bool)
    (current : ((locallyFiniteRuleSystem canonical).ruleNetwork 0).Flow (0 : Fin 6) (5 : Fin 6)) :
    locallyFiniteRuleResistance canonical ≤
      ((locallyFiniteRuleSystem canonical).ruleNetwork 0).energyNetwork current.val (fun _ => 1) := by
  have bound := Network.potential_difference_sq_le_flow_energy_mul_potential_energy
    ((locallyFiniteRuleSystem canonical).ruleNetwork 0) (fun _ => 1) (fun _ => zero_lt_one)
    (0 : Fin 6) (5 : Fin 6) (by decide : (0 : Fin 6) ≠ 5) current (locallyFiniteTerminalPotential canonical)
  have terminals : locallyFiniteTerminalPotential canonical 0 - locallyFiniteTerminalPotential canonical 5 =
      locallyFiniteRuleResistance canonical := by
    cases canonical <;> norm_num [locallyFiniteTerminalPotential, locallyFiniteRuleResistance, Matrix.cons_val_succ]
  rw [locallyFiniteTerminalPotential_energy, terminals] at bound
  have resistancePositive : 0 < locallyFiniteRuleResistance canonical := by
    cases canonical <;> norm_num [locallyFiniteRuleResistance]
  nlinarith

theorem locallyFiniteRule_effRes_one (canonical : Bool)
    (flowExists : Nonempty (((locallyFiniteRuleSystem canonical).ruleNetwork 0).Flow (0 : Fin 6) (5 : Fin 6))) :
    ((locallyFiniteRuleSystem canonical).ruleNetwork 0).effRes (0 : Fin 6) (5 : Fin 6) flowExists (fun _ => 1) =
      locallyFiniteRuleResistance canonical := by
  apply le_antisymm
  · have bound := ((locallyFiniteRuleSystem canonical).ruleNetwork 0).effRes_le_energy
      (0 : Fin 6) (5 : Fin 6) flowExists (fun _ => zero_le_one) (locallyFiniteTerminalFlow canonical)
    change _ ≤ ((locallyFiniteRuleSystem canonical).ruleNetwork 0).energyNetwork
      (locallyFiniteUnitCurrent canonical) (fun _ => 1) at bound
    rw [locallyFiniteUnitCurrent_energy] at bound
    exact bound
  · exact ((locallyFiniteRuleSystem canonical).ruleNetwork 0).le_effRes _ _ flowExists
      (fun current => locallyFiniteFlow_energy_lower canonical current)

theorem locallyFiniteRule_effRes (canonical : Bool)
    (flowExists : Nonempty (((locallyFiniteRuleSystem canonical).ruleNetwork 0).Flow (0 : Fin 6) (5 : Fin 6)))
    (resistances : Fin 1 → ℝ) (resistancesNonnegative : 0 ≤ resistances) :
    ((locallyFiniteRuleSystem canonical).ruleNetwork 0).effRes (0 : Fin 6) (5 : Fin 6) flowExists resistances =
      locallyFiniteRuleResistance canonical * resistances 0 := by
  have resistancesEquality : resistances = resistances 0 • (fun _ : Fin 1 => (1 : ℝ)) := by
    funext colour
    have colourZero : colour = 0 := Subsingleton.elim _ _
    simp [colourZero]
  conv_lhs => rw [resistancesEquality]
  rw [Network.effRes_smul _ _ _ _ _ (resistancesNonnegative 0),
    locallyFiniteRule_effRes_one canonical flowExists]
  ring

theorem locallyFiniteRuleSystem_Psi (canonical : Bool)
    (resistances : Fin 1 → ℝ) (resistancesNonnegative : 0 ≤ resistances) :
    ((locallyFiniteRuleSystem canonical).ruleFamily (locallyFiniteRuleSystem_connected canonical)).Psi
      resistances = fun _ => locallyFiniteRuleResistance canonical * resistances 0 := by
  funext colour
  have colourZero : colour = 0 := Subsingleton.elim _ _
  subst colour
  exact locallyFiniteRule_effRes canonical _ resistances resistancesNonnegative

end
end EIGS

#print axioms EIGS.locallyFiniteUnitCurrent_isUnitFlow
#print axioms EIGS.locallyFiniteUnitCurrent_energy
#print axioms EIGS.locallyFiniteTerminalPotential_energy
#print axioms EIGS.locallyFiniteFlow_energy_lower
#print axioms EIGS.locallyFiniteRule_effRes_one
#print axioms EIGS.locallyFiniteRule_effRes
#print axioms EIGS.locallyFiniteRuleSystem_Psi
