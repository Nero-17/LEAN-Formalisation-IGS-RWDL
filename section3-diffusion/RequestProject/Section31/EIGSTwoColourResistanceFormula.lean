import RequestProject.Section31.EIGSTwoColourRuleGraph
import RequestProject.Section31.NetworkOhmResistanceCertificate

/-! The rational map of the paper is derived from the literal two rule
graphs. Explicit unit currents and their potentials certify Thomson
optimality on the unchanged oriented coloured edges. No resistance formula
is a hypothesis. Candidate source, awaiting actual compilation. -/

namespace EIGS
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000

def twoColourRedCurrent (resistances : Fin 2 → ℝ) : Fin 6 → ℝ :=
  ![(resistances 0 + 2 * resistances 1) / (3 * (resistances 0 + resistances 1)),
    (2 * resistances 0 + resistances 1) / (3 * (resistances 0 + resistances 1)),
    (2 * resistances 0 + resistances 1) / (3 * (resistances 0 + resistances 1)),
    (resistances 0 + 2 * resistances 1) / (3 * (resistances 0 + resistances 1)),
    (resistances 1 - resistances 0) / (3 * (resistances 0 + resistances 1)),
    (resistances 0 - resistances 1) / (3 * (resistances 0 + resistances 1))]

def twoColourRedPotential (resistances : Fin 2 → ℝ) : Fin 5 → ℝ :=
  ![(resistances 0 ^ 2 + 4 * resistances 0 * resistances 1 + resistances 1 ^ 2) /
      (3 * (resistances 0 + resistances 1)),
    resistances 1 * (2 * resistances 0 + resistances 1) / (3 * (resistances 0 + resistances 1)),
    (resistances 0 ^ 2 + resistances 0 * resistances 1 + resistances 1 ^ 2) /
      (3 * (resistances 0 + resistances 1)),
    resistances 0 * (resistances 0 + 2 * resistances 1) / (3 * (resistances 0 + resistances 1)),
    0]

def twoColourBlueCurrent (resistances : Fin 2 → ℝ) : Fin 5 → ℝ :=
  ![(resistances 0 + resistances 1) / (2 * resistances 0 + 3 * resistances 1),
    (resistances 0 + resistances 1) / (2 * resistances 0 + 3 * resistances 1),
    (resistances 0 + resistances 1) / (2 * resistances 0 + 3 * resistances 1),
    (resistances 0 + 2 * resistances 1) / (2 * resistances 0 + 3 * resistances 1),
    (resistances 0 + 2 * resistances 1) / (2 * resistances 0 + 3 * resistances 1)]

def twoColourBluePotential (resistances : Fin 2 → ℝ) : Fin 5 → ℝ :=
  ![(resistances 0 + 2 * resistances 1) * (resistances 0 + resistances 1) /
      (2 * resistances 0 + 3 * resistances 1),
    (resistances 0 + resistances 1) ^ 2 / (2 * resistances 0 + 3 * resistances 1),
    resistances 1 * (resistances 0 + resistances 1) / (2 * resistances 0 + 3 * resistances 1),
    resistances 0 * (resistances 0 + 2 * resistances 1) / (2 * resistances 0 + 3 * resistances 1),
    0]

theorem twoColourRedCurrent_isUnitFlow (resistances : Fin 2 → ℝ)
    (positive : ∀ colour, 0 < resistances colour) :
    (twoColourSystem.ruleNetwork 0).IsUnitFlow (0 : Fin 5) (4 : Fin 5) (twoColourRedCurrent resistances) := by
  have sumNeZero : resistances 0 + resistances 1 ≠ 0 := ne_of_gt (add_pos (positive 0) (positive 1))
  change ∀ vertex : Fin 5,
    (∑ edge : Fin 6, if twoColourRedRule.tail edge = vertex then twoColourRedCurrent resistances edge else 0) -
      (∑ edge : Fin 6, if twoColourRedRule.head edge = vertex then twoColourRedCurrent resistances edge else 0) =
        if vertex = 0 then 1 else if vertex = 4 then -1 else 0
  intro vertex
  fin_cases vertex <;>
    dsimp only [twoColourRedRule] <;>
    simp only [twoColourRedCurrent, Fin.sum_univ_six,
      Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val] <;>
    norm_num [Fin.ext_iff, Fin.reduceFinMk, Matrix.cons_val] <;>
    field_simp [sumNeZero] <;> ring

theorem twoColourBlueCurrent_isUnitFlow (resistances : Fin 2 → ℝ)
    (positive : ∀ colour, 0 < resistances colour) :
    (twoColourSystem.ruleNetwork 1).IsUnitFlow (0 : Fin 5) (4 : Fin 5) (twoColourBlueCurrent resistances) := by
  have redPositive := positive 0
  have bluePositive := positive 1
  have denominatorNeZero : 2 * resistances 0 + 3 * resistances 1 ≠ 0 := by positivity
  change ∀ vertex : Fin 5,
    (∑ edge : Fin 5, if twoColourBlueRule.tail edge = vertex then twoColourBlueCurrent resistances edge else 0) -
      (∑ edge : Fin 5, if twoColourBlueRule.head edge = vertex then twoColourBlueCurrent resistances edge else 0) =
        if vertex = 0 then 1 else if vertex = 4 then -1 else 0
  intro vertex
  fin_cases vertex <;>
    dsimp only [twoColourBlueRule] <;>
    simp only [twoColourBlueCurrent, Fin.sum_univ_five,
      Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val] <;>
    norm_num [Fin.ext_iff, Fin.reduceFinMk, Matrix.cons_val] <;>
    field_simp [denominatorNeZero] <;> ring

def twoColourRedUnitFlow (resistances : Fin 2 → ℝ) (positive : ∀ colour, 0 < resistances colour) :
    (twoColourSystem.ruleNetwork 0).Flow (0 : Fin 5) (4 : Fin 5) :=
  ⟨twoColourRedCurrent resistances, twoColourRedCurrent_isUnitFlow resistances positive⟩

def twoColourBlueUnitFlow (resistances : Fin 2 → ℝ) (positive : ∀ colour, 0 < resistances colour) :
    (twoColourSystem.ruleNetwork 1).Flow (0 : Fin 5) (4 : Fin 5) :=
  ⟨twoColourBlueCurrent resistances, twoColourBlueCurrent_isUnitFlow resistances positive⟩

theorem twoColourRedCurrent_ohm (resistances : Fin 2 → ℝ)
    (edge : Fin 6) :
    resistances (twoColourRedRule.col edge) * twoColourRedCurrent resistances edge =
      twoColourRedPotential resistances (twoColourRedRule.tail edge) -
        twoColourRedPotential resistances (twoColourRedRule.head edge) := by
  fin_cases edge <;>
    dsimp only [twoColourRedRule] <;>
    simp only [twoColourRedCurrent, twoColourRedPotential,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val] <;> ring

theorem twoColourBlueCurrent_ohm (resistances : Fin 2 → ℝ)
    (edge : Fin 5) :
    resistances (twoColourBlueRule.col edge) * twoColourBlueCurrent resistances edge =
      twoColourBluePotential resistances (twoColourBlueRule.tail edge) -
        twoColourBluePotential resistances (twoColourBlueRule.head edge) := by
  fin_cases edge <;>
    dsimp only [twoColourBlueRule] <;>
    simp only [twoColourBlueCurrent, twoColourBluePotential,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val] <;> ring

theorem twoColourRedCurrent_energy (resistances : Fin 2 → ℝ)
    (positive : ∀ colour, 0 < resistances colour) :
    (twoColourSystem.ruleNetwork 0).energyNetwork (twoColourRedCurrent resistances) resistances =
      (resistances 0 ^ 2 + 4 * resistances 0 * resistances 1 + resistances 1 ^ 2) /
        (3 * (resistances 0 + resistances 1)) := by
  have sumNeZero : resistances 0 + resistances 1 ≠ 0 := ne_of_gt (add_pos (positive 0) (positive 1))
  change (∑ edge : Fin 6, resistances (twoColourRedRule.col edge) * (twoColourRedCurrent resistances edge) ^ 2) = _
  dsimp only [twoColourRedRule]
  norm_num [twoColourRedRule, twoColourRedCurrent, Fin.sum_univ_succ]
  field_simp [sumNeZero]
  ring

theorem twoColourBlueCurrent_energy (resistances : Fin 2 → ℝ)
    (positive : ∀ colour, 0 < resistances colour) :
    (twoColourSystem.ruleNetwork 1).energyNetwork (twoColourBlueCurrent resistances) resistances =
      (resistances 0 + 2 * resistances 1) * (resistances 0 + resistances 1) /
        (2 * resistances 0 + 3 * resistances 1) := by
  have redPositive := positive 0
  have bluePositive := positive 1
  have denominatorNeZero : 2 * resistances 0 + 3 * resistances 1 ≠ 0 := by positivity
  change (∑ edge : Fin 5, resistances (twoColourBlueRule.col edge) * (twoColourBlueCurrent resistances edge) ^ 2) = _
  dsimp only [twoColourBlueRule]
  norm_num [twoColourBlueRule, twoColourBlueCurrent, Fin.sum_univ_succ]
  field_simp [denominatorNeZero]
  ring

theorem twoColourSystem_Psi (resistances : Fin 2 → ℝ)
    (positive : ∀ colour, 0 < resistances colour) :
    (twoColourSystem.ruleFamily twoColourSystem_connected).Psi resistances = example22Psi resistances := by
  ext colour
  fin_cases colour
  · change (twoColourSystem.ruleNetwork 0).effRes (0 : Fin 5) (4 : Fin 5) _ resistances = _
    rw [Network.effRes_eq_energy_of_unitFlow_ohm (twoColourSystem.ruleNetwork 0) (0 : Fin 5) (4 : Fin 5)
      (by decide : (0 : Fin 5) ≠ 4) _ resistances positive (twoColourRedUnitFlow resistances positive)
      (twoColourRedPotential resistances) (twoColourRedCurrent_ohm resistances)]
    exact twoColourRedCurrent_energy resistances positive
  · change (twoColourSystem.ruleNetwork 1).effRes (0 : Fin 5) (4 : Fin 5) _ resistances = _
    rw [Network.effRes_eq_energy_of_unitFlow_ohm (twoColourSystem.ruleNetwork 1) (0 : Fin 5) (4 : Fin 5)
      (by decide : (0 : Fin 5) ≠ 4) _ resistances positive (twoColourBlueUnitFlow resistances positive)
      (twoColourBluePotential resistances) (twoColourBlueCurrent_ohm resistances)]
    exact twoColourBlueCurrent_energy resistances positive

end
end EIGS

#print axioms EIGS.twoColourRedCurrent_isUnitFlow
#print axioms EIGS.twoColourBlueCurrent_isUnitFlow
#print axioms EIGS.twoColourSystem_Psi
