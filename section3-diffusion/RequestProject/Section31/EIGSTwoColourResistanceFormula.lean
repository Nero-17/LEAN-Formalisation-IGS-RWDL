import RequestProject.Section31.EIGSTwoColourRuleGraph
import RequestProject.Section31.NetworkOhmResistanceCertificate

/-! The rational map of the paper is derived from the literal two rule
graphs. Explicit unit currents and their potentials certify Thomson
optimality on the unchanged oriented coloured edges. No resistance formula
is a hypothesis. Candidate source, awaiting actual compilation. -/

namespace EIGS
open scoped BigOperators Classical
noncomputable section

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
    (twoColourSystem.ruleNetwork 0).IsUnitFlow 0 4 (twoColourRedCurrent resistances) := by
  have sumNeZero : resistances 0 + resistances 1 ≠ 0 := ne_of_gt (add_pos (positive 0) (positive 1))
  intro vertex
  fin_cases vertex <;>
    norm_num [Network.div, twoColourRedCurrent, twoColourSystem, EIGSData.ruleNetwork,
      twoColourRedRule, Fin.sum_univ_succ] <;>
    field_simp [sumNeZero] <;> ring

theorem twoColourBlueCurrent_isUnitFlow (resistances : Fin 2 → ℝ)
    (positive : ∀ colour, 0 < resistances colour) :
    (twoColourSystem.ruleNetwork 1).IsUnitFlow 0 4 (twoColourBlueCurrent resistances) := by
  have denominatorNeZero : 2 * resistances 0 + 3 * resistances 1 ≠ 0 := by positivity
  intro vertex
  fin_cases vertex <;>
    norm_num [Network.div, twoColourBlueCurrent, twoColourSystem, EIGSData.ruleNetwork,
      twoColourBlueRule, Fin.sum_univ_succ] <;>
    field_simp [denominatorNeZero] <;> ring

def twoColourRedUnitFlow (resistances : Fin 2 → ℝ) (positive : ∀ colour, 0 < resistances colour) :
    (twoColourSystem.ruleNetwork 0).Flow 0 4 :=
  ⟨twoColourRedCurrent resistances, twoColourRedCurrent_isUnitFlow resistances positive⟩

def twoColourBlueUnitFlow (resistances : Fin 2 → ℝ) (positive : ∀ colour, 0 < resistances colour) :
    (twoColourSystem.ruleNetwork 1).Flow 0 4 :=
  ⟨twoColourBlueCurrent resistances, twoColourBlueCurrent_isUnitFlow resistances positive⟩

theorem twoColourRedCurrent_ohm (resistances : Fin 2 → ℝ)
    (edge : (twoColourSystem.ruleNetwork 0).E) :
    resistances ((twoColourSystem.ruleNetwork 0).color edge) * twoColourRedCurrent resistances edge =
      twoColourRedPotential resistances ((twoColourSystem.ruleNetwork 0).tail edge) -
        twoColourRedPotential resistances ((twoColourSystem.ruleNetwork 0).head edge) := by
  fin_cases edge <;>
    norm_num [twoColourSystem, EIGSData.ruleNetwork, twoColourRedRule,
      twoColourRedCurrent, twoColourRedPotential] <;> ring

theorem twoColourBlueCurrent_ohm (resistances : Fin 2 → ℝ)
    (edge : (twoColourSystem.ruleNetwork 1).E) :
    resistances ((twoColourSystem.ruleNetwork 1).color edge) * twoColourBlueCurrent resistances edge =
      twoColourBluePotential resistances ((twoColourSystem.ruleNetwork 1).tail edge) -
        twoColourBluePotential resistances ((twoColourSystem.ruleNetwork 1).head edge) := by
  fin_cases edge <;>
    norm_num [twoColourSystem, EIGSData.ruleNetwork, twoColourBlueRule,
      twoColourBlueCurrent, twoColourBluePotential] <;> ring

theorem twoColourRedCurrent_energy (resistances : Fin 2 → ℝ)
    (positive : ∀ colour, 0 < resistances colour) :
    (twoColourSystem.ruleNetwork 0).energyNetwork (twoColourRedCurrent resistances) resistances =
      (resistances 0 ^ 2 + 4 * resistances 0 * resistances 1 + resistances 1 ^ 2) /
        (3 * (resistances 0 + resistances 1)) := by
  have sumNeZero : resistances 0 + resistances 1 ≠ 0 := ne_of_gt (add_pos (positive 0) (positive 1))
  norm_num [Network.energyNetwork, twoColourSystem, EIGSData.ruleNetwork,
    twoColourRedRule, twoColourRedCurrent, Fin.sum_univ_succ]
  field_simp [sumNeZero]
  ring

theorem twoColourBlueCurrent_energy (resistances : Fin 2 → ℝ)
    (positive : ∀ colour, 0 < resistances colour) :
    (twoColourSystem.ruleNetwork 1).energyNetwork (twoColourBlueCurrent resistances) resistances =
      (resistances 0 + 2 * resistances 1) * (resistances 0 + resistances 1) /
        (2 * resistances 0 + 3 * resistances 1) := by
  have denominatorNeZero : 2 * resistances 0 + 3 * resistances 1 ≠ 0 := by positivity
  norm_num [Network.energyNetwork, twoColourSystem, EIGSData.ruleNetwork,
    twoColourBlueRule, twoColourBlueCurrent, Fin.sum_univ_succ]
  field_simp [denominatorNeZero]
  ring

theorem twoColourSystem_Psi (resistances : Fin 2 → ℝ)
    (positive : ∀ colour, 0 < resistances colour) :
    (twoColourSystem.ruleFamily twoColourSystem_connected).Psi resistances = example22Psi resistances := by
  ext colour
  fin_cases colour
  · change (twoColourSystem.ruleNetwork 0).effRes 0 4 _ resistances = _
    rw [Network.effRes_eq_energy_of_unitFlow_ohm (twoColourSystem.ruleNetwork 0) 0 4
      (by decide) _ resistances positive (twoColourRedUnitFlow resistances positive)
      (twoColourRedPotential resistances) (twoColourRedCurrent_ohm resistances)]
    exact twoColourRedCurrent_energy resistances positive
  · change (twoColourSystem.ruleNetwork 1).effRes 0 4 _ resistances = _
    rw [Network.effRes_eq_energy_of_unitFlow_ohm (twoColourSystem.ruleNetwork 1) 0 4
      (by decide) _ resistances positive (twoColourBlueUnitFlow resistances positive)
      (twoColourBluePotential resistances) (twoColourBlueCurrent_ohm resistances)]
    exact twoColourBlueCurrent_energy resistances positive

end
end EIGS

#print axioms EIGS.twoColourRedCurrent_isUnitFlow
#print axioms EIGS.twoColourBlueCurrent_isUnitFlow
#print axioms EIGS.twoColourSystem_Psi
