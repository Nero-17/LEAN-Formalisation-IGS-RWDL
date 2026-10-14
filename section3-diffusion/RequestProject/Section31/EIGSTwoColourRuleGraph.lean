import RequestProject.Section1Connected
import RequestProject.Section2Concrete
import RequestProject.Section2Simplicity
import Mathlib.Tactic

/-! Literal oriented rule graphs of arXiv:2603.13798v3 Figure 3.
Vertices are source 0, upper 1, middle/upper-right 2, lower 3, sink 4.
Colour 0 is red and colour 1 is blue. The arrows, including the two
oppositely oriented central edges of the red rule, are retained exactly.
Source image SHA256 DB4111CF9C67B897CA175AC6D815A778230517FC66A8067AB427558E1B3A3A2F.
Candidate source; compilation is not claimed. -/

namespace EIGS
noncomputable section

def twoColourRedRule : ColGraph 2 where
  V := Fin 5
  E := Fin 6
  tail := ![0, 1, 0, 3, 1, 3]
  head := ![1, 4, 3, 4, 2, 2]
  col := ![0, 1, 1, 0, 0, 1]

def twoColourBlueRule : ColGraph 2 where
  V := Fin 5
  E := Fin 5
  tail := ![0, 1, 2, 0, 3]
  head := ![1, 2, 4, 3, 4]
  col := ![1, 0, 1, 1, 0]

abbrev twoColourRule (colour : Fin 2) : ColGraph 2 where
  V := Fin 5
  E := Fin (if colour = 0 then 6 else 5)
  tail edge := if isRed : colour = 0 then
    twoColourRedRule.tail ⟨edge.val, by simpa [isRed] using edge.isLt⟩
    else twoColourBlueRule.tail ⟨edge.val, by simpa [isRed] using edge.isLt⟩
  head edge := if isRed : colour = 0 then
    twoColourRedRule.head ⟨edge.val, by simpa [isRed] using edge.isLt⟩
    else twoColourBlueRule.head ⟨edge.val, by simpa [isRed] using edge.isLt⟩
  col edge := if isRed : colour = 0 then
    twoColourRedRule.col ⟨edge.val, by simpa [isRed] using edge.isLt⟩
    else twoColourBlueRule.col ⟨edge.val, by simpa [isRed] using edge.isLt⟩

abbrev twoColourSystem : EIGSData 2 where
  initCol := 0
  rule := twoColourRule
  plantPlus _ := (0 : Fin 5)
  plantMinus _ := (4 : Fin 5)
  plant_ne _ := (by decide : (0 : Fin 5) ≠ 4)

theorem twoColourSystem_connected (colour : Fin 2) :
    (ruleSG twoColourSystem colour).Connected := by
  fin_cases colour
  · have first : (ruleSG twoColourSystem 0).Adj 0 1 := by dsimp only [ruleSG, SimpleGraph.fromRel]; decide
    have middle : (ruleSG twoColourSystem 0).Adj 1 2 := by dsimp only [ruleSG, SimpleGraph.fromRel]; decide
    have lower : (ruleSG twoColourSystem 0).Adj 0 3 := by dsimp only [ruleSG, SimpleGraph.fromRel]; decide
    have last : (ruleSG twoColourSystem 0).Adj 1 4 := by dsimp only [ruleSG, SimpleGraph.fromRel]; decide
    have reaches (vertex : Fin 5) : (ruleSG twoColourSystem 0).Reachable 0 vertex := by
      fin_cases vertex
      · exact SimpleGraph.Reachable.refl _
      · exact first.reachable
      · exact first.reachable.trans middle.reachable
      · exact lower.reachable
      · exact first.reachable.trans last.reachable
    exact ⟨fun first second => (reaches first).symm.trans (reaches second)⟩
  · have first : (ruleSG twoColourSystem 1).Adj 0 1 := by dsimp only [ruleSG, SimpleGraph.fromRel]; decide
    have middle : (ruleSG twoColourSystem 1).Adj 1 2 := by dsimp only [ruleSG, SimpleGraph.fromRel]; decide
    have lower : (ruleSG twoColourSystem 1).Adj 0 3 := by dsimp only [ruleSG, SimpleGraph.fromRel]; decide
    have last : (ruleSG twoColourSystem 1).Adj 3 4 := by dsimp only [ruleSG, SimpleGraph.fromRel]; decide
    have reaches (vertex : Fin 5) : (ruleSG twoColourSystem 1).Reachable 0 vertex := by
      fin_cases vertex
      · exact SimpleGraph.Reachable.refl _
      · exact first.reachable
      · exact first.reachable.trans middle.reachable
      · exact lower.reachable
      · exact lower.reachable.trans last.reachable
    exact ⟨fun first second => (reaches first).symm.trans (reaches second)⟩

theorem twoColourSystem_loopless (colour : Fin 2) :
    (twoColourSystem.ruleNetwork colour).Loopless := by
  fin_cases colour <;> unfold Network.Loopless <;> decide

theorem twoColourSystem_edgesUnique (colour : Fin 2) :
    (twoColourSystem.ruleNetwork colour).EdgesUnique := by
  fin_cases colour <;>
    dsimp [Network.EdgesUnique, EIGSData.ruleNetwork, twoColourSystem, twoColourRule,
      twoColourRedRule, twoColourBlueRule] <;> decide

theorem twoColourSystem_plantingNonadjacent (colour : Fin 2) :
    ¬ (ruleSG twoColourSystem colour).Adj
      (twoColourSystem.plantPlus colour) (twoColourSystem.plantMinus colour) := by
  fin_cases colour <;> dsimp only [ruleSG, SimpleGraph.fromRel] <;> decide

theorem twoColourSystem_massMatrix :
    massMatrix twoColourSystem.toRuleData = !![3, 3; 2, 3] := by
  ext row column
  fin_cases row <;> fin_cases column <;> decide

theorem twoColourSystem_massMatrixR :
    massMatrixR twoColourSystem.toRuleData = !![(3 : ℝ), 3; 2, 3] := by
  ext row column
  simp only [massMatrixR, twoColourSystem_massMatrix]
  fin_cases row <;> fin_cases column <;> norm_num

end
end EIGS

#print axioms EIGS.twoColourSystem_connected
#print axioms EIGS.twoColourSystem_loopless
#print axioms EIGS.twoColourSystem_edgesUnique
#print axioms EIGS.twoColourSystem_plantingNonadjacent
#print axioms EIGS.twoColourSystem_massMatrix
