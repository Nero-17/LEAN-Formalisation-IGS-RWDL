import RequestProject.Section1Connected
import RequestProject.Section2Concrete
import RequestProject.Section2Simplicity
import RequestProject.Section2DistancePositive
import RequestProject.Section2FiniteSpectralRadius
import Mathlib.Tactic

/-! Literal six-edge locally finite examples from Table 1.
`canonical = true` is the original canonical Xi rule, including its reverse
upper-right arc (source figure SHA256
8b84f7d8bf0802baab539d8059833e28ae864acaf90b42368f2edd81f211d60c).
`canonical = false` is the six-copy Laakso rule in Figure 1 of Margaris and
Robinson, doi:10.5802/crmath.70. Vertices are source 0, left branch 1,
upper/interior 2 and 3, right branch 4, and sink 5.
The two models are distinguished before any spectral parameter is proved. -/

namespace EIGS
noncomputable section
set_option maxHeartbeats 2200000

abbrev locallyFiniteRuleGraph (canonical : Bool) : ColGraph 1 where
  V := Fin 6
  E := Fin 6
  tail := if canonical then ![0, 1, 4, 1, 2, 4] else ![0, 1, 2, 1, 3, 4]
  head := if canonical then ![1, 4, 5, 2, 3, 3] else ![1, 2, 4, 3, 4, 5]
  col _ := 0

abbrev locallyFiniteRuleSystem (canonical : Bool) : EIGSData 1 where
  initCol := 0
  rule _ := locallyFiniteRuleGraph canonical
  plantPlus _ := (0 : Fin 6)
  plantMinus _ := (5 : Fin 6)
  plant_ne _ := (by decide : (0 : Fin 6) ≠ 5)

theorem locallyFiniteRuleSystem_connected (canonical : Bool) (colour : Fin 1) :
    (ruleSG (locallyFiniteRuleSystem canonical) colour).Connected := by
  fin_cases colour
  cases canonical
  · have first : (ruleSG (locallyFiniteRuleSystem false) 0).Adj 0 1 := by
      dsimp only [ruleSG, SimpleGraph.fromRel]; decide
    have upper : (ruleSG (locallyFiniteRuleSystem false) 0).Adj 1 2 := by
      dsimp only [ruleSG, SimpleGraph.fromRel]; decide
    have upperLast : (ruleSG (locallyFiniteRuleSystem false) 0).Adj 2 4 := by
      dsimp only [ruleSG, SimpleGraph.fromRel]; decide
    have lower : (ruleSG (locallyFiniteRuleSystem false) 0).Adj 1 3 := by
      dsimp only [ruleSG, SimpleGraph.fromRel]; decide
    have last : (ruleSG (locallyFiniteRuleSystem false) 0).Adj 4 5 := by
      dsimp only [ruleSG, SimpleGraph.fromRel]; decide
    have reaches (vertex : Fin 6) : (ruleSG (locallyFiniteRuleSystem false) 0).Reachable 0 vertex := by
      fin_cases vertex
      · exact SimpleGraph.Reachable.refl _
      · exact first.reachable
      · exact first.reachable.trans upper.reachable
      · exact first.reachable.trans lower.reachable
      · exact (first.reachable.trans upper.reachable).trans upperLast.reachable
      · exact ((first.reachable.trans upper.reachable).trans upperLast.reachable).trans last.reachable
    exact ⟨fun first second => (reaches first).symm.trans (reaches second)⟩
  · have first : (ruleSG (locallyFiniteRuleSystem true) 0).Adj 0 1 := by
      dsimp only [ruleSG, SimpleGraph.fromRel]; decide
    have upper : (ruleSG (locallyFiniteRuleSystem true) 0).Adj 1 2 := by
      dsimp only [ruleSG, SimpleGraph.fromRel]; decide
    have top : (ruleSG (locallyFiniteRuleSystem true) 0).Adj 2 3 := by
      dsimp only [ruleSG, SimpleGraph.fromRel]; decide
    have right : (ruleSG (locallyFiniteRuleSystem true) 0).Adj 3 4 := by
      dsimp only [ruleSG, SimpleGraph.fromRel]; decide
    have last : (ruleSG (locallyFiniteRuleSystem true) 0).Adj 4 5 := by
      dsimp only [ruleSG, SimpleGraph.fromRel]; decide
    have reaches (vertex : Fin 6) : (ruleSG (locallyFiniteRuleSystem true) 0).Reachable 0 vertex := by
      fin_cases vertex
      · exact SimpleGraph.Reachable.refl _
      · exact first.reachable
      · exact first.reachable.trans upper.reachable
      · exact (first.reachable.trans upper.reachable).trans top.reachable
      · exact ((first.reachable.trans upper.reachable).trans top.reachable).trans right.reachable
      · exact (((first.reachable.trans upper.reachable).trans top.reachable).trans right.reachable).trans last.reachable
    exact ⟨fun first second => (reaches first).symm.trans (reaches second)⟩

theorem locallyFiniteRuleSystem_loopless (canonical : Bool) (colour : Fin 1) :
    ((locallyFiniteRuleSystem canonical).ruleNetwork colour).Loopless := by
  cases canonical <;> fin_cases colour <;> unfold Network.Loopless <;> decide

theorem locallyFiniteRuleSystem_edgesUnique (canonical : Bool) (colour : Fin 1) :
    ((locallyFiniteRuleSystem canonical).ruleNetwork colour).EdgesUnique := by
  cases canonical <;> fin_cases colour <;>
    dsimp [Network.EdgesUnique, EIGSData.ruleNetwork] <;> decide

theorem locallyFiniteRuleSystem_plantingNonadjacent (canonical : Bool) (colour : Fin 1) :
    ¬ (ruleSG (locallyFiniteRuleSystem canonical) colour).Adj
      ((locallyFiniteRuleSystem canonical).plantPlus colour)
      ((locallyFiniteRuleSystem canonical).plantMinus colour) := by
  cases canonical <;> fin_cases colour <;> dsimp only [ruleSG, SimpleGraph.fromRel] <;> decide

theorem locallyFiniteRuleSystem_distancePositive (canonical : Bool) (ruleColour edgeColour : Fin 1) :
    ¬ (((locallyFiniteRuleSystem canonical).ruleNetwork ruleColour).withoutColour edgeColour).Reachable
      ((locallyFiniteRuleSystem canonical).plantPlus ruleColour)
      ((locallyFiniteRuleSystem canonical).plantMinus ruleColour) := by
  have edgeZero : edgeColour = 0 := Subsingleton.elim _ _
  subst edgeColour
  have graphEmpty : (((locallyFiniteRuleSystem canonical).ruleNetwork ruleColour).withoutColour 0) = ⊥ := by
    ext first second
    simp [Network.withoutColour, EIGSData.ruleNetwork]
  rw [graphEmpty, SimpleGraph.reachable_bot]
  exact (locallyFiniteRuleSystem canonical).plant_ne ruleColour

theorem locallyFiniteRuleSystem_massMatrix (canonical : Bool) :
    massMatrix (locallyFiniteRuleSystem canonical).toRuleData = fun _ _ => 6 := by
  ext row column
  fin_cases row
  fin_cases column
  cases canonical <;> decide

theorem locallyFiniteRuleSystem_terminal_degree_counts (canonical : Bool) :
    ruleTailDeg (locallyFiniteRuleSystem canonical) 0 0 0 = 1 ∧
    ruleHeadDeg (locallyFiniteRuleSystem canonical) 0 0 0 = 0 ∧
    ruleTailDeg (locallyFiniteRuleSystem canonical) 0 5 0 = 0 ∧
    ruleHeadDeg (locallyFiniteRuleSystem canonical) 0 5 0 = 1 := by
  cases canonical <;> decide

theorem locallyFiniteRuleSystem_degreeMatrix (canonical : Bool) :
    degreeMatrix (locallyFiniteRuleSystem canonical) = 1 := by
  have counts := locallyFiniteRuleSystem_terminal_degree_counts canonical
  ext row column
  rcases row with row | row <;> rcases column with column | column <;>
    fin_cases row <;> fin_cases column <;>
    simp [degreeMatrix, Matrix.one_apply, counts.1, counts.2.1, counts.2.2.1, counts.2.2.2]

theorem locallyFiniteRuleSystem_degreeSpectralRadius (canonical : Bool) :
    finiteRealMatrixSpectralRadius (degreeMatrix (locallyFiniteRuleSystem canonical)) = 1 := by
  apply finiteRealMatrixSpectralRadius_eq_positive_eigenvalue
    (degreeMatrix (locallyFiniteRuleSystem canonical)) (degreeMatrix_nonneg _) (fun _ => 1) 1
  · intro state
    norm_num
  · norm_num
  · rw [locallyFiniteRuleSystem_degreeMatrix]
    simp

end
end EIGS

#print axioms EIGS.locallyFiniteRuleSystem_connected
#print axioms EIGS.locallyFiniteRuleSystem_loopless
#print axioms EIGS.locallyFiniteRuleSystem_edgesUnique
#print axioms EIGS.locallyFiniteRuleSystem_plantingNonadjacent
#print axioms EIGS.locallyFiniteRuleSystem_distancePositive
#print axioms EIGS.locallyFiniteRuleSystem_massMatrix
#print axioms EIGS.locallyFiniteRuleSystem_terminal_degree_counts
#print axioms EIGS.locallyFiniteRuleSystem_degreeMatrix
#print axioms EIGS.locallyFiniteRuleSystem_degreeSpectralRadius
