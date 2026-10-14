import RequestProject.Section31.EIGSPrivateVertexDegree
import RequestProject.Section31.EIGSTwoColourExactDegreeGrowth

/-! Actual private birth degrees and maximum degrees for Figure 3. This is
the finite-graph input for the stationary normalized degree of Li--Britz,
arXiv:2109.14463v2, Definitions 3.1--3.2. Candidate source. -/

namespace EIGS
open scoped BigOperators Classical
noncomputable section

theorem twoColourSystem_rule_interior_degree_counts (colour : Fin 2) (vertex : Fin 5)
    (notPlus : vertex ≠ 0) (notMinus : vertex ≠ 4) :
    (∑ edgeColour, ruleTailDeg twoColourSystem colour vertex edgeColour) +
      (∑ edgeColour, ruleHeadDeg twoColourSystem colour vertex edgeColour) =
      if colour = 0 ∧ (vertex = 1 ∨ vertex = 3) then 3 else 2 := by
  fin_cases colour <;> fin_cases vertex <;>
    simp_all only [Fin.isValue, ne_eq, not_true_eq_false]
  all_goals decide

theorem twoColourSystem_private_birth_degree (level : ℕ)
    (edge : XiEdge twoColourSystem.toRuleData level)
    (privateVertex : {vertex : Fin 5 // vertex ≠ 0 ∧ vertex ≠ 4}) :
    (XiSimpleGraph twoColourSystem (level + 1)).degree (Sum.inr ⟨edge, privateVertex⟩) =
      if XiCol twoColourSystem.toRuleData level edge = 0 ∧
        (privateVertex.val = 1 ∨ privateVertex.val = 3) then 3 else 2 := by
  have counts := twoColourSystem_rule_interior_degree_counts
    (XiCol twoColourSystem.toRuleData level edge) privateVertex.val
    privateVertex.property.1 privateVertex.property.2
  have degreeIdentity := xiSimpleGraph_degree_eq_degree_state_sum twoColourSystem
    twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique
    twoColourSystem_plantingNonadjacent (level + 1) (Sum.inr ⟨edge, privateVertex⟩)
  rw [Fintype.sum_sum_type] at degreeIdentity
  simp only [degVec, Sum.elim_inl, Sum.elim_inr, outDeg_private, inDeg_private] at degreeIdentity
  have realCounts :
      (∑ edgeColour, (ruleTailDeg twoColourSystem
        (XiCol twoColourSystem.toRuleData level edge) privateVertex.val edgeColour : ℝ)) +
      (∑ edgeColour, (ruleHeadDeg twoColourSystem
        (XiCol twoColourSystem.toRuleData level edge) privateVertex.val edgeColour : ℝ)) =
      if XiCol twoColourSystem.toRuleData level edge = 0 ∧
        (privateVertex.val = 1 ∨ privateVertex.val = 3) then 3 else 2 := by
    exact_mod_cast counts
  have realDegree := degreeIdentity.trans realCounts
  exact_mod_cast realDegree

theorem twoColourSystem_private_birth_degree_le_three (level : ℕ)
    (edge : XiEdge twoColourSystem.toRuleData level)
    (privateVertex : {vertex : Fin 5 // vertex ≠ 0 ∧ vertex ≠ 4}) :
    (XiSimpleGraph twoColourSystem (level + 1)).degree (Sum.inr ⟨edge, privateVertex⟩) ≤ 3 := by
  rw [twoColourSystem_private_birth_degree]
  split_ifs <;> omega

theorem twoColourSystem_initial_degree (vertex : XiVtx twoColourSystem 0) :
    (XiSimpleGraph twoColourSystem 0).degree vertex = 1 := by
  have degreeIdentity := xiSimpleGraph_degree_eq_degree_state_sum twoColourSystem
    twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique
    twoColourSystem_plantingNonadjacent 0 vertex
  have stateSum : (∑ state, degVec twoColourSystem 0 vertex state) = 1 := by
    change Bool at vertex
    cases vertex <;>
      norm_num [Fintype.sum_sum_type, Fin.sum_univ_two, degVec, outDeg, inDeg,
        XiTail, XiHead, XiEnds, XiCol, XiLvl, XiEdge, twoColourSystem, EIGSData.toRuleData]
    all_goals
      change (Finset.univ.filter (fun _ : Unit => (0 : Fin 2) = 0)).card = 1
      simp
  have realDegree := degreeIdentity.trans stateSum
  exact_mod_cast realDegree

theorem twoColourSystem_degree_upper (level : ℕ) :
    ∀ vertex : XiVtx twoColourSystem (level + 1),
      (XiSimpleGraph twoColourSystem (level + 1)).degree vertex ≤ 3 * 2 ^ level := by
  induction level with
  | zero =>
      intro vertex
      rcases vertex with vertex | ⟨edge, privateVertex⟩
      · rw [twoColourSystem_simpleGraph_degree_doubles, twoColourSystem_initial_degree]
        norm_num
      · simpa using twoColourSystem_private_birth_degree_le_three 0 edge privateVertex
  | succ level induction =>
      intro vertex
      rcases vertex with vertex | ⟨edge, privateVertex⟩
      · rw [twoColourSystem_simpleGraph_degree_doubles]
        have bound := induction vertex
        calc
          2 * (XiSimpleGraph twoColourSystem (level + 1)).degree vertex ≤
              2 * (3 * 2 ^ level) := Nat.mul_le_mul_left 2 bound
          _ = 3 * 2 ^ (level + 1) := by rw [pow_succ]; ring
      · have bound := twoColourSystem_private_birth_degree_le_three (level + 1) edge privateVertex
        have powerPositive : 0 < (2 : ℕ) ^ (level + 1) := pow_pos (by omega) _
        omega

def twoColourFirstMaximumVertex : XiVtx twoColourSystem 1 :=
  Sum.inr ⟨(), ⟨(1 : Fin 5), by decide⟩⟩

theorem twoColourSystem_first_maximum_vertex_degree :
    (XiSimpleGraph twoColourSystem 1).degree twoColourFirstMaximumVertex = 3 := by
  unfold twoColourFirstMaximumVertex
  rw [twoColourSystem_private_birth_degree]
  norm_num [XiCol, XiLvl, twoColourSystem, EIGSData.toRuleData] <;> rfl

theorem twoColourSystem_maxDegree (level : ℕ) :
    (XiSimpleGraph twoColourSystem (level + 1)).maxDegree = 3 * 2 ^ level := by
  apply Nat.le_antisymm
  · exact SimpleGraph.maxDegree_le_of_forall_degree_le _ _ (twoColourSystem_degree_upper level)
  · have bound := (XiSimpleGraph twoColourSystem (1 + level)).degree_le_maxDegree
      (xiForward twoColourSystem 1 level twoColourFirstMaximumVertex)
    rw [twoColourSystem_simpleGraph_degree_forward,
      twoColourSystem_first_maximum_vertex_degree] at bound
    rw [Nat.add_comm level 1]
    exact bound

end
end EIGS

#print axioms EIGS.twoColourSystem_rule_interior_degree_counts
#print axioms EIGS.twoColourSystem_private_birth_degree
#print axioms EIGS.twoColourSystem_initial_degree
#print axioms EIGS.twoColourSystem_maxDegree
