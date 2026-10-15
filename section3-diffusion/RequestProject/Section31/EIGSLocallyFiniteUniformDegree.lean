import RequestProject.Section31.EIGSLocallyFiniteRuleGraphs
import RequestProject.Section31.EIGSPrimitiveDegreeNormalizedGrowth
import RequestProject.Section31.EIGSUniformBirthDegreeBound
import RequestProject.Section31.EIGSIncidenceResistanceDecayWithoutPrimitive
import RequestProject.Section2LocalBall

/-! Uniform degree bounds on the literal Laakso and canonical Xi systems.
Their actual degree matrix is the identity, so old degrees are preserved.
Private birth degrees are computed directly from the finite rule graphs.
The spectral equality nu=1 alone is not used to infer bounded degrees.
Candidate source, awaiting compilation. -/

namespace EIGS
open scoped BigOperators
noncomputable section

theorem locallyFiniteRuleSystem_rule_degree_le_three (canonical : Bool)
    (colour : Fin 1) (vertex : Fin 6) :
    ruleTailDeg (locallyFiniteRuleSystem canonical) colour vertex 0 +
      ruleHeadDeg (locallyFiniteRuleSystem canonical) colour vertex 0 ≤ 3 := by
  cases canonical <;> fin_cases colour <;> fin_cases vertex <;> decide

open scoped Classical

theorem locallyFiniteRuleSystem_old_degree_vector (canonical : Bool) (level : ℕ)
    (vertex : XiVtx (locallyFiniteRuleSystem canonical) level) :
    degVec (locallyFiniteRuleSystem canonical) (level + 1) (Sum.inl vertex) =
      degVec (locallyFiniteRuleSystem canonical) level vertex := by
  have forward := degVec_xiForward_eq_vecMul_pow (locallyFiniteRuleSystem canonical) level 1 vertex
  simpa only [locallyFiniteRuleSystem_degreeMatrix, one_pow, Matrix.vecMul_one,
    xiForward, id_eq] using forward

theorem locallyFiniteRuleSystem_degree_state_sum_le_three (canonical : Bool) :
    ∀ level (vertex : XiVtx (locallyFiniteRuleSystem canonical) level),
      (∑ state, degVec (locallyFiniteRuleSystem canonical) level vertex state) ≤ 3 := by
  intro level
  induction level with
  | zero =>
      intro vertex
      have initialEquality :
          (∑ state, degVec (locallyFiniteRuleSystem canonical) 0 vertex state) = 1 := by
        simpa only [mul_one, ite_self] using
          degree_initial_eigenweight (locallyFiniteRuleSystem canonical) (fun _ => 1) vertex
      rw [initialEquality]
      norm_num
  | succ level induction =>
      intro vertex
      rcases vertex with vertex | ⟨edge, privateVertex⟩
      · rw [locallyFiniteRuleSystem_old_degree_vector]
        exact induction vertex
      · rw [Fintype.sum_sum_type]
        simp only [degVec, Sum.elim_inl, Sum.elim_inr, outDeg_private, inDeg_private,
          Fin.sum_univ_one]
        exact_mod_cast locallyFiniteRuleSystem_rule_degree_le_three canonical
          (XiCol (locallyFiniteRuleSystem canonical).toRuleData level edge) privateVertex.val

theorem locallyFiniteRuleSystem_incidence_le_three (canonical : Bool) (level : ℕ)
    (vertex : XiVtx (locallyFiniteRuleSystem canonical) level) :
    (xiVertexIncidenceCount (locallyFiniteRuleSystem canonical) level vertex : ℝ) ≤ 3 := by
  rw [xiVertexIncidenceCount_eq_degree_state_sum]
  exact locallyFiniteRuleSystem_degree_state_sum_le_three canonical level vertex

theorem locallyFiniteRuleSystem_simpleGraph_degree_le_three (canonical : Bool) (level : ℕ)
    (vertex : XiVtx (locallyFiniteRuleSystem canonical) level) :
    (XiSimpleGraph (locallyFiniteRuleSystem canonical) level).degree vertex ≤ 3 := by
  have actual := locallyFiniteRuleSystem_degree_state_sum_le_three canonical level vertex
  rw [← xiSimpleGraph_degree_eq_degree_state_sum (locallyFiniteRuleSystem canonical)
    (locallyFiniteRuleSystem_connected canonical) (locallyFiniteRuleSystem_loopless canonical)
    (locallyFiniteRuleSystem_edgesUnique canonical) (locallyFiniteRuleSystem_plantingNonadjacent canonical)] at actual
  exact_mod_cast actual

end
end EIGS

#print axioms EIGS.locallyFiniteRuleSystem_rule_degree_le_three
#print axioms EIGS.locallyFiniteRuleSystem_old_degree_vector
#print axioms EIGS.locallyFiniteRuleSystem_degree_state_sum_le_three
#print axioms EIGS.locallyFiniteRuleSystem_incidence_le_three
#print axioms EIGS.locallyFiniteRuleSystem_simpleGraph_degree_le_three
