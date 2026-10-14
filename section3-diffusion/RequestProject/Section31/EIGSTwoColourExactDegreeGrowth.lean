import RequestProject.Section31.EIGSTwoColourPositiveDegreeData
import RequestProject.Section2LocalBall

/-! Exact degrees for the unchanged arrows of Figure 3. Every actual old
vertex has its degree doubled at each substitution. These statements concern
the actual finite simple graphs, not an assumed degree distribution.
Candidate source; no whole-file verification is claimed. -/

namespace EIGS
open scoped BigOperators Classical
noncomputable section

theorem twoColourSystem_degreeMatrix_row_sum (state : Fin 2 ⊕ Fin 2) :
    ∑ nextState, degreeMatrix twoColourSystem state nextState = 2 := by
  rw [twoColourSystem_degreeMatrix]
  rcases state with colour | colour <;> fin_cases colour <;>
    norm_num [Fintype.sum_sum_type, Fin.sum_univ_two, twoColourDegreeMatrix]

theorem twoColourSystem_degree_state_sum_inl (level : ℕ)
    (vertex : XiVtx twoColourSystem level) :
    (∑ state, degVec twoColourSystem (level + 1) (Sum.inl vertex) state) =
      2 * ∑ state, degVec twoColourSystem level vertex state := by
  rw [degVec_inl]
  calc
    (∑ state, (Matrix.vecMul (degVec twoColourSystem level vertex)
        (degreeMatrix twoColourSystem)) state) =
        ∑ oldState, degVec twoColourSystem level vertex oldState *
          ∑ state, degreeMatrix twoColourSystem oldState state := by
      simp only [Matrix.vecMul, dotProduct]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = 2 * ∑ state, degVec twoColourSystem level vertex state := by
      simp only [twoColourSystem_degreeMatrix_row_sum, Finset.mul_sum, mul_comm]

theorem twoColourSystem_degree_state_sum_forward (birth age : ℕ)
    (vertex : XiVtx twoColourSystem birth) :
    (∑ state, degVec twoColourSystem (birth + age)
      (xiForward twoColourSystem birth age vertex) state) =
      (∑ state, degVec twoColourSystem birth vertex state) * 2 ^ age := by
  induction age with
  | zero => simp [xiForward]
  | succ age induction =>
      change (∑ state, degVec twoColourSystem ((birth + age) + 1)
        (Sum.inl (xiForward twoColourSystem birth age vertex)) state) = _
      rw [twoColourSystem_degree_state_sum_inl, induction, pow_succ]
      ring

theorem twoColourSystem_simpleGraph_degree_doubles (level : ℕ)
    (vertex : XiVtx twoColourSystem level) :
    (XiSimpleGraph twoColourSystem (level + 1)).degree (Sum.inl vertex) =
      2 * (XiSimpleGraph twoColourSystem level).degree vertex := by
  have degreeIdentity := xiSimpleGraph_degree_eq_degree_state_sum twoColourSystem
    twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique
    twoColourSystem_plantingNonadjacent
  have realIdentity :
      ((XiSimpleGraph twoColourSystem (level + 1)).degree (Sum.inl vertex) : ℝ) =
        2 * ((XiSimpleGraph twoColourSystem level).degree vertex : ℝ) := by
    rw [degreeIdentity, degreeIdentity, twoColourSystem_degree_state_sum_inl]
  exact_mod_cast realIdentity

theorem twoColourSystem_simpleGraph_degree_forward (birth age : ℕ)
    (vertex : XiVtx twoColourSystem birth) :
    (XiSimpleGraph twoColourSystem (birth + age)).degree
      (xiForward twoColourSystem birth age vertex) =
      (XiSimpleGraph twoColourSystem birth).degree vertex * 2 ^ age := by
  have degreeIdentity := xiSimpleGraph_degree_eq_degree_state_sum twoColourSystem
    twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique
    twoColourSystem_plantingNonadjacent
  have realIdentity :
      ((XiSimpleGraph twoColourSystem (birth + age)).degree
        (xiForward twoColourSystem birth age vertex) : ℝ) =
      ((XiSimpleGraph twoColourSystem birth).degree vertex : ℝ) * (2 : ℝ) ^ age := by
    rw [degreeIdentity, degreeIdentity, twoColourSystem_degree_state_sum_forward]
  exact_mod_cast realIdentity

end
end EIGS

#print axioms EIGS.twoColourSystem_degreeMatrix_row_sum
#print axioms EIGS.twoColourSystem_degree_state_sum_forward
#print axioms EIGS.twoColourSystem_simpleGraph_degree_doubles
#print axioms EIGS.twoColourSystem_simpleGraph_degree_forward
