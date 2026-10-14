import RequestProject.Section31.PrimitiveMatrixNormalizedRowSumLimit
import RequestProject.Section2DegreeGrowth

/-! Actual normalized degree convergence at every finite-born vertex,
from standing primitive rules. The vector and common coefficient are selected
once for the actual degree matrix, and all birth vertices use that same data.
This is an input to global maximum-degree normalization, not yet the global
stationary degree distribution theorem. Candidate source. -/

namespace EIGS
open Filter Topology
open scoped BigOperators
noncomputable section
variable {K : ℕ}

theorem degVec_xiForward_eq_vecMul_pow (system : EIGSData K)
    (birth age : ℕ) (vertex : XiVtx system birth) :
    degVec system (birth + age) (xiForward system birth age vertex) =
      Matrix.vecMul (degVec system birth vertex) ((degreeMatrix system) ^ age) := by
  induction age with
  | zero => simp [xiForward]
  | succ age induction =>
      rw [degVec_xiForward_succ, induction]
      simp only [pow_succ, Matrix.vecMul_vecMul]

theorem degree_state_sum_forward_normalized_identity (system : EIGSData K)
    (birth age : ℕ) (vertex : XiVtx system birth) (rate : ℝ) :
    (∑ state, degVec system (birth + age) (xiForward system birth age vertex) state) / rate ^ age =
      ∑ initialState, degVec system birth vertex initialState *
        ((∑ state, ((degreeMatrix system) ^ age) initialState state) / rate ^ age) := by
  rw [degVec_xiForward_eq_vecMul_pow]
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, Finset.sum_div, mul_div_assoc]

theorem degree_normalized_growth_from_primitive_rules (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (primitive : (degreeMatrix system).IsPrimitive) :
    ∃ vector : Fin K ⊕ Fin K → ℝ, ∃ coefficient : ℝ,
      (∀ state, 0 < vector state) ∧ (∑ state, vector state) = 1 ∧
      (degreeMatrix system).mulVec vector =
        finiteRealMatrixSpectralRadius (degreeMatrix system) • vector ∧
      0 < coefficient ∧ ∀ birth (vertex : XiVtx system birth),
        0 < coefficient * (∑ state, degVec system birth vertex state * vector state) ∧
        Tendsto (fun age : ℕ =>
          (∑ state, degVec system (birth + age) (xiForward system birth age vertex) state) /
            (finiteRealMatrixSpectralRadius (degreeMatrix system)) ^ age)
          atTop (𝓝 (coefficient * (∑ state, degVec system birth vertex state * vector state))) := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  letI : Nonempty (Fin K ⊕ Fin K) := ⟨Sum.inl system.initCol⟩
  obtain ⟨vector, coefficient, vectorPositive, normalized, eigenpair, coefficientPositive, convergence⟩ :=
    primitive_matrix_normalized_row_sum_limit (degreeMatrix system) primitive
  refine ⟨vector, coefficient, vectorPositive, normalized, eigenpair, coefficientPositive, ?_⟩
  intro birth vertex
  refine ⟨mul_pos coefficientPositive
    (degVec_weighted_positive system connected birth vertex vector vectorPositive), ?_⟩
  have actual := tendsto_finset_sum Finset.univ
    (fun state _ => (convergence state).const_mul (degVec system birth vertex state))
  have valueIdentity :
      (∑ state, degVec system birth vertex state * (coefficient * vector state)) =
        coefficient * (∑ state, degVec system birth vertex state * vector state) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro state _
    ring
  simpa only [← degree_state_sum_forward_normalized_identity, valueIdentity] using actual

end
end EIGS

#print axioms EIGS.degVec_xiForward_eq_vecMul_pow
#print axioms EIGS.degree_state_sum_forward_normalized_identity
#print axioms EIGS.degree_normalized_growth_from_primitive_rules
