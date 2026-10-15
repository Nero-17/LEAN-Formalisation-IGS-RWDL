import RequestProject.Section31.EIGSUniformBirthDegreeBound
import RequestProject.Section31.EIGSPrivateBirthTypes
import RequestProject.Section2GroundedResistanceBounds
import RequestProject.Section2FiniteSpectralRadius

/-! Uniform degree growth from actual birth data. The constants below
are common to all private birth types and all birth generations, and also
cover the two initial vertices. Actual positive Perron weights are
constructed internally from the primitive degree matrix. -/

namespace EIGS
noncomputable section
open scoped Classical BigOperators
variable {K : ℕ}

theorem xi_degree_eigenweight_comparison (system : EIGSData K) [Nonempty (Fin K)]
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (weights : Fin K ⊕ Fin K → ℝ) (weightsPositive : ∀ state, 0 < weights state)
    (normalized : (∑ state, weights state) = 1) (level : ℕ) (vertex : XiVtx system level) :
    finiteVectorMinimum weights * ((XiSimpleGraph system level).degree vertex : ℝ) ≤
        ∑ state, degVec system level vertex state * weights state ∧
      (∑ state, degVec system level vertex state * weights state) ≤
        ((XiSimpleGraph system level).degree vertex : ℝ) := by
  letI : Nonempty (Fin K ⊕ Fin K) := ⟨Sum.inl system.initCol⟩
  have weightAtMostOne (state : Fin K ⊕ Fin K) : weights state ≤ 1 := by
    rw [← normalized]
    exact Finset.single_le_sum (fun other _ => (weightsPositive other).le) (Finset.mem_univ state)
  have degreeNonnegative (state : Fin K ⊕ Fin K) : 0 ≤ degVec system level vertex state := by
    cases state <;> exact Nat.cast_nonneg _
  rw [xiSimpleGraph_degree_eq_degree_state_sum system connected loopless unique plantingNonadjacent]
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro state _
    have weightLower : finiteVectorMinimum weights ≤ weights state :=
      Finset.inf'_le _ (Finset.mem_univ state)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right weightLower (degreeNonnegative state)
  · apply Finset.sum_le_sum
    intro state _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (weightAtMostOne state) (degreeNonnegative state)

theorem xi_degree_eigenweight_lower_at_every_vertex (system : EIGSData K) [Nonempty (Fin K)]
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (weights : Fin K ⊕ Fin K → ℝ) (weightsPositive : ∀ state, 0 < weights state)
    (normalized : (∑ state, weights state) = 1) (level : ℕ) (vertex : XiVtx system level) :
    finiteVectorMinimum weights ≤ ∑ state, degVec system level vertex state * weights state := by
  letI : Nonempty (Fin K ⊕ Fin K) := ⟨Sum.inl system.initCol⟩
  have minimumPositive : 0 < finiteVectorMinimum weights :=
    (Finset.lt_inf'_iff _).2 (fun state _ => weightsPositive state)
  have degreePositive := xiSimpleGraph_degree_positive system connected level vertex
  have degreeAtLeastOne : (1 : ℝ) ≤ (XiSimpleGraph system level).degree vertex := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp degreePositive.ne')
  have lower := (xi_degree_eigenweight_comparison system connected loopless unique plantingNonadjacent
    weights weightsPositive normalized level vertex).1
  have minimumLeDegree : finiteVectorMinimum weights ≤
      finiteVectorMinimum weights * ((XiSimpleGraph system level).degree vertex : ℝ) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left degreeAtLeastOne minimumPositive.le
  exact minimumLeDegree.trans lower

theorem xiSimpleGraph_uniform_birth_degree_spectral_growth (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (primitiveDegree : (degreeMatrix system).IsPrimitive) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      (∀ level (vertex : XiNewVertices system level) age,
        lower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age ≤
          ((XiSimpleGraph system ((level + 1) + age)).degree
            (xiForward system (level + 1) age (Sum.inr vertex)) : ℝ) ∧
        ((XiSimpleGraph system ((level + 1) + age)).degree
            (xiForward system (level + 1) age (Sum.inr vertex)) : ℝ) ≤
          upper * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age) ∧
      (∀ (vertex : Bool) age,
        lower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age ≤
          ((XiSimpleGraph system (0 + age)).degree (xiForward system 0 age vertex) : ℝ) ∧
        ((XiSimpleGraph system (0 + age)).degree (xiForward system 0 age vertex) : ℝ) ≤
          upper * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age) := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  letI : Nonempty (Fin K ⊕ Fin K) := ⟨Sum.inl system.initCol⟩
  obtain ⟨weights, weightsPositive, ratePositive, normalized, eigenpair⟩ :=
    primitive_matrix_spectralRadius_eigenpair_finite (degreeMatrix system) primitiveDegree
  have minimumPositive : 0 < finiteVectorMinimum weights :=
    (Finset.lt_inf'_iff _).2 (fun state _ => weightsPositive state)
  have birthBoundPositive := xiPrivateBirthWeightBound_positive system weights (fun state => (weightsPositive state).le)
  have weightAtMostOne (state : Fin K ⊕ Fin K) : weights state ≤ 1 := by
    rw [← normalized]
    exact Finset.single_le_sum (fun other _ => (weightsPositive other).le) (Finset.mem_univ state)
  have forwardBounds (birth : ℕ) (vertex : XiVtx system birth)
      (birthBound : (∑ state, degVec system birth vertex state * weights state) ≤
        xiPrivateBirthWeightBound system weights) (age : ℕ) :
      finiteVectorMinimum weights * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age ≤
        ((XiSimpleGraph system (birth + age)).degree (xiForward system birth age vertex) : ℝ) ∧
      ((XiSimpleGraph system (birth + age)).degree (xiForward system birth age vertex) : ℝ) ≤
        (xiPrivateBirthWeightBound system weights / finiteVectorMinimum weights) *
          finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age := by
    have beforeLower := xi_degree_eigenweight_lower_at_every_vertex system connected loopless unique
      plantingNonadjacent weights weightsPositive normalized birth vertex
    have afterBounds := xi_degree_eigenweight_comparison system connected loopless unique plantingNonadjacent
      weights weightsPositive normalized (birth + age) (xiForward system birth age vertex)
    rw [degree_eigenweight_forward system weights _ eigenpair] at afterBounds
    constructor
    · have scaledLower : finiteVectorMinimum weights *
          finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age ≤
          finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age *
            ∑ state, degVec system birth vertex state * weights state := by
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left beforeLower (pow_pos ratePositive age).le
      exact scaledLower.trans afterBounds.2
    · rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ minimumPositive).2
      simpa only [mul_comm] using afterBounds.1.trans
        (mul_le_mul_of_nonneg_left birthBound (pow_pos ratePositive age).le)
  refine ⟨finiteVectorMinimum weights,
    xiPrivateBirthWeightBound system weights / finiteVectorMinimum weights,
    minimumPositive, div_pos birthBoundPositive minimumPositive, ?_, ?_⟩
  · intro level vertex age
    apply forwardBounds (level + 1) (Sum.inr vertex) _ age
    rw [private_vertex_degree_weight_eq_rule_weight]
    exact xiRuleDegreeWeight_le_birth_bound system weights (fun state => (weightsPositive state).le) _ _
  · intro vertex age
    apply forwardBounds 0 vertex _ age
    rw [degree_initial_eigenweight]
    cases vertex <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      exact (weightAtMostOne _).trans
        (xiPrivateBirthWeightBound_ge_one system weights (fun state => (weightsPositive state).le))

end
end EIGS

#print axioms EIGS.xi_degree_eigenweight_comparison
#print axioms EIGS.xi_degree_eigenweight_lower_at_every_vertex
#print axioms EIGS.xiSimpleGraph_uniform_birth_degree_spectral_growth
