import RequestProject.Section31.EIGSDegreeEigenweight
import RequestProject.Section31.EIGSTraceEnergy
import RequestProject.Section31.FiniteMarkovVectorRange
import RequestProject.Section2LocalBall

/-! Actual uniform bounds over all finite vertices, with decay in birth level.
The finite rule bound and Perron-weight identity are filled internally.
This is the uniform tail needed for global maximum-degree normalization.
Candidate source. -/

namespace EIGS
open Filter Topology
open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

theorem degree_initial_eigenweight (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (vertex : Bool) :
    (∑ state, degVec system 0 vertex state * weights state) =
      if vertex then weights (Sum.inr system.initCol) else weights (Sum.inl system.initCol) := by
  cases vertex <;>
    simp [degVec, outDeg, inDeg, Fintype.sum_sum_type, XiTail, XiHead, XiEnds,
      XiCol, XiLvl, XiEdge, EIGSData.toRuleData, apply_ite, ite_mul, eq_comm]

theorem xiPrivateBirthWeightBound_ge_one (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (nonnegative : ∀ state, 0 ≤ weights state) :
    1 ≤ xiPrivateBirthWeightBound system weights := by
  have sumNonnegative : 0 ≤ ∑ colour, ∑ vertex : (system.rule colour).V,
      xiRuleDegreeWeight system weights colour vertex :=
    Finset.sum_nonneg (fun colour _ => Finset.sum_nonneg
      (fun vertex _ => xiRuleDegreeWeight_nonnegative system weights nonnegative colour vertex))
  unfold xiPrivateBirthWeightBound
  linarith

theorem degree_weight_uniform_birth_bound (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (weightsNonnegative : ∀ state, 0 ≤ weights state)
    (normalized : (∑ state, weights state) = 1) (rate : ℝ) (ratePositive : 0 < rate)
    (eigenpair : (degreeMatrix system).mulVec weights = rate • weights) :
    ∀ level (vertex : XiVtx system level),
      (∑ state, degVec system level vertex state * weights state) ≤
        xiPrivateBirthWeightBound system weights *
          rate ^ (level - xiUnionBirth system (xiVertexEmbedding system level vertex)) := by
  have initialBound (vertex : Bool) :
      (∑ state, degVec system 0 vertex state * weights state) ≤
        xiPrivateBirthWeightBound system weights := by
    have stateBound (state : Fin K ⊕ Fin K) : weights state ≤ 1 := by
      rw [← normalized]
      exact Finset.single_le_sum (fun state _ => weightsNonnegative state) (Finset.mem_univ state)
    rw [degree_initial_eigenweight]
    cases vertex <;> exact (stateBound _).trans
      (xiPrivateBirthWeightBound_ge_one system weights weightsNonnegative)
  intro level
  induction level with
  | zero =>
      intro vertex
      simpa only [xiVertexEmbedding, xiUnionBirth, Nat.sub_self, pow_zero, mul_one] using initialBound vertex
  | succ level induction =>
      intro vertex
      rcases vertex with vertex | ⟨edge, privateVertex⟩
      · have oneStep := degree_eigenweight_forward system weights rate eigenpair level 1 vertex
        simp only [xiForward, pow_one, id_eq] at oneStep
        rw [oneStep]
        have birthLe := xiUnionBirth_embedding_le system level vertex
        have exponentIdentity :
            level + 1 - xiUnionBirth system (xiVertexEmbedding system level vertex) =
              (level - xiUnionBirth system (xiVertexEmbedding system level vertex)) + 1 := by omega
        have comparison := mul_le_mul_of_nonneg_left (induction vertex) ratePositive.le
        simpa only [xiVertexEmbedding_old, exponentIdentity, pow_succ,
          mul_assoc, mul_comm, mul_left_comm] using comparison
      · simpa only [xiVertexEmbedding, xiUnionBirth, Nat.sub_self, pow_zero, mul_one] using
          private_vertex_degree_weight_le_birth_bound system weights weightsNonnegative level edge privateVertex

theorem degree_weight_normalized_birth_bound (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (weightsNonnegative : ∀ state, 0 ≤ weights state)
    (normalized : (∑ state, weights state) = 1) (rate : ℝ) (ratePositive : 0 < rate)
    (eigenpair : (degreeMatrix system).mulVec weights = rate • weights)
    (level : ℕ) (vertex : XiVtx system level) :
    (∑ state, degVec system level vertex state * weights state) / rate ^ level ≤
      xiPrivateBirthWeightBound system weights /
        rate ^ xiUnionBirth system (xiVertexEmbedding system level vertex) := by
  apply (div_le_iff₀ (pow_pos ratePositive level)).2
  have birthLe := xiUnionBirth_embedding_le system level vertex
  have powerIdentity : rate ^ level =
      rate ^ (level - xiUnionBirth system (xiVertexEmbedding system level vertex)) *
        rate ^ xiUnionBirth system (xiVertexEmbedding system level vertex) := by
    rw [← pow_add, Nat.sub_add_cancel birthLe]
  calc
    (∑ state, degVec system level vertex state * weights state) ≤
        xiPrivateBirthWeightBound system weights *
          rate ^ (level - xiUnionBirth system (xiVertexEmbedding system level vertex)) :=
      degree_weight_uniform_birth_bound system weights weightsNonnegative normalized rate ratePositive eigenpair level vertex
    _ = (xiPrivateBirthWeightBound system weights /
          rate ^ xiUnionBirth system (xiVertexEmbedding system level vertex)) * rate ^ level := by
      rw [powerIdentity]
      field_simp [ratePositive.ne'] <;> ring

theorem degree_uniform_normalized_birth_bound (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (weightsPositive : ∀ state, 0 < weights state)
    (normalized : (∑ state, weights state) = 1) (rate : ℝ) (ratePositive : 0 < rate)
    (eigenpair : (degreeMatrix system).mulVec weights = rate • weights) :
    ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ level (vertex : XiVtx system level),
      (∑ state, degVec system level vertex state) / rate ^ level ≤
        coefficient / rate ^ xiUnionBirth system (xiVertexEmbedding system level vertex) := by
  letI : Nonempty (Fin K ⊕ Fin K) := ⟨Sum.inl system.initCol⟩
  have minimumPositive : 0 < finiteVectorMinimum weights :=
    (Finset.lt_inf'_iff _).2 (fun state _ => weightsPositive state)
  refine ⟨xiPrivateBirthWeightBound system weights / finiteVectorMinimum weights,
    div_pos (xiPrivateBirthWeightBound_positive system weights (fun state => (weightsPositive state).le))
      minimumPositive, ?_⟩
  intro level vertex
  have weightedLower :
      (∑ state, degVec system level vertex state) * finiteVectorMinimum weights ≤
        ∑ state, degVec system level vertex state * weights state := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro state _
    have degreeNonnegative : 0 ≤ degVec system level vertex state := by
      cases state <;> exact Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_left (finiteVector_range_bounds weights state).1 degreeNonnegative
  have weightedBound := degree_weight_normalized_birth_bound system weights
    (fun state => (weightsPositive state).le) normalized rate ratePositive eigenpair level vertex
  calc
    (∑ state, degVec system level vertex state) / rate ^ level ≤
        ((∑ state, degVec system level vertex state * weights state) / rate ^ level) /
          finiteVectorMinimum weights := by
      apply (le_div_iff₀ minimumPositive).2
      simpa only [div_mul_eq_mul_div] using
        div_le_div_of_nonneg_right weightedLower (pow_pos ratePositive level).le
    _ ≤ (xiPrivateBirthWeightBound system weights /
          rate ^ xiUnionBirth system (xiVertexEmbedding system level vertex)) / finiteVectorMinimum weights :=
      div_le_div_of_nonneg_right weightedBound minimumPositive.le
    _ = (xiPrivateBirthWeightBound system weights / finiteVectorMinimum weights) /
          rate ^ xiUnionBirth system (xiVertexEmbedding system level vertex) := by ring

theorem degree_uniform_recent_birth_tail (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (weightsPositive : ∀ state, 0 < weights state)
    (normalized : (∑ state, weights state) = 1) (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (degreeMatrix system).mulVec weights = rate • weights) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ threshold : ℕ,
      ∀ level (vertex : XiVtx system level),
        threshold ≤ xiUnionBirth system (xiVertexEmbedding system level vertex) →
        (∑ state, degVec system level vertex state) / rate ^ level < epsilon := by
  obtain ⟨coefficient, coefficientPositive, uniformBound⟩ :=
    degree_uniform_normalized_birth_bound system weights weightsPositive normalized rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair
  have tailConvergence : Tendsto (fun threshold : ℕ => coefficient / rate ^ threshold)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt rateGreaterThanOne)).const_mul coefficient
  intro epsilon epsilonPositive
  obtain ⟨threshold, small⟩ := (tailConvergence.eventually_lt_const epsilonPositive).exists
  refine ⟨threshold, ?_⟩
  intro level vertex birthLarge
  have decreasing : coefficient /
      rate ^ xiUnionBirth system (xiVertexEmbedding system level vertex) ≤ coefficient / rate ^ threshold :=
    div_le_div_of_nonneg_left coefficientPositive.le
      (pow_pos (zero_lt_one.trans rateGreaterThanOne) threshold)
      (pow_le_pow_right₀ rateGreaterThanOne.le birthLarge)
  exact ((uniformBound level vertex).trans decreasing).trans_lt small

theorem xiSimpleGraph_uniform_recent_birth_degree_tail (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (weights : Fin K ⊕ Fin K → ℝ) (weightsPositive : ∀ state, 0 < weights state)
    (normalized : (∑ state, weights state) = 1) (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (degreeMatrix system).mulVec weights = rate • weights) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ threshold : ℕ,
      ∀ level (vertex : XiVtx system level),
        threshold ≤ xiUnionBirth system (xiVertexEmbedding system level vertex) →
        ((XiSimpleGraph system level).degree vertex : ℝ) / rate ^ level < epsilon := by
  simpa only [xiSimpleGraph_degree_eq_degree_state_sum system connected loopless unique plantingNonadjacent] using
    degree_uniform_recent_birth_tail system weights weightsPositive normalized rate rateGreaterThanOne eigenpair

end
end EIGS

#print axioms EIGS.degree_weight_uniform_birth_bound
#print axioms EIGS.degree_weight_normalized_birth_bound
#print axioms EIGS.degree_uniform_normalized_birth_bound
#print axioms EIGS.xiSimpleGraph_uniform_recent_birth_degree_tail
