import RequestProject.Section31.EIGSPrimitiveDegreeUnionLimit
import RequestProject.Section31.FiniteBirthMaximumConvergence

/-! Maximum-degree normalization on the actual graphs. Pointwise Perron
limits, finite early birth sets, and the actual uniform birth tail produce
one positive attained maximum limit. No maximum-limit hypothesis is used.
The supercritical degree range is explicit. Candidate source. -/

namespace EIGS
open Filter Topology
open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

theorem xiUnion_early_birth_finite (system : EIGSData K) (threshold : ℕ) :
    {vertex : XiVertexUnion system | xiUnionBirth system vertex < threshold}.Finite := by
  apply (Set.finite_range (xiVertexEmbedding system threshold)).subset
  intro vertex early
  exact ⟨xiVertexAtLevel system vertex threshold (Nat.le_of_lt early),
    xiVertexEmbedding_atLevel system vertex threshold (Nat.le_of_lt early)⟩

theorem xiNormalizedDegreeAtLevel_uniform_birth_tail (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (weightsPositive : ∀ state, 0 < weights state)
    (normalized : (∑ state, weights state) = 1) (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (degreeMatrix system).mulVec weights = rate • weights) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ threshold : ℕ,
      ∀ level vertex, threshold ≤ xiUnionBirth system vertex →
        xiNormalizedDegreeAtLevel system rate level vertex < epsilon := by
  intro epsilon epsilonPositive
  obtain ⟨threshold, finiteTail⟩ := degree_uniform_recent_birth_tail system weights
    weightsPositive normalized rate rateGreaterThanOne eigenpair epsilon epsilonPositive
  refine ⟨threshold, ?_⟩
  intro level vertex late
  unfold xiNormalizedDegreeAtLevel
  split_ifs with born
  · have finiteSmall := finiteTail level (xiVertexAtLevel system vertex level born)
    rw [xiVertexEmbedding_atLevel] at finiteSmall
    exact finiteSmall late
  · exact epsilonPositive

theorem xiNormalizedDegreeAtLevel_le_graph_maximum (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (rate : ℝ) (ratePositive : 0 < rate) (level : ℕ) (vertex : XiVertexUnion system) :
    xiNormalizedDegreeAtLevel system rate level vertex ≤
      ((XiSimpleGraph system level).maxDegree : ℝ) / rate ^ level := by
  unfold xiNormalizedDegreeAtLevel
  split_ifs with born
  · rw [← xiSimpleGraph_degree_eq_degree_state_sum system connected loopless unique plantingNonadjacent]
    apply div_le_div_of_nonneg_right _ (pow_pos ratePositive level).le
    exact_mod_cast (XiSimpleGraph system level).degree_le_maxDegree
      (xiVertexAtLevel system vertex level born)
  · exact div_nonneg (Nat.cast_nonneg _) (pow_pos ratePositive level).le

theorem xiNormalizedDegreeAtLevel_graph_maximum_attained (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour)) (rate : ℝ) (level : ℕ) :
    ∃ vertex : XiVertexUnion system,
      ((XiSimpleGraph system level).maxDegree : ℝ) / rate ^ level =
        xiNormalizedDegreeAtLevel system rate level vertex := by
  letI : Nonempty (XiVtx system level) :=
    ⟨by simpa only [Nat.zero_add] using xiLiftVertices system 0 level true⟩
  obtain ⟨vertex, maximumEquality⟩ := (XiSimpleGraph system level).exists_maximal_degree_vertex
  refine ⟨xiVertexEmbedding system level vertex, ?_⟩
  rw [xiNormalizedDegreeAtLevel_embedding, maximumEquality,
    xiSimpleGraph_degree_eq_degree_state_sum system connected loopless unique plantingNonadjacent]

theorem primitive_degree_actual_maximum_normalized_limit (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (primitive : (degreeMatrix system).IsPrimitive)
    (degreeSupercritical : 1 < finiteRealMatrixSpectralRadius (degreeMatrix system)) :
    ∃ weights : Fin K ⊕ Fin K → ℝ, ∃ coefficient : ℝ, ∃ maximizer : XiVertexUnion system,
      (∀ state, 0 < weights state) ∧ (∑ state, weights state) = 1 ∧
      (degreeMatrix system).mulVec weights = finiteRealMatrixSpectralRadius (degreeMatrix system) • weights ∧
      0 < coefficient ∧
      (∀ vertex, 0 < xiDegreeLimitAmplitude system weights coefficient
        (finiteRealMatrixSpectralRadius (degreeMatrix system)) vertex ∧
        Tendsto (fun level => xiNormalizedDegreeAtLevel system
          (finiteRealMatrixSpectralRadius (degreeMatrix system)) level vertex) atTop
          (𝓝 (xiDegreeLimitAmplitude system weights coefficient
            (finiteRealMatrixSpectralRadius (degreeMatrix system)) vertex))) ∧
      (∀ vertex, xiDegreeLimitAmplitude system weights coefficient
        (finiteRealMatrixSpectralRadius (degreeMatrix system)) vertex ≤
          xiDegreeLimitAmplitude system weights coefficient
            (finiteRealMatrixSpectralRadius (degreeMatrix system)) maximizer) ∧
      Tendsto (fun level => ((XiSimpleGraph system level).maxDegree : ℝ) /
        (finiteRealMatrixSpectralRadius (degreeMatrix system)) ^ level) atTop
        (𝓝 (xiDegreeLimitAmplitude system weights coefficient
          (finiteRealMatrixSpectralRadius (degreeMatrix system)) maximizer)) := by
  obtain ⟨weights, coefficient, weightsPositive, normalized, eigenpair, coefficientPositive, pointwise⟩ :=
    primitive_degree_vertex_union_normalized_limit system connected primitive
  letI : Nonempty (XiVertexUnion system) := ⟨Sum.inl false⟩
  obtain ⟨maximizer, maximumPositive, domination, convergence⟩ :=
    finite_birth_maximum_convergence (xiUnionBirth system)
      (xiNormalizedDegreeAtLevel system (finiteRealMatrixSpectralRadius (degreeMatrix system)))
      (xiDegreeLimitAmplitude system weights coefficient (finiteRealMatrixSpectralRadius (degreeMatrix system)))
      (xiUnion_early_birth_finite system) (fun vertex => (pointwise vertex).1)
      (fun vertex => (pointwise vertex).2)
      (xiNormalizedDegreeAtLevel_uniform_birth_tail system weights weightsPositive normalized
        (finiteRealMatrixSpectralRadius (degreeMatrix system)) degreeSupercritical eigenpair)
      (fun level => ((XiSimpleGraph system level).maxDegree : ℝ) /
        (finiteRealMatrixSpectralRadius (degreeMatrix system)) ^ level)
      (xiNormalizedDegreeAtLevel_le_graph_maximum system connected loopless unique plantingNonadjacent
        (finiteRealMatrixSpectralRadius (degreeMatrix system)) (zero_lt_one.trans degreeSupercritical))
      (xiNormalizedDegreeAtLevel_graph_maximum_attained system connected loopless unique plantingNonadjacent
        (finiteRealMatrixSpectralRadius (degreeMatrix system)))
  exact ⟨weights, coefficient, maximizer, weightsPositive, normalized, eigenpair,
    coefficientPositive, pointwise, domination, convergence⟩

end
end EIGS

#print axioms EIGS.xiUnion_early_birth_finite
#print axioms EIGS.xiNormalizedDegreeAtLevel_graph_maximum_attained
#print axioms EIGS.primitive_degree_actual_maximum_normalized_limit
