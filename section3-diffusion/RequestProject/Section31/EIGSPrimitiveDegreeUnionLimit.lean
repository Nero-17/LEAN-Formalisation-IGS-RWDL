import RequestProject.Section31.EIGSPrimitiveDegreeNormalizedGrowth
import RequestProject.Section31.EIGSUniformBirthDegreeBound
import RequestProject.Section31.EIGSVertexInclusion

/-! Actual absolute-generation normalized degrees on the same vertex union.
The initially absent vertex is assigned zero, which affects only finitely
many generations for each fixed vertex. Pointwise limits use one Perron
vector and one coefficient for all birth levels. Candidate source. -/

namespace EIGS
open Filter Topology
open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

def xiNormalizedDegreeAtLevel (system : EIGSData K) (rate : ℝ)
    (level : ℕ) (vertex : XiVertexUnion system) : ℝ :=
  if born : xiUnionBirth system vertex ≤ level then
    (∑ state, degVec system level (xiVertexAtLevel system vertex level born) state) / rate ^ level
  else 0

def xiDegreeLimitAmplitude (system : EIGSData K) (weights : Fin K ⊕ Fin K → ℝ)
    (coefficient rate : ℝ) (vertex : XiVertexUnion system) : ℝ :=
  coefficient * (∑ state, degVec system (xiUnionBirth system vertex)
    (xiVertexAtLevel system vertex (xiUnionBirth system vertex) le_rfl) state * weights state) /
      rate ^ xiUnionBirth system vertex

theorem xiVertexAtLevel_forward_from_birth (system : EIGSData K)
    (vertex : XiVertexUnion system) (age : ℕ) :
    xiVertexAtLevel system vertex (xiUnionBirth system vertex + age) (Nat.le_add_right _ _) =
      xiForward system (xiUnionBirth system vertex) age
        (xiVertexAtLevel system vertex (xiUnionBirth system vertex) le_rfl) := by
  apply xiVertexEmbedding_injective system (xiUnionBirth system vertex + age)
  rw [xiVertexEmbedding_atLevel, xiVertexEmbedding_forward, xiVertexEmbedding_atLevel]

theorem xiNormalizedDegreeAtLevel_age_identity (system : EIGSData K)
    (rate : ℝ) (vertex : XiVertexUnion system) (age : ℕ) :
    xiNormalizedDegreeAtLevel system rate (xiUnionBirth system vertex + age) vertex =
      ((∑ state, degVec system (xiUnionBirth system vertex + age)
        (xiForward system (xiUnionBirth system vertex) age
          (xiVertexAtLevel system vertex (xiUnionBirth system vertex) le_rfl)) state) /
        rate ^ age) / rate ^ xiUnionBirth system vertex := by
  unfold xiNormalizedDegreeAtLevel
  rw [dif_pos (Nat.le_add_right _ _), xiVertexAtLevel_forward_from_birth, pow_add, div_div]
  congr 1
  ring

theorem xiNormalizedDegreeAtLevel_embedding (system : EIGSData K)
    (rate : ℝ) (level : ℕ) (vertex : XiVtx system level) :
    xiNormalizedDegreeAtLevel system rate level (xiVertexEmbedding system level vertex) =
      (∑ state, degVec system level vertex state) / rate ^ level := by
  unfold xiNormalizedDegreeAtLevel
  rw [dif_pos (xiUnionBirth_embedding_le system level vertex)]
  have equality : xiVertexAtLevel system (xiVertexEmbedding system level vertex) level
      (xiUnionBirth_embedding_le system level vertex) = vertex := by
    apply xiVertexEmbedding_injective system level
    rw [xiVertexEmbedding_atLevel]
  rw [equality]

theorem primitive_degree_vertex_union_normalized_limit (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (primitive : (degreeMatrix system).IsPrimitive) :
    ∃ weights : Fin K ⊕ Fin K → ℝ, ∃ coefficient : ℝ,
      (∀ state, 0 < weights state) ∧ (∑ state, weights state) = 1 ∧
      (degreeMatrix system).mulVec weights = finiteRealMatrixSpectralRadius (degreeMatrix system) • weights ∧
      0 < coefficient ∧ ∀ vertex : XiVertexUnion system,
        0 < xiDegreeLimitAmplitude system weights coefficient
          (finiteRealMatrixSpectralRadius (degreeMatrix system)) vertex ∧
        Tendsto (fun level : ℕ => xiNormalizedDegreeAtLevel system
          (finiteRealMatrixSpectralRadius (degreeMatrix system)) level vertex) atTop
          (𝓝 (xiDegreeLimitAmplitude system weights coefficient
            (finiteRealMatrixSpectralRadius (degreeMatrix system)) vertex)) := by
  obtain ⟨weights, coefficient, weightsPositive, normalized, eigenpair, coefficientPositive, convergence⟩ :=
    degree_normalized_growth_from_primitive_rules system connected primitive
  letI : Nonempty (Fin K ⊕ Fin K) := ⟨Sum.inl system.initCol⟩
  have ratePositive : 0 < finiteRealMatrixSpectralRadius (degreeMatrix system) := by
    obtain ⟨_, _, positive, _⟩ := primitive_matrix_spectralRadius_eigenpair_finite (degreeMatrix system) primitive
    exact positive
  refine ⟨weights, coefficient, weightsPositive, normalized, eigenpair, coefficientPositive, ?_⟩
  intro vertex
  have actual := convergence (xiUnionBirth system vertex)
    (xiVertexAtLevel system vertex (xiUnionBirth system vertex) le_rfl)
  refine ⟨div_pos actual.1 (pow_pos ratePositive _), ?_⟩
  apply (tendsto_add_atTop_iff_nat (xiUnionBirth system vertex)).mp
  have shifted := actual.2.div_const
    ((finiteRealMatrixSpectralRadius (degreeMatrix system)) ^ xiUnionBirth system vertex)
  simpa only [xiNormalizedDegreeAtLevel_age_identity, xiDegreeLimitAmplitude, Nat.add_comm] using shifted

end
end EIGS

#print axioms EIGS.xiVertexAtLevel_forward_from_birth
#print axioms EIGS.xiNormalizedDegreeAtLevel_embedding
#print axioms EIGS.primitive_degree_vertex_union_normalized_limit
