import RequestProject.Section31.EIGSPrimitiveStationaryNormalizedDegree
import RequestProject.Section31.EIGSPrivateBirthTypes

/-! One explicit actual stationary degree function and its finite-family
birth formulas. The normalizer is supplied by the proved actual maximum
limit in the rule-only existence theorem. Candidate source. -/

namespace EIGS
open Filter Topology
open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

def xiStationaryDegreeFromAmplitudes (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (coefficient rate normalizer : ℝ)
    (vertex : XiVertexUnion system) : ℝ :=
  xiDegreeLimitAmplitude system weights coefficient rate vertex / normalizer

def xiPrivateDegreeLadderCoefficient (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (coefficient rate normalizer : ℝ)
    (kind : XiPrivateBirthType system) : ℝ :=
  coefficient * xiRuleDegreeWeight system weights kind.1 kind.2.val / (rate * normalizer)

theorem xiStationaryDegree_private_birth_formula (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (coefficient rate normalizer : ℝ)
    (level : ℕ) (vertex : XiNewVertices system level) :
    xiStationaryDegreeFromAmplitudes system weights coefficient rate normalizer (Sum.inr ⟨level, vertex⟩) =
      xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer
        (xiPrivateBirthTypeOf system level vertex) / rate ^ level := by
  unfold xiStationaryDegreeFromAmplitudes xiPrivateDegreeLadderCoefficient
  rw [xiDegreeLimitAmplitude_private_birth, pow_succ, div_div, div_div]
  congr 1
  ring

theorem xiDegreeLimitAmplitude_initial (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (coefficient rate : ℝ) (vertex : Bool) :
    xiDegreeLimitAmplitude system weights coefficient rate (Sum.inl vertex) =
      coefficient * (if vertex then weights (Sum.inr system.initCol) else weights (Sum.inl system.initCol)) := by
  have representative : xiVertexAtLevel system (Sum.inl vertex) 0 le_rfl = vertex := by
    apply xiVertexEmbedding_injective system 0
    rw [xiVertexEmbedding_atLevel]
    rfl
  unfold xiDegreeLimitAmplitude
  change coefficient * (∑ state, degVec system 0
    (xiVertexAtLevel system (Sum.inl vertex) 0 le_rfl) state * weights state) / rate ^ 0 = _
  rw [representative, pow_zero, div_one, degree_initial_eigenweight]

theorem xiPrivateDegreeLadderCoefficient_positive (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (weights : Fin K ⊕ Fin K → ℝ) (weightsPositive : ∀ state, 0 < weights state)
    (coefficient rate normalizer : ℝ) (coefficientPositive : 0 < coefficient)
    (ratePositive : 0 < rate) (normalizerPositive : 0 < normalizer) (kind : XiPrivateBirthType system) :
    0 < xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer kind :=
  div_pos (mul_pos coefficientPositive
    (xiPrivateBirthType_weight_positive system connected distancePositive weights weightsPositive kind))
    (mul_pos ratePositive normalizerPositive)

theorem primitive_rules_explicit_stationary_degree (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (primitive : (degreeMatrix system).IsPrimitive)
    (degreeSupercritical : 1 < finiteRealMatrixSpectralRadius (degreeMatrix system)) :
    ∃ weights : Fin K ⊕ Fin K → ℝ, ∃ coefficient normalizer : ℝ,
      (∀ state, 0 < weights state) ∧ (∑ state, weights state) = 1 ∧
      (degreeMatrix system).mulVec weights = finiteRealMatrixSpectralRadius (degreeMatrix system) • weights ∧
      0 < coefficient ∧ 0 < normalizer ∧
      (∀ vertex, 0 < xiStationaryDegreeFromAmplitudes system weights coefficient
        (finiteRealMatrixSpectralRadius (degreeMatrix system)) normalizer vertex ∧
        xiStationaryDegreeFromAmplitudes system weights coefficient
          (finiteRealMatrixSpectralRadius (degreeMatrix system)) normalizer vertex ≤ 1) ∧
      ∀ vertex, Tendsto (fun level => xiActualMaxNormalizedDegree system level vertex) atTop
        (𝓝 (xiStationaryDegreeFromAmplitudes system weights coefficient
          (finiteRealMatrixSpectralRadius (degreeMatrix system)) normalizer vertex)) := by
  obtain ⟨weights, coefficient, maximizer, weightsPositive, normalized, eigenpair,
    coefficientPositive, pointwise, domination, maximumConvergence⟩ :=
      primitive_degree_actual_maximum_normalized_limit system connected loopless unique
        plantingNonadjacent primitive degreeSupercritical
  refine ⟨weights, coefficient, xiDegreeLimitAmplitude system weights coefficient
    (finiteRealMatrixSpectralRadius (degreeMatrix system)) maximizer,
    weightsPositive, normalized, eigenpair, coefficientPositive, (pointwise maximizer).1, ?_, ?_⟩
  · intro vertex
    exact ⟨div_pos (pointwise vertex).1 (pointwise maximizer).1,
      (div_le_one₀ (pointwise maximizer).1).2 (domination vertex)⟩
  · intro vertex
    have actual := (pointwise vertex).2.div maximumConvergence (pointwise maximizer).1.ne'
    simpa only [xiStationaryDegreeFromAmplitudes, xiActualMaxNormalizedDegree_eq_normalized_quotient
      system connected loopless unique plantingNonadjacent
        (finiteRealMatrixSpectralRadius (degreeMatrix system)) (zero_lt_one.trans degreeSupercritical)] using actual

end
end EIGS

#print axioms EIGS.xiStationaryDegree_private_birth_formula
#print axioms EIGS.xiDegreeLimitAmplitude_initial
#print axioms EIGS.xiPrivateDegreeLadderCoefficient_positive
#print axioms EIGS.primitive_rules_explicit_stationary_degree
