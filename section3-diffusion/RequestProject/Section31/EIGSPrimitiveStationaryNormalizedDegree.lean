import RequestProject.Section31.EIGSPrimitiveMaximumDegreeLimit

/-! The stationary normalized degree is the limit of degree divided by
the maximum degree of the same actual finite graph, as in Li--Britz,
arXiv:2109.14463v2 Definition 3.1. Perron and maximum limits are constructed
from the rules. The point-count distribution is a separate next step.
Candidate source. -/

namespace EIGS
open Filter Topology
open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

def xiActualMaxNormalizedDegree (system : EIGSData K) (level : ℕ)
    (vertex : XiVertexUnion system) : ℝ :=
  if born : xiUnionBirth system vertex ≤ level then
    ((XiSimpleGraph system level).degree (xiVertexAtLevel system vertex level born) : ℝ) /
      ((XiSimpleGraph system level).maxDegree : ℝ)
  else 0

theorem xiActualMaxNormalizedDegree_eq_normalized_quotient (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (rate : ℝ) (ratePositive : 0 < rate) (level : ℕ) (vertex : XiVertexUnion system) :
    xiActualMaxNormalizedDegree system level vertex =
      xiNormalizedDegreeAtLevel system rate level vertex /
        (((XiSimpleGraph system level).maxDegree : ℝ) / rate ^ level) := by
  unfold xiActualMaxNormalizedDegree xiNormalizedDegreeAtLevel
  split_ifs with born
  · rw [← xiSimpleGraph_degree_eq_degree_state_sum system connected loopless unique plantingNonadjacent]
    exact (div_div_div_cancel_right₀ (pow_ne_zero level ratePositive.ne') _ _).symm
  · exact (zero_div _).symm

theorem primitive_degree_stationary_normalized_limit (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (primitive : (degreeMatrix system).IsPrimitive)
    (degreeSupercritical : 1 < finiteRealMatrixSpectralRadius (degreeMatrix system)) :
    ∃ stationary : XiVertexUnion system → ℝ,
      (∀ vertex, 0 < stationary vertex ∧ stationary vertex ≤ 1) ∧
      (∃ vertex, stationary vertex = 1) ∧
      ∀ vertex, Tendsto (fun level : ℕ => xiActualMaxNormalizedDegree system level vertex)
        atTop (𝓝 (stationary vertex)) := by
  obtain ⟨weights, coefficient, maximizer, weightsPositive, normalized, eigenpair,
    coefficientPositive, pointwise, domination, maximumConvergence⟩ :=
      primitive_degree_actual_maximum_normalized_limit system connected loopless unique
        plantingNonadjacent primitive degreeSupercritical
  have maximumPositive := (pointwise maximizer).1
  refine ⟨fun vertex => xiDegreeLimitAmplitude system weights coefficient
    (finiteRealMatrixSpectralRadius (degreeMatrix system)) vertex /
      xiDegreeLimitAmplitude system weights coefficient
        (finiteRealMatrixSpectralRadius (degreeMatrix system)) maximizer, ?_, ?_, ?_⟩
  · intro vertex
    exact ⟨div_pos (pointwise vertex).1 maximumPositive,
      (div_le_one₀ maximumPositive).2 (domination vertex)⟩
  · exact ⟨maximizer, div_self maximumPositive.ne'⟩
  · intro vertex
    have quotientConvergence := (pointwise vertex).2.div maximumConvergence maximumPositive.ne'
    simpa only [xiActualMaxNormalizedDegree_eq_normalized_quotient system connected
      loopless unique plantingNonadjacent (finiteRealMatrixSpectralRadius (degreeMatrix system))
      (zero_lt_one.trans degreeSupercritical)] using quotientConvergence

end
end EIGS

#print axioms EIGS.xiActualMaxNormalizedDegree_eq_normalized_quotient
#print axioms EIGS.primitive_degree_stationary_normalized_limit
