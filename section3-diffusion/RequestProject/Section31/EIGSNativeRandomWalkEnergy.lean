import RequestProject.Section31.EIGSNativeDiscreteEnergy
import RequestProject.Section31.EIGSSpeedDegree
import RequestProject.Section2GroundedTrace
import RequestProject.Section2RandomWalk
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The existing simple-random-walk transition probabilities act on the actual
native speed L² space. Its generator quadratic form is precisely the actual
scaled unit-edge energy, with the explicit factor 2 |E| κ ρ^n. -/

namespace EIGS

open MeasureTheory Matrix
open scoped BigOperators ENNReal Classical

noncomputable section

set_option maxHeartbeats 2400000

variable {K : ℕ}

/-- The finite speed measure charges every vertex, so evaluation is an actual
linear equivalence, not a choice of representatives up to a null set. -/
def xiNativeEvaluationLinearEquiv (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) (level : ℕ) :
    Lp ℝ 2 (xiVertexSpeedMeasure system mass level) ≃ₗ[ℝ] (XiVtx system level → ℝ) where
  toFun function := fun vertex => function vertex
  invFun := xiFiniteSpeedL2 system mass level
  left_inv := xiFiniteSpeedL2_representative system mass level
  right_inv values := funext (xiFiniteSpeedL2_apply system rulesConnected mass level values)
  map_add' first second := funext fun vertex =>
    (xiVertexSpeedMeasure_ae_iff system rulesConnected mass level _).1
      (Lp.coeFn_add first second) vertex
  map_smul' scalar function := funext fun vertex =>
    (xiVertexSpeedMeasure_ae_iff system rulesConnected mass level _).1
      (Lp.coeFn_smul scalar function) vertex

/-- Transport the already-defined true simple-walk matrix `transProb` to native
L². Finite dimensionality proves continuity of this concrete linear map. -/
def xiNativeRandomWalk (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) (level : ℕ) :
    Lp ℝ 2 (xiVertexSpeedMeasure system mass level) →L[ℝ]
      Lp ℝ 2 (xiVertexSpeedMeasure system mass level) := by
  let equivalence := xiNativeEvaluationLinearEquiv system rulesConnected mass level
  letI : FiniteDimensional ℝ (Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :=
    equivalence.symm.finiteDimensional
  exact (equivalence.symm.toLinearMap.comp
    ((Matrix.toLin' (transProb (XiSimpleGraph system level))).comp
      equivalence.toLinearMap)).toContinuousLinearMap

theorem xiNativeRandomWalk_apply (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) (level : ℕ)
    (function : Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
    (vertex : XiVtx system level) :
    xiNativeRandomWalk system rulesConnected mass level function vertex =
      ∑ other, transProb (XiSimpleGraph system level) vertex other * function other := by
  change xiFiniteSpeedL2 system mass level
    (fun source => ∑ other, transProb (XiSimpleGraph system level) source other * function other)
      vertex = _
  exact xiFiniteSpeedL2_apply system rulesConnected mass level _ vertex

theorem lapMatrix_mulVec_eq_degree_mul_randomWalk_difference
    {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (values : Vertex → ℝ) (vertex : Vertex) (degreePositive : 0 < graph.degree vertex) :
    (graph.lapMatrix ℝ *ᵥ values) vertex =
      (graph.degree vertex : ℝ) *
        (values vertex - ∑ other, transProb graph vertex other * values other) := by
  have degreeNonzero : (graph.degree vertex : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr degreePositive)
  rw [EIGS.lapMatrix_mulVec_apply, transProb_smul_sum degreePositive,
    mul_sub, ← mul_assoc, mul_inv_cancel₀ degreeNonzero, one_mul]

variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (mass : XiMassParameters system) (level : ℕ)

include rulesConnected rulesLoopless rulesUnique plantingNonadjacent

theorem xiNativeL2_inner_degree
    (first second : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    inner ℝ first second =
      ∑ vertex, ((XiSimpleGraph system level).degree vertex : ℝ) /
        (2 * (totalEdges system.toRuleData level : ℝ)) * first vertex * second vertex := by
  rw [L2.inner_def, integral_fintype _ Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro vertex _
  rw [measureReal_def, xiVertexSpeedMeasure_singleton_degree system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent mass level vertex]
  simp [ENNReal.toReal_div, ENNReal.toReal_mul, mul_assoc, mul_comm]

theorem xiNativeRandomWalk_inner_difference
    (function : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    inner ℝ function (function - xiNativeRandomWalk system rulesConnected mass level function) =
      dirichletEnergy (XiSimpleGraph system level) (fun vertex => function vertex) /
        (2 * (totalEdges system.toRuleData level : ℝ)) := by
  have degreePositive : ∀ vertex : XiVtx system level,
      0 < (XiSimpleGraph system level).degree vertex := by
    intro vertex
    rw [← xiVertexIncidenceCount_eq_degree system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent level vertex]
    exact xiVertexIncidenceCount_positive system rulesConnected level vertex
  have subtraction : ∀ vertex : XiVtx system level,
      (function - xiNativeRandomWalk system rulesConnected mass level function) vertex =
        function vertex - xiNativeRandomWalk system rulesConnected mass level function vertex :=
    (xiVertexSpeedMeasure_ae_iff system rulesConnected mass level _).1
      (Lp.coeFn_sub function (xiNativeRandomWalk system rulesConnected mass level function))
  rw [xiNativeL2_inner_degree system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass level, dirichletEnergy_eq_quad, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro vertex _
  rw [subtraction, xiNativeRandomWalk_apply,
    lapMatrix_mulVec_eq_degree_mul_randomWalk_difference
      (XiSimpleGraph system level) (fun vertex => function vertex) vertex (degreePositive vertex)]
  ring

/-- The exact native generator normalization. No asymptotic approximation or
independently selected normalization is used in this identity. -/
theorem xiNativeScaledUnitEnergy_eq_randomWalk_form
    (resistanceRate normalization : ℝ)
    (function : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    xiNativeScaledUnitEnergy system mass resistanceRate normalization level function =
      (2 * normalization * resistanceRate ^ level * (totalEdges system.toRuleData level : ℝ)) *
        inner ℝ function (function - xiNativeRandomWalk system rulesConnected mass level function) := by
  have edgesNonzero : (totalEdges system.toRuleData level : ℝ) ≠ 0 := by
    letI : Nonempty (XiEdge system.toRuleData level) := mass.edge_nonempty level
    exact_mod_cast (Fintype.card_ne_zero (α := XiEdge system.toRuleData level))
  rw [xiNativeScaledUnitEnergy, xiScaledUnitEnergy,
    (XiNetwork system level).unit_potential_energy_eq_dirichletEnergy
      (xiNetwork_loopless system rulesConnected rulesLoopless level)
      (xiNetwork_edges_unique system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level),
    xiNativeRandomWalk_inner_difference system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent mass level]
  change normalization * resistanceRate ^ level *
    dirichletEnergy (XiSimpleGraph system level) (fun vertex => function vertex) = _
  field_simp [edgesNonzero]
  <;> ring

end
end EIGS

#print axioms EIGS.xiNativeEvaluationLinearEquiv
#print axioms EIGS.xiNativeRandomWalk_apply
#print axioms EIGS.lapMatrix_mulVec_eq_degree_mul_randomWalk_difference
#print axioms EIGS.xiNativeL2_inner_degree
#print axioms EIGS.xiNativeRandomWalk_inner_difference
#print axioms EIGS.xiNativeScaledUnitEnergy_eq_randomWalk_form
