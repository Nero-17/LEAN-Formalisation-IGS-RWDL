import RequestProject.Section31.EIGSSpeedWeakConvergence
import RequestProject.Section2LocalBall

/-! The native endpoint speed probability is the actual simple-graph degree law
under the original simplicity assumptions. -/

namespace EIGS

open MeasureTheory
open scoped BigOperators ENNReal Classical

noncomputable section

variable {K : ℕ}

theorem xiVertexIncidenceCount_eq_degree (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (level : ℕ) (vertex : XiVtx system level) :
    xiVertexIncidenceCount system level vertex = (XiSimpleGraph system level).degree vertex := by
  classical
  have degree_sum := (XiNetwork system level).degree_eq_incident_edge_sum
    (xiNetwork_loopless system ruleConnected rulesLoopless level)
    (xiNetwork_edges_unique system ruleConnected rulesLoopless rulesUnique plantingNonadjacent level) vertex
  have incidence_sum : (xiVertexIncidenceCount system level vertex : ℝ) =
      ∑ edge, ((if XiTail system level edge = vertex then (1 : ℝ) else 0) +
        (if XiHead system level edge = vertex then (1 : ℝ) else 0)) := by
    simp only [xiVertexIncidenceCount, Nat.cast_add, Nat.card_eq_fintype_card,
      Fintype.card_subtype, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, Finset.sum_add_distrib]
  have incidence_degree : (xiVertexIncidenceCount system level vertex : ℝ) =
      ((XiSimpleGraph system level).degree vertex : ℝ) := incidence_sum.trans degree_sum.symm
  exact_mod_cast incidence_degree

theorem xiVertexSpeedMeasure_singleton_degree (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (mass : XiMassParameters system) (level : ℕ) (vertex : XiVtx system level) :
    xiVertexSpeedMeasure system mass level {vertex} =
      ((XiSimpleGraph system level).degree vertex : ℝ≥0∞) /
        (2 * (totalEdges system.toRuleData level : ℝ≥0∞)) := by
  rw [xiVertexSpeedMeasure_singleton, xiVertexIncidenceCount_eq_degree system
    ruleConnected rulesLoopless rulesUnique plantingNonadjacent]

end
end EIGS


#print axioms EIGS.xiVertexIncidenceCount_eq_degree
#print axioms EIGS.xiVertexSpeedMeasure_singleton_degree
