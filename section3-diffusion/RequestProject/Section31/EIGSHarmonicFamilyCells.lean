import RequestProject.Section31.EIGSDescendantEndpointEdges
import RequestProject.Section31.EIGSHarmonicTraceMinimum

/-! Local cell bounds for an actual compatible harmonic family. The family
identities here are later supplied by the constructed stationary extension. -/

namespace EIGS

variable {K : ℕ}

section Harmonic

variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (initialLevel : ℕ) (values : ∀ level, XiVtx system level → ℝ)
    (stepAgreement : ∀ level, initialLevel ≤ level → values (level + 1) =
      xiHarmonicStep system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair level (values level))

include stepAgreement

theorem xiHarmonicFamily_boundary (offset : ℕ) (vertex : XiVtx system initialLevel) :
    values (initialLevel + offset) (xiForward system initialLevel offset vertex) = values initialLevel vertex := by
  induction offset with
  | zero => rfl
  | succ offset induction =>
      change values ((initialLevel + offset) + 1) (Sum.inl (xiForward system initialLevel offset vertex)) = _
      rw [stepAgreement (initialLevel + offset) (by omega)]
      exact (xiHarmonicStep_old system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
        (initialLevel + offset) (values (initialLevel + offset)) _).trans induction

theorem xiHarmonicFamily_descendant_range (offset : ℕ)
    (edge : XiEdge system.toRuleData (initialLevel + offset)) :
    (min (values initialLevel (XiTail system initialLevel (xiEdgeAncestor system initialLevel offset edge)))
        (values initialLevel (XiHead system initialLevel (xiEdgeAncestor system initialLevel offset edge))) ≤
      values (initialLevel + offset) (XiTail system (initialLevel + offset) edge) ∧
     values (initialLevel + offset) (XiTail system (initialLevel + offset) edge) ≤
       max (values initialLevel (XiTail system initialLevel (xiEdgeAncestor system initialLevel offset edge)))
         (values initialLevel (XiHead system initialLevel (xiEdgeAncestor system initialLevel offset edge)))) ∧
    (min (values initialLevel (XiTail system initialLevel (xiEdgeAncestor system initialLevel offset edge)))
        (values initialLevel (XiHead system initialLevel (xiEdgeAncestor system initialLevel offset edge))) ≤
      values (initialLevel + offset) (XiHead system (initialLevel + offset) edge) ∧
     values (initialLevel + offset) (XiHead system (initialLevel + offset) edge) ≤
       max (values initialLevel (XiTail system initialLevel (xiEdgeAncestor system initialLevel offset edge)))
         (values initialLevel (XiHead system initialLevel (xiEdgeAncestor system initialLevel offset edge)))) := by
  induction offset with
  | zero => exact ⟨⟨min_le_left _ _, le_max_left _ _⟩, ⟨min_le_right _ _, le_max_right _ _⟩⟩
  | succ offset induction =>
      have parentRange := induction edge.1
      have tailRange := xiHarmonicStep_rule_vertex_range system rulesConnected resistanceRate ratePositive
        resistanceVector vectorPositive eigenpair (initialLevel + offset) (values (initialLevel + offset))
        edge.1 ((system.rule _).tail edge.2)
      have headRange := xiHarmonicStep_rule_vertex_range system rulesConnected resistanceRate ratePositive
        resistanceVector vectorPositive eigenpair (initialLevel + offset) (values (initialLevel + offset))
        edge.1 ((system.rule _).head edge.2)
      rw [← stepAgreement (initialLevel + offset) (by omega)] at tailRange headRange
      exact ⟨⟨(le_min parentRange.1.1 parentRange.2.1).trans tailRange.1,
        tailRange.2.trans (max_le parentRange.1.2 parentRange.2.2)⟩,
        ⟨(le_min parentRange.1.1 parentRange.2.1).trans headRange.1,
        headRange.2.trans (max_le parentRange.1.2 parentRange.2.2)⟩⟩

theorem xiHarmonicFamily_local_edge_decay
    (contractionFactor : ℝ) (factorNonnegative : 0 ≤ contractionFactor)
    (stepContraction : ∀ level (oldValues : XiVtx system level → ℝ)
      (edge : XiEdge system.toRuleData (level + 1)),
      |xiHarmonicStep system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
          level oldValues (XiTail system (level + 1) edge) -
        xiHarmonicStep system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
          level oldValues (XiHead system (level + 1) edge)| ≤
        |oldValues (XiTail system level edge.1) - oldValues (XiHead system level edge.1)| * contractionFactor)
    (offset : ℕ) (edge : XiEdge system.toRuleData (initialLevel + offset)) :
    |values (initialLevel + offset) (XiTail system (initialLevel + offset) edge) -
      values (initialLevel + offset) (XiHead system (initialLevel + offset) edge)| ≤
    contractionFactor ^ offset *
      |values initialLevel (XiTail system initialLevel (xiEdgeAncestor system initialLevel offset edge)) -
        values initialLevel (XiHead system initialLevel (xiEdgeAncestor system initialLevel offset edge))| := by
  induction offset with
  | zero => simp only [pow_zero, one_mul]; exact le_rfl
  | succ offset induction =>
      have contraction := stepContraction (initialLevel + offset) (values (initialLevel + offset)) edge
      rw [← stepAgreement (initialLevel + offset) (by omega)] at contraction
      exact contraction.trans
        (by
          have multiplied := mul_le_mul_of_nonneg_right (induction edge.1) factorNonnegative
          convert multiplied using 1 <;> simp only [xiEdgeAncestor, pow_succ] <;> ring)

end Harmonic

end EIGS
