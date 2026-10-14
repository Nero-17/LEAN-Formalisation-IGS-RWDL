import RequestProject.Section1Vertices

/-! Degrees at the actual birth of a private rule vertex. A private vertex
has precisely the incident arcs of its own rule copy. No growth or
distribution formula is assumed. Candidate source. -/

namespace EIGS
open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

theorem embedRuleVtx_eq_private_iff (system : EIGSData K) (level : ℕ)
    (edge : XiEdge system.toRuleData level) (tail head : XiVtx system level)
    (privateVertex : {vertex : (system.rule (XiCol system.toRuleData level edge)).V //
      vertex ≠ system.plantPlus (XiCol system.toRuleData level edge) ∧
      vertex ≠ system.plantMinus (XiCol system.toRuleData level edge)})
    (endpoint : (system.rule (XiCol system.toRuleData level edge)).V) :
    embedRuleVtx system level edge tail head endpoint = Sum.inr ⟨edge, privateVertex⟩ ↔
      endpoint = privateVertex.val := by
  constructor
  · intro equality
    unfold embedRuleVtx at equality
    split_ifs at equality with plus minus
    have privateEquality := (Sigma.mk.inj_iff.1 (Sum.inr.inj equality)).2
    exact congrArg Subtype.val (eq_of_heq privateEquality)
  · intro equality
    subst endpoint
    exact embedRuleVtx_interior system level edge tail head
      privateVertex.property.1 privateVertex.property.2

theorem embedRuleVtx_ne_private_of_edge_ne (system : EIGSData K) (level : ℕ)
    (edge otherEdge : XiEdge system.toRuleData level) (different : otherEdge ≠ edge)
    (tail head : XiVtx system level)
    (privateVertex : {vertex : (system.rule (XiCol system.toRuleData level edge)).V //
      vertex ≠ system.plantPlus (XiCol system.toRuleData level edge) ∧
      vertex ≠ system.plantMinus (XiCol system.toRuleData level edge)})
    (endpoint : (system.rule (XiCol system.toRuleData level otherEdge)).V) :
    embedRuleVtx system level otherEdge tail head endpoint ≠ Sum.inr ⟨edge, privateVertex⟩ := by
  intro equality
  unfold embedRuleVtx at equality
  split_ifs at equality with plus minus
  exact different (congrArg Sigma.fst (Sum.inr.inj equality))

theorem outDeg_private (system : EIGSData K) (level : ℕ)
    (edge : XiEdge system.toRuleData level)
    (privateVertex : {vertex : (system.rule (XiCol system.toRuleData level edge)).V //
      vertex ≠ system.plantPlus (XiCol system.toRuleData level edge) ∧
      vertex ≠ system.plantMinus (XiCol system.toRuleData level edge)}) (colour : Fin K) :
    outDeg system (level + 1) (Sum.inr ⟨edge, privateVertex⟩) colour =
      ruleTailDeg system (XiCol system.toRuleData level edge) privateVertex.val colour := by
  unfold outDeg ruleTailDeg
  simp only [Finset.card_filter]
  change (∑ pair : Σ otherEdge : XiEdge system.toRuleData level,
      (system.rule (XiCol system.toRuleData level otherEdge)).E,
      if XiTail system (level + 1) pair = Sum.inr ⟨edge, privateVertex⟩ ∧
        XiCol system.toRuleData (level + 1) pair = colour then (1 : ℕ) else 0) = _
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single edge]
  · apply Finset.sum_congr rfl
    intro ruleEdge _
    simp only [XiTail_succ, embedRuleVtx_eq_private_iff, XiCol, XiLvl] <;> rfl
  · intro otherEdge _ different
    apply Finset.sum_eq_zero
    intro ruleEdge _
    have nonincident := embedRuleVtx_ne_private_of_edge_ne system level edge otherEdge
      different (XiTail system level otherEdge) (XiHead system level otherEdge)
      privateVertex ((system.rule (XiCol system.toRuleData level otherEdge)).tail ruleEdge)
    simp only [XiTail_succ, nonincident, false_and, ite_false]
  · simp

theorem inDeg_private (system : EIGSData K) (level : ℕ)
    (edge : XiEdge system.toRuleData level)
    (privateVertex : {vertex : (system.rule (XiCol system.toRuleData level edge)).V //
      vertex ≠ system.plantPlus (XiCol system.toRuleData level edge) ∧
      vertex ≠ system.plantMinus (XiCol system.toRuleData level edge)}) (colour : Fin K) :
    inDeg system (level + 1) (Sum.inr ⟨edge, privateVertex⟩) colour =
      ruleHeadDeg system (XiCol system.toRuleData level edge) privateVertex.val colour := by
  unfold inDeg ruleHeadDeg
  simp only [Finset.card_filter]
  change (∑ pair : Σ otherEdge : XiEdge system.toRuleData level,
      (system.rule (XiCol system.toRuleData level otherEdge)).E,
      if XiHead system (level + 1) pair = Sum.inr ⟨edge, privateVertex⟩ ∧
        XiCol system.toRuleData (level + 1) pair = colour then (1 : ℕ) else 0) = _
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single edge]
  · apply Finset.sum_congr rfl
    intro ruleEdge _
    simp only [XiHead_succ, embedRuleVtx_eq_private_iff, XiCol, XiLvl] <;> rfl
  · intro otherEdge _ different
    apply Finset.sum_eq_zero
    intro ruleEdge _
    have nonincident := embedRuleVtx_ne_private_of_edge_ne system level edge otherEdge
      different (XiTail system level otherEdge) (XiHead system level otherEdge)
      privateVertex ((system.rule (XiCol system.toRuleData level otherEdge)).head ruleEdge)
    simp only [XiHead_succ, nonincident, false_and, ite_false]
  · simp

end
end EIGS

#print axioms EIGS.outDeg_private
#print axioms EIGS.inDeg_private
