import RequestProject.Section2StarVolume
import RequestProject.Section31.EIGSEdgeMarginals
import RequestProject.Section31.EIGSSpeedWeakConvergence

/-! Actual private-vertex ancestry. Coarse skeleton vertices have no parent cell;
every vertex born later belongs to its unique actual coarse ancestor edge. -/

namespace EIGS

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal Classical

noncomputable section

variable {K : ℕ}

def xiVertexAncestorEdge (system : EIGSData K) (coarseLevel : ℕ) :
    (offset : ℕ) → XiVtx system (coarseLevel + offset) → Option (XiEdge system.toRuleData coarseLevel)
  | 0 => fun _ => none
  | offset + 1 => fun vertex => match vertex with
    | Sum.inl oldVertex => xiVertexAncestorEdge system coarseLevel offset oldVertex
    | Sum.inr interiorVertex => some (xiEdgeAncestor system coarseLevel offset interiorVertex.1)

theorem xiVertexAncestorEdge_fibre_card (system : EIGSData K) (coarseLevel offset : ℕ)
    (ancestor : XiEdge system.toRuleData coarseLevel) :
    Fintype.card {vertex : XiVtx system (coarseLevel + offset) //
      xiVertexAncestorEdge system coarseLevel offset vertex = some ancestor} =
        xiInteriorBirthCount system (XiCol system.toRuleData coarseLevel ancestor) offset := by
  induction offset with
  | zero => simp [xiVertexAncestorEdge, xiInteriorBirthCount]
  | succ offset inductionHypothesis =>
    rw [Fintype.card_subtype, Finset.card_filter]
    change (∑ vertex : (XiVtx system (coarseLevel + offset) ⊕
      (Σ edge : XiEdge system.toRuleData (coarseLevel + offset),
        {interior : (system.rule (XiCol system.toRuleData (coarseLevel + offset) edge)).V //
          interior ≠ system.plantPlus (XiCol system.toRuleData (coarseLevel + offset) edge) ∧
          interior ≠ system.plantMinus (XiCol system.toRuleData (coarseLevel + offset) edge)})),
        if xiVertexAncestorEdge system coarseLevel (offset + 1) vertex = some ancestor then 1 else 0) = _
    rw [Fintype.sum_sum_type, Fintype.sum_sigma]
    simp only [xiVertexAncestorEdge, Option.some.injEq]
    have oldCardinality :
        (∑ vertex : XiVtx system (coarseLevel + offset),
          if xiVertexAncestorEdge system coarseLevel offset vertex = some ancestor then 1 else 0) =
          xiInteriorBirthCount system (XiCol system.toRuleData coarseLevel ancestor) offset := by
      rw [← Finset.card_filter, ← Fintype.card_subtype]
      exact inductionHypothesis
    rw [oldCardinality]
    have interiorCardinality :
        (∑ edge : XiEdge system.toRuleData (coarseLevel + offset),
          ∑ interior : {interior : (system.rule (XiCol system.toRuleData (coarseLevel + offset) edge)).V //
            interior ≠ system.plantPlus (XiCol system.toRuleData (coarseLevel + offset) edge) ∧
            interior ≠ system.plantMinus (XiCol system.toRuleData (coarseLevel + offset) edge)},
            if xiEdgeAncestor system coarseLevel offset edge = ancestor then 1 else 0) =
        ∑ edge : XiEdge system.toRuleData (coarseLevel + offset),
          if xiEdgeAncestor system coarseLevel offset edge = ancestor then
            xiRuleInteriorCount system (XiCol system.toRuleData (coarseLevel + offset) edge) else 0 := by
      apply Finset.sum_congr rfl
      intro edge _
      by_cases sameAncestor : xiEdgeAncestor system coarseLevel offset edge = ancestor
      · simp only [sameAncestor, ↓reduceIte, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
        rfl
      · simp only [sameAncestor, ↓reduceIte, Finset.sum_const_zero]
    rw [interiorCardinality, xiDescendant_weight_sum, xiInteriorBirthCount_succ]

theorem xiVertexAncestorEdge_none_card (system : EIGSData K) (coarseLevel offset : ℕ) :
    Fintype.card {vertex : XiVtx system (coarseLevel + offset) //
      xiVertexAncestorEdge system coarseLevel offset vertex = none} = Fintype.card (XiVtx system coarseLevel) := by
  induction offset with
  | zero => simp [xiVertexAncestorEdge]
  | succ offset inductionHypothesis =>
    rw [Fintype.card_subtype, Finset.card_filter]
    change (∑ vertex : (XiVtx system (coarseLevel + offset) ⊕ _),
      if xiVertexAncestorEdge system coarseLevel (offset + 1) vertex = none then 1 else 0) = _
    rw [Fintype.sum_sum_type, Fintype.sum_sigma]
    simp only [xiVertexAncestorEdge, Option.some_ne_none, ↓reduceIte, Finset.sum_const_zero, add_zero]
    rw [← Finset.card_filter, ← Fintype.card_subtype]
    exact inductionHypothesis

end
end EIGS

#print axioms EIGS.xiVertexAncestorEdge_fibre_card
#print axioms EIGS.xiVertexAncestorEdge_none_card
