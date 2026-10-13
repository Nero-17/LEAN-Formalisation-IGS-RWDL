import RequestProject.Section2MultiStepBall
import RequestProject.Section31.EIGSEdgeDescendants

/-! Actual multi-step stars are supported on descendants of coarse edges
incident to their original center. The counting uses the actual ancestor map. -/

namespace EIGS

open scoped BigOperators Classical

variable {K : ℕ}

theorem xiIncidentStar_embedRuleVtx_imp (system : EIGSData K) (coarse steps : ℕ)
    (center : XiVtx system coarse) (edge : XiEdge system.toRuleData (coarse + steps))
    (vertex : (system.rule (XiCol system.toRuleData (coarse + steps) edge)).V)
    (membership : xiIncidentStar system coarse center (steps + 1)
      (embedRuleVtx system (coarse + steps) edge
        (XiTail system (coarse + steps) edge) (XiHead system (coarse + steps) edge) vertex)) :
    xiIncidentStar system coarse center steps (XiTail system (coarse + steps) edge) ∨
      xiIncidentStar system coarse center steps (XiHead system (coarse + steps) edge) := by
  by_cases plus_eq : vertex = system.plantPlus (XiCol system.toRuleData (coarse + steps) edge)
  · subst vertex
    rw [embedRuleVtx_plantPlus] at membership
    exact Or.inl membership
  · by_cases minus_eq : vertex = system.plantMinus (XiCol system.toRuleData (coarse + steps) edge)
    · subst vertex
      rw [embedRuleVtx_plantMinus] at membership
      exact Or.inr membership
    · simpa only [embedRuleVtx, plus_eq, minus_eq, ↓reduceDIte, xiIncidentStar] using membership

theorem xiIncidentStar_endpoint_has_incident_ancestor (system : EIGSData K)
    (coarse steps : ℕ) (center : XiVtx system coarse)
    (edge : XiEdge system.toRuleData (coarse + steps))
    (incident : xiIncidentStar system coarse center steps (XiTail system (coarse + steps) edge) ∨
      xiIncidentStar system coarse center steps (XiHead system (coarse + steps) edge)) :
    XiTail system coarse (xiEdgeAncestor system coarse steps edge) = center ∨
      XiHead system coarse (xiEdgeAncestor system coarse steps edge) = center := by
  induction steps with
  | zero => exact incident
  | succ steps induction_hypothesis =>
    apply induction_hypothesis edge.1
    rcases incident with tail_incident | head_incident
    · change xiIncidentStar system coarse center (steps + 1)
        (XiTail system ((coarse + steps) + 1) edge) at tail_incident
      rw [XiTail_succ] at tail_incident
      exact xiIncidentStar_embedRuleVtx_imp system coarse steps center edge.1 _ tail_incident
    · change xiIncidentStar system coarse center (steps + 1)
        (XiHead system ((coarse + steps) + 1) edge) at head_incident
      rw [XiHead_succ] at head_incident
      exact xiIncidentStar_embedRuleVtx_imp system coarse steps center edge.1 _ head_incident

noncomputable def xiRuleInteriorCount (system : EIGSData K) (colour : Fin K) : ℕ :=
  Fintype.card {vertex : (system.rule colour).V //
    vertex ≠ system.plantPlus colour ∧ vertex ≠ system.plantMinus colour}

theorem xiIncidentStar_card_succ (system : EIGSData K) (coarse steps : ℕ)
    (center : XiVtx system coarse) :
    (Finset.univ.filter (xiIncidentStar system coarse center (steps + 1))).card =
      (Finset.univ.filter (xiIncidentStar system coarse center steps)).card +
        ∑ edge : XiEdge system.toRuleData (coarse + steps),
          if xiIncidentStar system coarse center steps (XiTail system (coarse + steps) edge) ∨
            xiIncidentStar system coarse center steps (XiHead system (coarse + steps) edge)
          then xiRuleInteriorCount system (XiCol system.toRuleData (coarse + steps) edge) else 0 := by
  classical
  simp only [Finset.card_filter]
  change (∑ vertex : XiVtx system (coarse + steps) ⊕
    (Σ edge : XiEdge system.toRuleData (coarse + steps),
      {vertex : (system.rule (XiCol system.toRuleData (coarse + steps) edge)).V //
        vertex ≠ system.plantPlus (XiCol system.toRuleData (coarse + steps) edge) ∧
        vertex ≠ system.plantMinus (XiCol system.toRuleData (coarse + steps) edge)}),
    if xiIncidentStar system coarse center (steps + 1) vertex then (1 : ℕ) else 0) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  apply congrArg₂ Nat.add
  · rfl
  · apply Finset.sum_congr rfl
    intro edge _
    by_cases incident :
        xiIncidentStar system coarse center steps (XiTail system (coarse + steps) edge) ∨
        xiIncidentStar system coarse center steps (XiHead system (coarse + steps) edge)
    <;> simp [xiIncidentStar, incident, xiRuleInteriorCount]

theorem xiIncidentStar_card_succ_le_descendants (system : EIGSData K) (coarse steps : ℕ)
    (center : XiVtx system coarse) :
    (Finset.univ.filter (xiIncidentStar system coarse center (steps + 1))).card ≤
      (Finset.univ.filter (xiIncidentStar system coarse center steps)).card +
        ∑ edge : XiEdge system.toRuleData coarse,
          if XiTail system coarse edge = center ∨ XiHead system coarse edge = center then
            ∑ descendant : XiEdge {system.toRuleData with ι := XiCol system.toRuleData coarse edge} steps,
              xiRuleInteriorCount system
                (XiCol {system.toRuleData with ι := XiCol system.toRuleData coarse edge} steps descendant)
          else 0 := by
  rw [xiIncidentStar_card_succ]
  apply Nat.add_le_add_left
  have fine_bound :
      (∑ edge : XiEdge system.toRuleData (coarse + steps),
        if xiIncidentStar system coarse center steps (XiTail system (coarse + steps) edge) ∨
          xiIncidentStar system coarse center steps (XiHead system (coarse + steps) edge) then
          xiRuleInteriorCount system (XiCol system.toRuleData (coarse + steps) edge) else 0) ≤
      ∑ edge : XiEdge system.toRuleData (coarse + steps),
        if XiTail system coarse (xiEdgeAncestor system coarse steps edge) = center ∨
          XiHead system coarse (xiEdgeAncestor system coarse steps edge) = center then
          xiRuleInteriorCount system (XiCol system.toRuleData (coarse + steps) edge) else 0 := by
    apply Finset.sum_le_sum
    intro edge _
    by_cases incident :
        xiIncidentStar system coarse center steps (XiTail system (coarse + steps) edge) ∨
        xiIncidentStar system coarse center steps (XiHead system (coarse + steps) edge)
    · simp only [incident, xiIncidentStar_endpoint_has_incident_ancestor system coarse steps center
        edge incident, ↓reduceIte, le_refl]
    · simp only [incident, ↓reduceIte]
      split <;> exact Nat.zero_le _
  refine fine_bound.trans_eq ?_
  calc
    _ = ∑ edge : XiEdge system.toRuleData (coarse + steps),
        ∑ ancestor : XiEdge system.toRuleData coarse,
          if xiEdgeAncestor system coarse steps edge = ancestor then
            if XiTail system coarse ancestor = center ∨ XiHead system coarse ancestor = center then
              xiRuleInteriorCount system (XiCol system.toRuleData (coarse + steps) edge) else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro edge _
      simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ancestor _
      by_cases incident : XiTail system coarse ancestor = center ∨ XiHead system coarse ancestor = center
      · simp only [incident, ↓reduceIte]
        exact xiDescendant_weight_sum system coarse steps ancestor (xiRuleInteriorCount system)
      · simp only [incident, ↓reduceIte, ite_self, Finset.sum_const_zero]

end EIGS

#print axioms EIGS.xiIncidentStar_embedRuleVtx_imp
#print axioms EIGS.xiIncidentStar_endpoint_has_incident_ancestor
#print axioms EIGS.xiIncidentStar_card_succ
#print axioms EIGS.xiIncidentStar_card_succ_le_descendants
