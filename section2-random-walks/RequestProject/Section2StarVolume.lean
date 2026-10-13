import RequestProject.Section2StarCounts
import RequestProject.Section2VertexGrowth

/-! Finite actual descendant-star volume bounds. The birth sums telescope
to the vertex counts of the original rules replanted at each coarse edge. -/

namespace EIGS

open scoped BigOperators Classical

variable {K : ℕ}

noncomputable def xiInteriorBirthCount (system : EIGSData K) (colour : Fin K) (steps : ℕ) : ℕ :=
  ∑ birth ∈ Finset.range steps,
    ∑ edge : XiEdge {system.toRuleData with ι := colour} birth,
      xiRuleInteriorCount system (XiCol {system.toRuleData with ι := colour} birth edge)

theorem xiInteriorBirthCount_succ (system : EIGSData K) (colour : Fin K) (steps : ℕ) :
    xiInteriorBirthCount system colour (steps + 1) = xiInteriorBirthCount system colour steps +
      ∑ edge : XiEdge {system.toRuleData with ι := colour} steps,
        xiRuleInteriorCount system (XiCol {system.toRuleData with ι := colour} steps edge) := by
  exact Finset.sum_range_succ _ _

theorem xiVtx_card_eq_two_add_interior_births (system : EIGSData K) (steps : ℕ) :
    Fintype.card (XiVtx system steps) = 2 + xiInteriorBirthCount system system.initCol steps := by
  induction steps with
  | zero => simp [XiVtx, xiInteriorBirthCount]
  | succ steps induction_hypothesis =>
    have cardinal_succ : Fintype.card (XiVtx system (steps + 1)) =
        Fintype.card (XiVtx system steps) +
          ∑ edge : XiEdge system.toRuleData steps,
            xiRuleInteriorCount system (XiCol system.toRuleData steps edge) := by
      change Fintype.card (XiVtx system steps ⊕
        (Σ edge : XiEdge system.toRuleData steps,
          {vertex : (system.rule (XiCol system.toRuleData steps edge)).V //
            vertex ≠ system.plantPlus (XiCol system.toRuleData steps edge) ∧
            vertex ≠ system.plantMinus (XiCol system.toRuleData steps edge)})) = _
      rw [Fintype.card_sum, Fintype.card_sigma]
      rfl
    rw [cardinal_succ, induction_hypothesis, xiInteriorBirthCount_succ]
    exact Nat.add_assoc _ _ _

theorem xiIncidentStar_card_le_interior_births (system : EIGSData K) (coarse steps : ℕ)
    (center : XiVtx system coarse) :
    (Finset.univ.filter (xiIncidentStar system coarse center steps)).card ≤
      1 + ∑ edge : XiEdge system.toRuleData coarse,
        if XiTail system coarse edge = center ∨ XiHead system coarse edge = center then
          xiInteriorBirthCount system (XiCol system.toRuleData coarse edge) steps else 0 := by
  induction steps with
  | zero =>
    have singleton : Finset.univ.filter (xiIncidentStar system coarse center 0) = {center} := by
      ext vertex
      simp [xiIncidentStar]
    rw [singleton]
    simp [xiInteriorBirthCount]
  | succ steps induction_hypothesis =>
    calc
      _ ≤ (Finset.univ.filter (xiIncidentStar system coarse center steps)).card +
          ∑ edge : XiEdge system.toRuleData coarse,
            if XiTail system coarse edge = center ∨ XiHead system coarse edge = center then
              ∑ descendant : XiEdge
                {system.toRuleData with ι := XiCol system.toRuleData coarse edge} steps,
                xiRuleInteriorCount system
                  (XiCol {system.toRuleData with ι := XiCol system.toRuleData coarse edge}
                    steps descendant)
            else 0 := xiIncidentStar_card_succ_le_descendants system coarse steps center
      _ ≤ (1 + ∑ edge : XiEdge system.toRuleData coarse,
          if XiTail system coarse edge = center ∨ XiHead system coarse edge = center then
            xiInteriorBirthCount system (XiCol system.toRuleData coarse edge) steps else 0) +
          ∑ edge : XiEdge system.toRuleData coarse,
            if XiTail system coarse edge = center ∨ XiHead system coarse edge = center then
              ∑ descendant : XiEdge
                {system.toRuleData with ι := XiCol system.toRuleData coarse edge} steps,
                xiRuleInteriorCount system
                  (XiCol {system.toRuleData with ι := XiCol system.toRuleData coarse edge}
                    steps descendant)
            else 0 := Nat.add_le_add_right induction_hypothesis _
      _ = _ := by
        simp_rw [xiInteriorBirthCount_succ]
        rw [Nat.add_assoc, ← Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro edge _
        by_cases incident : XiTail system coarse edge = center ∨ XiHead system coarse edge = center
        <;> simp [incident]

theorem xiIncidentStar_card_le_replanted_vertices (system : EIGSData K) (coarse steps : ℕ)
    (center : XiVtx system coarse) :
    (Finset.univ.filter (xiIncidentStar system coarse center steps)).card ≤
      1 + ∑ edge : XiEdge system.toRuleData coarse,
        if XiTail system coarse edge = center ∨ XiHead system coarse edge = center then
          Fintype.card (XiVtx {system with initCol := XiCol system.toRuleData coarse edge} steps)
        else 0 := by
  apply (xiIncidentStar_card_le_interior_births system coarse steps center).trans
  apply Nat.add_le_add_left
  apply Finset.sum_le_sum
  intro edge _
  by_cases incident : XiTail system coarse edge = center ∨ XiHead system coarse edge = center
  · simp only [incident, ↓reduceIte]
    rw [xiVtx_card_eq_two_add_interior_births]
    exact Nat.le_add_left _ _
  · simp only [incident, ↓reduceIte, le_refl]

end EIGS

#print axioms EIGS.xiInteriorBirthCount_succ
#print axioms EIGS.xiVtx_card_eq_two_add_interior_births
#print axioms EIGS.xiIncidentStar_card_le_interior_births
#print axioms EIGS.xiIncidentStar_card_le_replanted_vertices
