import RequestProject.Section31.EIGSHarmonicCellL2Bound

/-! Every endpoint of an actual ancestor edge remains incident to an edge in
that same descendant fibre at every depth. -/

namespace EIGS

variable {K : ℕ}

private theorem rule_vertex_incidence (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (colour : Fin K) (vertex : (system.rule colour).V) :
    ∃ edge : (system.rule colour).E,
      (system.rule colour).tail edge = vertex ∨ (system.rule colour).head edge = vertex := by
  letI : Nontrivial (system.rule colour).V :=
    ⟨⟨system.plantPlus colour, system.plantMinus colour, system.plant_ne colour⟩⟩
  obtain ⟨neighbor, adjacency⟩ := (rulesConnected colour).preconnected.exists_adj_of_nontrivial vertex
  rcases adjacency with ⟨_, ⟨edge, tailEquality, _⟩ | ⟨edge, _, headEquality⟩⟩
  · exact ⟨edge, Or.inl tailEquality⟩
  · exact ⟨edge, Or.inr headEquality⟩

theorem exists_xiDescendant_incident_edge (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (initialLevel offset : ℕ) (ancestor : XiEdge system.toRuleData initialLevel)
    (vertex : XiVtx system initialLevel)
    (incidence : XiTail system initialLevel ancestor = vertex ∨ XiHead system initialLevel ancestor = vertex) :
    ∃ edge : XiEdge system.toRuleData (initialLevel + offset),
      xiEdgeAncestor system initialLevel offset edge = ancestor ∧
      (XiTail system (initialLevel + offset) edge = xiForward system initialLevel offset vertex ∨
        XiHead system (initialLevel + offset) edge = xiForward system initialLevel offset vertex) := by
  induction offset with
  | zero => exact ⟨ancestor, rfl, incidence⟩
  | succ offset induction =>
      obtain ⟨parent, ancestorEquality, parentIncidence⟩ := induction
      rcases parentIncidence with parentTail | parentHead
      · obtain ⟨child, childIncidence⟩ := rule_vertex_incidence system rulesConnected
          (XiCol system.toRuleData (initialLevel + offset) parent)
          (system.plantPlus (XiCol system.toRuleData (initialLevel + offset) parent))
        refine ⟨⟨parent, child⟩, ancestorEquality, ?_⟩
        rcases childIncidence with childTail | childHead
        · left
          change (XiNetwork system (initialLevel + offset)).substEmbed (system.ruleFamily rulesConnected) parent
            ((system.rule (XiCol system.toRuleData (initialLevel + offset) parent)).tail child) =
              Sum.inl (xiForward system initialLevel offset vertex)
          rw [childTail]
          change (XiNetwork system (initialLevel + offset)).substEmbed (system.ruleFamily rulesConnected) parent
            ((system.ruleFamily rulesConnected).βplus ((XiNetwork system (initialLevel + offset)).color parent)) = _
          rw [Network.substEmbed_plantPlus]
          exact congrArg Sum.inl parentTail
        · right
          change (XiNetwork system (initialLevel + offset)).substEmbed (system.ruleFamily rulesConnected) parent
            ((system.rule (XiCol system.toRuleData (initialLevel + offset) parent)).head child) =
              Sum.inl (xiForward system initialLevel offset vertex)
          rw [childHead]
          change (XiNetwork system (initialLevel + offset)).substEmbed (system.ruleFamily rulesConnected) parent
            ((system.ruleFamily rulesConnected).βplus ((XiNetwork system (initialLevel + offset)).color parent)) = _
          rw [Network.substEmbed_plantPlus]
          exact congrArg Sum.inl parentTail
      · obtain ⟨child, childIncidence⟩ := rule_vertex_incidence system rulesConnected
          (XiCol system.toRuleData (initialLevel + offset) parent)
          (system.plantMinus (XiCol system.toRuleData (initialLevel + offset) parent))
        refine ⟨⟨parent, child⟩, ancestorEquality, ?_⟩
        rcases childIncidence with childTail | childHead
        · left
          change (XiNetwork system (initialLevel + offset)).substEmbed (system.ruleFamily rulesConnected) parent
            ((system.rule (XiCol system.toRuleData (initialLevel + offset) parent)).tail child) =
              Sum.inl (xiForward system initialLevel offset vertex)
          rw [childTail]
          change (XiNetwork system (initialLevel + offset)).substEmbed (system.ruleFamily rulesConnected) parent
            ((system.ruleFamily rulesConnected).βminus ((XiNetwork system (initialLevel + offset)).color parent)) = _
          rw [Network.substEmbed_plantMinus]
          exact congrArg Sum.inl parentHead
        · right
          change (XiNetwork system (initialLevel + offset)).substEmbed (system.ruleFamily rulesConnected) parent
            ((system.rule (XiCol system.toRuleData (initialLevel + offset) parent)).head child) =
              Sum.inl (xiForward system initialLevel offset vertex)
          rw [childHead]
          change (XiNetwork system (initialLevel + offset)).substEmbed (system.ruleFamily rulesConnected) parent
            ((system.ruleFamily rulesConnected).βminus ((XiNetwork system (initialLevel + offset)).color parent)) = _
          rw [Network.substEmbed_plantMinus]
          exact congrArg Sum.inl parentHead

end EIGS
