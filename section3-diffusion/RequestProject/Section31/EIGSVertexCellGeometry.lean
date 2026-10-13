import RequestProject.Section31.EIGSVertexDescendants
import RequestProject.Section31.EIGSSpeedWeakLimit

/-! Actual private-vertex cell geometry in the constructed completion. -/

namespace EIGS

open scoped BigOperators Classical

variable {K : ℕ}

theorem ruleVertex_has_incident_edge (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (colour : Fin K) (vertex : (system.rule colour).V) :
    ∃ edge : (system.rule colour).E,
      (system.rule colour).tail edge = vertex ∨ (system.rule colour).head edge = vertex := by
  letI : Nontrivial (system.rule colour).V :=
    ⟨⟨system.plantPlus colour, system.plantMinus colour, system.plant_ne colour⟩⟩
  obtain ⟨neighbor, adjacency⟩ := (ruleConnected colour).preconnected.exists_adj_of_nontrivial vertex
  change vertex ≠ neighbor ∧
    ((∃ edge, (system.rule colour).tail edge = vertex ∧ (system.rule colour).head edge = neighbor) ∨
      (∃ edge, (system.rule colour).tail edge = neighbor ∧ (system.rule colour).head edge = vertex)) at adjacency
  rcases adjacency.2 with ⟨edge, tailEquality, _⟩ | ⟨edge, _, headEquality⟩
  · exact ⟨edge, Or.inl tailEquality⟩
  · exact ⟨edge, Or.inr headEquality⟩

variable (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily ruleConnected).metricLengths lengths = rate • lengths)

theorem xiPrivateVertex_to_ancestorTail (mass : XiMassParameters system) (coarseLevel offset : ℕ)
    (ancestor : XiEdge system.toRuleData coarseLevel)
    (vertex : XiVtx system (coarseLevel + offset))
    (membership : xiVertexAncestorEdge system coarseLevel offset vertex = some ancestor) :
    dist (xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair (coarseLevel + offset) vertex)
      (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair
        coarseLevel ancestor) ≤
      rate⁻¹ ^ coarseLevel * (∑ colour, lengths colour) +
        2 * ((xiRuleRadius system lengths * rate⁻¹) * rate⁻¹ ^ coarseLevel / (1 - rate⁻¹)) := by
  induction offset with
  | zero => simp [xiVertexAncestorEdge] at membership
  | succ offset inductionHypothesis =>
    rcases vertex with oldVertex | ⟨parent, interior⟩
    · have oldMembership : xiVertexAncestorEdge system coarseLevel offset oldVertex = some ancestor := membership
      simpa only [xiCompletionEmbedding, Function.comp_apply, xiVertexEmbedding_old] using
        inductionHypothesis oldVertex oldMembership
    · obtain ⟨ruleEdge, incidence⟩ := ruleVertex_has_incident_edge system ruleConnected
        (XiCol system.toRuleData (coarseLevel + offset) parent) interior.val
      let fineEdge : XiEdge system.toRuleData (coarseLevel + (offset + 1)) := ⟨parent, ruleEdge⟩
      have ancestorEquality : xiEdgeAncestor system coarseLevel (offset + 1) fineEdge = ancestor :=
        Option.some.inj membership
      have endpointEquality :
          XiTail system (coarseLevel + (offset + 1)) fineEdge = Sum.inr ⟨parent, interior⟩ ∨
          XiHead system (coarseLevel + (offset + 1)) fineEdge = Sum.inr ⟨parent, interior⟩ := by
        rcases incidence with tailEquality | headEquality
        · left
          simp only [Nat.add_succ, fineEdge, XiTail_succ, tailEquality]
          exact embedRuleVtx_interior system (coarseLevel + offset) parent
            (XiTail system (coarseLevel + offset) parent) (XiHead system (coarseLevel + offset) parent)
            interior.property.1 interior.property.2
        · right
          simp only [Nat.add_succ, fineEdge, XiHead_succ, headEquality]
          exact embedRuleVtx_interior system (coarseLevel + offset) parent
            (XiTail system (coarseLevel + offset) parent) (XiHead system (coarseLevel + offset) parent)
            interior.property.1 interior.property.2
      have inverseNonnegative : 0 ≤ rate⁻¹ := inv_nonneg.mpr (zero_le_one.trans rateGreaterThanOne.le)
      have inverseLessThanOne : rate⁻¹ < 1 :=
        (inv_lt_one₀ (zero_lt_one.trans rateGreaterThanOne)).mpr rateGreaterThanOne
      have lengthSumNonnegative : 0 ≤ ∑ colour, lengths colour :=
        Finset.sum_nonneg (fun colour _ => (lengthsPositive colour).le)
      have colourBound : lengths (XiCol system.toRuleData (coarseLevel + (offset + 1)) fineEdge) ≤
          ∑ colour, lengths colour :=
        Finset.single_le_sum (fun colour _ => (lengthsPositive colour).le) (Finset.mem_univ _)
      have powerBound : rate⁻¹ ^ (coarseLevel + (offset + 1)) ≤ rate⁻¹ ^ coarseLevel := by
        rw [pow_add]
        exact mul_le_of_le_one_right (pow_nonneg inverseNonnegative _)
          (pow_le_one₀ inverseNonnegative inverseLessThanOne.le)
      have endpointBound :
          dist (xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
            (zero_lt_one.trans rateGreaterThanOne) eigenpair (coarseLevel + (offset + 1))
              (Sum.inr ⟨parent, interior⟩))
            (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair
              (coarseLevel + (offset + 1)) fineEdge) ≤
            rate⁻¹ ^ coarseLevel * (∑ colour, lengths colour) := by
        rcases endpointEquality with tailEquality | headEquality
        · rw [← tailEquality]
          simpa only [xiEdgeTailPoint, dist_self] using
            mul_nonneg (pow_nonneg inverseNonnegative _) lengthSumNonnegative
        · rw [← headEquality]
          change dist (xiEdgeHeadPoint system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair _ _)
            (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair _ _) ≤ _
          rw [dist_comm]
          exact (xiCompletionEdge_distance_le system ruleConnected lengths lengthsPositive rate
            rateGreaterThanOne eigenpair _ fineEdge).trans
              ((mul_le_mul_of_nonneg_left colourBound (pow_nonneg inverseNonnegative _)).trans
                (mul_le_mul_of_nonneg_right powerBound lengthSumNonnegative))
      have ancestorBound := xiFineTail_to_ancestorTail system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass coarseLevel (offset + 1) fineEdge
      rw [ancestorEquality] at ancestorBound
      have errorBound := xiAddressError_add_le system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair coarseLevel (offset + 1)
      have triangle := dist_triangle
        (xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair (coarseLevel + (offset + 1))
            (Sum.inr ⟨parent, interior⟩))
        (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair
          (coarseLevel + (offset + 1)) fineEdge)
        (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair
          coarseLevel ancestor)
      linarith

end EIGS

#print axioms EIGS.ruleVertex_has_incident_edge
#print axioms EIGS.xiPrivateVertex_to_ancestorTail
