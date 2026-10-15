import RequestProject.Section31.EIGSPhysicalClosedCell
import RequestProject.Section31.EIGSAddressCompactTopology
import RequestProject.Section31.EIGSAddressIncidentStar
import RequestProject.Section31.EIGSDescendantEndpointEdges

/-! The image of an actual address cylinder equals the closure of the actual
descendant vertices. Compactness proves that image is closed. To include a
finite endpoint, use genuine deeper descendant edges incident to that same
endpoint; their address limits approach it with the proved geometric mesh. -/

namespace EIGS
open Filter Topology
noncomputable section
variable {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)

theorem xiDescendantEndpoint_mem_addressCylinderImage (mass : XiMassParameters system)
    (coarse offset : ℕ) (ancestor : XiEdge system.toRuleData coarse)
    (edge : XiEdge system.toRuleData (coarse + offset))
    (ancestry : xiAncestorEdge system coarse offset edge = ancestor)
    (vertex : XiVtx system (coarse + offset))
    (incident : XiTail system (coarse + offset) edge = vertex ∨
      XiHead system (coarse + offset) edge = vertex) :
    xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair (coarse + offset) vertex ∈
        xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair ''
          {address | xiAddressEdge system coarse address = ancestor} := by
  have approximation (age : ℕ) : ∃ address : XiEdgeAddress system,
      xiAddressEdge system coarse address = ancestor ∧
      dist (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair address)
        (xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair (coarse + offset) vertex) ≤
        (xiMaximumColourLength system lengths +
          (xiRuleRadius system lengths * rate⁻¹) / (1 - rate⁻¹)) * rate⁻¹ ^ ((coarse + offset) + age) := by
    obtain ⟨descendant, descendantAncestry, descendantIncident⟩ :=
      exists_xiDescendant_incident_edge system connected (coarse + offset) age edge vertex incident
    obtain ⟨address, through⟩ := mass.exists_address_through_edge ((coarse + offset) + age) descendant
    have birthThrough : xiAddressEdge system (coarse + offset) address = edge := by
      have equality := xiEdgeAncestor_address system (coarse + offset) age address
      rw [through, descendantAncestry] at equality
      exact equality.symm
    have coarseThrough : xiAddressEdge system coarse address = ancestor := by
      have equality := xiAddressEdge_ancestor system coarse offset address
      rw [birthThrough, ancestry] at equality
      exact equality.symm
    have supported : xiAddressStarWeight system ((coarse + offset) + age)
        (xiForward system (coarse + offset) age vertex) address ≠ 0 := by
      rcases descendantIncident with tail | head
      · simp only [xiAddressStarWeight, xiEdgeStarMultiplicity, through, tail, if_true]
        split_ifs <;> norm_num
      · simp only [xiAddressStarWeight, xiEdgeStarMultiplicity, through, head, if_true]
        split_ifs <;> norm_num
    refine ⟨address, coarseThrough, ?_⟩
    have bound := xiAddressStarWeight_support_mesh system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair ((coarse + offset) + age)
      (xiForward system (coarse + offset) age vertex) address supported
    simpa only [xiCompletionEmbedding, Function.comp_apply, xiVertexEmbedding_forward] using bound
  choose addresses through close using approximation
  have meshLimit : Tendsto (fun age : ℕ =>
      (xiMaximumColourLength system lengths +
        (xiRuleRadius system lengths * rate⁻¹) / (1 - rate⁻¹)) * rate⁻¹ ^ ((coarse + offset) + age))
      atTop (𝓝 0) := by
    have shifted : Tendsto (fun age : ℕ => (coarse + offset) + age) atTop atTop := by
      simpa only [Nat.add_comm] using tendsto_add_atTop_nat (coarse + offset)
    simpa only [mul_zero] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one
        (inv_nonneg.mpr (zero_lt_one.trans rateGreaterThanOne).le)
        (inv_lt_one_of_one_lt₀ rateGreaterThanOne)).comp shifted).const_mul
          (xiMaximumColourLength system lengths + (xiRuleRadius system lengths * rate⁻¹) / (1 - rate⁻¹))
  have converges : Tendsto (fun age => xiAddressLimit system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair (addresses age)) atTop
      (𝓝 (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair (coarse + offset) vertex)) := by
    apply Metric.tendsto_atTop.mpr
    intro tolerance positive
    obtain ⟨threshold, small⟩ := eventually_atTop.mp (meshLimit.eventually (gt_mem_nhds positive))
    exact ⟨threshold, fun age large => (close age).trans_lt (small age large)⟩
  apply (xiAddressCylinder_image_isCompact system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair coarse ancestor).isClosed.mem_of_tendsto converges
  exact Filter.Eventually.of_forall (fun age => ⟨addresses age, through age, rfl⟩)

theorem xiPhysicalClosedCell_eq_addressCylinderImage (mass : XiMassParameters system)
    (coarse : ℕ) (ancestor : XiEdge system.toRuleData coarse) :
    xiPhysicalClosedCell system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair coarse ancestor =
      xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair ''
        {address | xiAddressEdge system coarse address = ancestor} := by
  apply Set.Subset.antisymm
  · apply closure_minimal _
      (xiAddressCylinder_image_isCompact system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair coarse ancestor).isClosed
    intro point membership
    obtain ⟨vertex, ⟨offset, edge, ancestry, endpoint⟩, rfl⟩ := membership
    rcases endpoint with tail | head
    · rw [← tail]
      exact xiDescendantEndpoint_mem_addressCylinderImage system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass coarse offset ancestor edge ancestry _ (Or.inl rfl)
    · rw [← head]
      exact xiDescendantEndpoint_mem_addressCylinderImage system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass coarse offset ancestor edge ancestry _ (Or.inr rfl)
  · rintro point ⟨address, through, rfl⟩
    exact xiAddressLimit_mem_physicalClosedCell system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair coarse ancestor address through

end
end EIGS

#print axioms EIGS.xiDescendantEndpoint_mem_addressCylinderImage
#print axioms EIGS.xiPhysicalClosedCell_eq_addressCylinderImage
