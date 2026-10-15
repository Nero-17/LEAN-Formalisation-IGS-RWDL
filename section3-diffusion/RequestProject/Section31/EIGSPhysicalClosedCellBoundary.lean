import RequestProject.Section31.EIGSPhysicalClosedCellImage
import RequestProject.Section31.EIGSDescendantCellBoundary
import RequestProject.Section31.EIGSAddressCellMetricSeparation

/-! Coincident address limits in distinct coarse cells lie at an actual
coarse terminal. Finite nonincident cells have a positive separation. At
every finer scale, a common endpoint therefore exists; its unique ancestor
classification puts it at a forwarded coarse terminal. The mesh tends to
zero, so no new intersection is created on passing to the completion. -/

namespace EIGS
open Filter Topology
noncomputable section
variable {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)

theorem xiAddress_same_limit_distinct_coarse_boundary (coarse : ℕ)
    (first second : XiEdgeAddress system)
    (distinct : xiAddressEdge system coarse first ≠ xiAddressEdge system coarse second)
    (same : xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair first =
      xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair second) :
    xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair first =
        xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair coarse
          (XiTail system coarse (xiAddressEdge system coarse first)) ∨
    xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair first =
        xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair coarse
          (XiHead system coarse (xiAddressEdge system coarse first)) := by
  obtain ⟨lowerLength, lowerPositive, lowerBound⟩ :=
    exists_positive_colour_length_lower_bound system lengths lengthsPositive
  have common (offset : ℕ) : ∃ vertex : XiVtx system (coarse + offset),
      (XiTail system (coarse + offset) (xiAddressEdge system (coarse + offset) first) = vertex ∨
        XiHead system (coarse + offset) (xiAddressEdge system (coarse + offset) first) = vertex) ∧
      (XiTail system (coarse + offset) (xiAddressEdge system (coarse + offset) second) = vertex ∨
        XiHead system (coarse + offset) (xiAddressEdge system (coarse + offset) second) = vertex) := by
    by_cases tailIncident :
        XiTail system (coarse + offset) (xiAddressEdge system (coarse + offset) second) =
          XiTail system (coarse + offset) (xiAddressEdge system (coarse + offset) first) ∨
        XiHead system (coarse + offset) (xiAddressEdge system (coarse + offset) second) =
          XiTail system (coarse + offset) (xiAddressEdge system (coarse + offset) first)
    · exact ⟨_, Or.inl rfl, tailIncident⟩
    · by_cases headIncident :
          XiTail system (coarse + offset) (xiAddressEdge system (coarse + offset) second) =
            XiHead system (coarse + offset) (xiAddressEdge system (coarse + offset) first) ∨
          XiHead system (coarse + offset) (xiAddressEdge system (coarse + offset) second) =
            XiHead system (coarse + offset) (xiAddressEdge system (coarse + offset) first)
      · exact ⟨_, Or.inr rfl, headIncident⟩
      · have separation := xiAddressLimits_separated_of_nonincident_cells system connected lengths
          lengthsPositive rate rateGreaterThanOne eigenpair lowerLength lowerPositive lowerBound
          (coarse + offset) first second tailIncident headIncident
        rw [same, dist_self] at separation
        exact (not_le_of_gt (mul_pos lowerPositive
          (pow_pos (inv_pos.mpr (zero_lt_one.trans rateGreaterThanOne)) _)) separation).elim
  have nearBoundary (offset : ℕ) :
      dist (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair first)
        (xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair coarse
          (XiTail system coarse (xiAddressEdge system coarse first))) ≤
        (xiMaximumColourLength system lengths +
          (xiRuleRadius system lengths * rate⁻¹) / (1 - rate⁻¹)) * rate⁻¹ ^ (coarse + offset) ∨
      dist (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair first)
        (xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair coarse
          (XiHead system coarse (xiAddressEdge system coarse first))) ≤
        (xiMaximumColourLength system lengths +
          (xiRuleRadius system lengths * rate⁻¹) / (1 - rate⁻¹)) * rate⁻¹ ^ (coarse + offset) := by
    obtain ⟨vertex, firstIncident, secondIncident⟩ := common offset
    have boundary := (xiDistinctCoarseCells_common_endpoint_is_boundary system coarse offset
      (xiAddressEdge system (coarse + offset) first) (xiAddressEdge system (coarse + offset) second)
      (by simpa only [xiEdgeAncestor_address] using distinct) vertex firstIncident secondIncident).1
    have supported : xiAddressStarWeight system (coarse + offset) vertex first ≠ 0 := by
      rcases firstIncident with tail | head
      · simp only [xiAddressStarWeight, xiEdgeStarMultiplicity, tail, if_true]
        split_ifs <;> norm_num
      · simp only [xiAddressStarWeight, xiEdgeStarMultiplicity, head, if_true]
        split_ifs <;> norm_num
    have bound := xiAddressStarWeight_support_mesh system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair (coarse + offset) vertex first supported
    rcases boundary with tail | head
    · left
      rw [tail] at bound
      simpa only [xiCompletionEmbedding, Function.comp_apply, xiVertexEmbedding_forward,
        xiEdgeAncestor_address] using bound
    · right
      rw [head] at bound
      simpa only [xiCompletionEmbedding, Function.comp_apply, xiVertexEmbedding_forward,
        xiEdgeAncestor_address] using bound
  have meshLimit : Tendsto (fun offset : ℕ =>
      (xiMaximumColourLength system lengths +
        (xiRuleRadius system lengths * rate⁻¹) / (1 - rate⁻¹)) * rate⁻¹ ^ (coarse + offset)) atTop (𝓝 0) := by
    have shifted : Tendsto (fun offset : ℕ => coarse + offset) atTop atTop := by
      simpa only [Nat.add_comm] using tendsto_add_atTop_nat coarse
    simpa only [mul_zero] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one
        (inv_nonneg.mpr (zero_lt_one.trans rateGreaterThanOne).le)
        (inv_lt_one_of_one_lt₀ rateGreaterThanOne)).comp shifted).const_mul
          (xiMaximumColourLength system lengths + (xiRuleRadius system lengths * rate⁻¹) / (1 - rate⁻¹))
  by_contra neither
  push_neg at neither
  have tailPositive := dist_pos.mpr neither.1
  have headPositive := dist_pos.mpr neither.2
  obtain ⟨offset, small⟩ := (meshLimit.eventually (gt_mem_nhds (lt_min tailPositive headPositive))).exists
  rcases nearBoundary offset with tail | head
  · exact (not_lt_of_ge tail) (small.trans_le (min_le_left _ _))
  · exact (not_lt_of_ge head) (small.trans_le (min_le_right _ _))

theorem xiPhysicalClosedCell_preimage_subset_cylinder_union_boundary (mass : XiMassParameters system)
    (coarse : ℕ) (ancestor : XiEdge system.toRuleData coarse) :
    (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair) ⁻¹'
        xiPhysicalClosedCell system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair coarse ancestor ⊆
      {address | xiAddressEdge system coarse address = ancestor} ∪
        (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair) ⁻¹'
          {xiCompletionEmbedding system connected lengths lengthsPositive rate
              (zero_lt_one.trans rateGreaterThanOne) eigenpair coarse (XiTail system coarse ancestor),
            xiCompletionEmbedding system connected lengths lengthsPositive rate
              (zero_lt_one.trans rateGreaterThanOne) eigenpair coarse (XiHead system coarse ancestor)} := by
  intro address membership
  by_cases through : xiAddressEdge system coarse address = ancestor
  · exact Or.inl through
  · right
    rw [xiPhysicalClosedCell_eq_addressCylinderImage system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass coarse ancestor] at membership
    obtain ⟨other, otherThrough, same⟩ := membership
    have boundary := xiAddress_same_limit_distinct_coarse_boundary system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair coarse other address
      (by rw [otherThrough]; exact Ne.symm through) same
    rw [otherThrough, same] at boundary
    simpa only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] using boundary

end
end EIGS

#print axioms EIGS.xiAddress_same_limit_distinct_coarse_boundary
#print axioms EIGS.xiPhysicalClosedCell_preimage_subset_cylinder_union_boundary
