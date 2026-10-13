import RequestProject.Section31.EIGSAddressMeasure

/-! Uniform geometric controls for the actual finite endpoints and their
address limits, used in transferring finite ancestor laws to the completion. -/

namespace EIGS

open Filter Topology

variable {K : ℕ} (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily ruleConnected).metricLengths lengths = rate • lengths)

include ruleConnected lengthsPositive rateGreaterThanOne eigenpair

theorem xiCompletionEdge_distance_le (level : ℕ) (edge : XiEdge system.toRuleData level) :
    dist (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair level edge)
      (xiEdgeHeadPoint system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair level edge) ≤
      rate⁻¹ ^ level * lengths (XiCol system.toRuleData level edge) := by
  letI := xiLevelMetricSpace system ruleConnected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) level
  have isometry := xiCompletionEmbedding_isometry system ruleConnected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) eigenpair level
  change dist (xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair level (XiTail system level edge))
    (xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair level (XiHead system level edge)) ≤ _
  rw [isometry.dist_eq]
  exact mul_le_mul_of_nonneg_left
    ((XiNetwork system level).weightedDistance_edge (fun colour => (lengthsPositive colour).le) edge)
    (pow_nonneg (inv_nonneg.mpr (zero_le_one.trans rateGreaterThanOne.le)) _)

theorem xiAddressLimits_same_edge_close (level : ℕ) (first second : XiEdgeAddress system)
    (edgeEquality : xiAddressEdge system level first = xiAddressEdge system level second) :
    dist (xiAddressLimit system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair first)
      (xiAddressLimit system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair second) ≤
      2 * ((xiRuleRadius system lengths * rate⁻¹) * rate⁻¹ ^ level / (1 - rate⁻¹)) := by
  have tailEquality : xiAddressTailApproximation system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair level first =
      xiAddressTailApproximation system ruleConnected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair level second := by
    unfold xiAddressTailApproximation
    rw [edgeEquality]
  have firstBound := xiAddressLimit_error system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair first level
  have secondBound := xiAddressLimit_error system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair second level
  have triangle := dist_triangle
    (xiAddressLimit system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair first)
    (xiAddressTailApproximation system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair level first)
    (xiAddressLimit system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair second)
  rw [dist_comm _ (xiAddressTailApproximation system ruleConnected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair level first), tailEquality] at triangle
  rw [tailEquality] at firstBound
  linarith

theorem xiFineTail_to_ancestorTail (mass : XiMassParameters system) (initialLevel offset : ℕ)
    (edge : XiEdge system.toRuleData (initialLevel + offset)) :
    dist (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair
        (initialLevel + offset) edge)
      (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair
        initialLevel (xiEdgeAncestor system initialLevel offset edge)) ≤
      (xiRuleRadius system lengths * rate⁻¹) * rate⁻¹ ^ (initialLevel + offset) / (1 - rate⁻¹) +
        (xiRuleRadius system lengths * rate⁻¹) * rate⁻¹ ^ initialLevel / (1 - rate⁻¹) := by
  obtain ⟨address, addressEquality⟩ := mass.exists_address_through_edge (initialLevel + offset) edge
  have ancestorEquality : xiAddressEdge system initialLevel address =
      xiEdgeAncestor system initialLevel offset edge := by
    simpa only [addressEquality] using (xiEdgeAncestor_address system initialLevel offset address).symm
  have fineEquality : xiAddressTailApproximation system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair (initialLevel + offset) address =
      xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair
        (initialLevel + offset) edge := by
    simp only [xiAddressTailApproximation, xiEdgeTailPoint, addressEquality]
  have coarseEquality : xiAddressTailApproximation system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair initialLevel address =
      xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair
        initialLevel (xiEdgeAncestor system initialLevel offset edge) := by
    simp only [xiAddressTailApproximation, xiEdgeTailPoint, ancestorEquality]
  rw [← fineEquality, ← coarseEquality]
  have triangle := dist_triangle
    (xiAddressTailApproximation system ruleConnected lengths lengthsPositive rate rateGreaterThanOne
      eigenpair (initialLevel + offset) address)
    (xiAddressLimit system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair address)
    (xiAddressTailApproximation system ruleConnected lengths lengthsPositive rate rateGreaterThanOne
      eigenpair initialLevel address)
  rw [dist_comm (xiAddressLimit system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair address)] at triangle
  exact triangle.trans (add_le_add
    (xiAddressLimit_error system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair address _)
    (xiAddressLimit_error system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair address _))

end EIGS

#print axioms EIGS.xiCompletionEdge_distance_le
#print axioms EIGS.xiAddressLimits_same_edge_close
#print axioms EIGS.xiFineTail_to_ancestorTail
