import RequestProject.Section31.EIGSMetricCompactness
import RequestProject.Section31.EIGSEdgeAddressMeasure

/-! Each actual compatible infinite edge address determines a Cauchy sequence
of edge endpoints in the constructed Xi completion. Its limit and a uniform
geometric approximation error are proved directly from finite rule paths. -/

namespace EIGS

open Filter Topology

variable {K : ℕ} (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily ruleConnected).metricLengths lengths = rate • lengths)

include ruleConnected lengthsPositive rateGreaterThanOne eigenpair

noncomputable def xiAddressTailApproximation (level : ℕ) (address : XiEdgeAddress system) :
    XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair :=
  xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) eigenpair level
      (XiTail system level (xiAddressEdge system level address))

theorem xiAddressTailApproximation_step (address : XiEdgeAddress system) (level : ℕ) :
    dist (xiAddressTailApproximation system ruleConnected lengths lengthsPositive rate rateGreaterThanOne
        eigenpair level address)
      (xiAddressTailApproximation system ruleConnected lengths lengthsPositive rate rateGreaterThanOne
        eigenpair (level + 1) address) ≤
      (xiRuleRadius system lengths * rate⁻¹) * rate⁻¹ ^ level := by
  letI := xiUnionMetricSpace system ruleConnected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) eigenpair
  have isometry := xiCompletionUnionEmbedding_isometry system ruleConnected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) eigenpair
  unfold xiAddressTailApproximation xiCompletionEmbedding
  simp only [Function.comp_apply, isometry.dist_eq]
  change xiUnionDistance system lengths rate
    (xiVertexEmbedding system level (XiTail system level (xiAddressEdge system level address)))
    (xiVertexEmbedding system (level + 1) (XiTail system (level + 1) (xiAddressEdge system (level + 1) address))) ≤ _
  have parentEquality : (xiAddressEdge system (level + 1) address).1 = xiAddressEdge system level address :=
    xiAddressEdge_parent system address level
  rw [← parentEquality, ← xiVertexEmbedding_old system level,
    xiUnionDistance_embedding system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair]
  have bound := xiScaledWeightedDistance_rule_vertex_bound system ruleConnected
    (fun colour => (lengthsPositive colour).le) (zero_le_one.trans rateGreaterThanOne.le)
    level (xiAddressEdge system (level + 1) address).1
      ((system.rule _).tail (xiAddressEdge system (level + 1) address).2)
  exact bound.trans_eq (by rw [pow_succ]; ring)

theorem xiAddressTailApproximation_cauchy (address : XiEdgeAddress system) :
    CauchySeq (fun level => xiAddressTailApproximation system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair level address) :=
  cauchySeq_of_le_geometric rate⁻¹ (xiRuleRadius system lengths * rate⁻¹)
    ((inv_lt_one₀ (zero_lt_one.trans rateGreaterThanOne)).mpr rateGreaterThanOne)
    (xiAddressTailApproximation_step system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair address)

noncomputable def xiAddressLimit (address : XiEdgeAddress system) :
    XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair :=
  Classical.choose (cauchySeq_tendsto_of_complete
    (xiAddressTailApproximation_cauchy system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair address))

theorem xiAddressTailApproximation_tendsto (address : XiEdgeAddress system) :
    Tendsto (fun level => xiAddressTailApproximation system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair level address) atTop
      (nhds (xiAddressLimit system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair address)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete
    (xiAddressTailApproximation_cauchy system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair address))

theorem xiAddressLimit_error (address : XiEdgeAddress system) (level : ℕ) :
    dist (xiAddressTailApproximation system ruleConnected lengths lengthsPositive rate rateGreaterThanOne
        eigenpair level address)
      (xiAddressLimit system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair address) ≤
      (xiRuleRadius system lengths * rate⁻¹) * rate⁻¹ ^ level / (1 - rate⁻¹) :=
  dist_le_of_le_geometric_of_tendsto rate⁻¹ (xiRuleRadius system lengths * rate⁻¹)
    ((inv_lt_one₀ (zero_lt_one.trans rateGreaterThanOne)).mpr rateGreaterThanOne)
    (xiAddressTailApproximation_step system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair address)
    (xiAddressTailApproximation_tendsto system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair address) level

end EIGS

#print axioms EIGS.xiAddressTailApproximation_cauchy
#print axioms EIGS.xiAddressTailApproximation_tendsto
#print axioms EIGS.xiAddressLimit_error
