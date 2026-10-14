import RequestProject.Section31.EIGSFiniteCellMetricSeparation
import RequestProject.Section31.EIGSIncidentStarCompletionMesh
import RequestProject.Section31.EIGSAddressGeometry
import RequestProject.Section2MultiStepSpectralBall

/-! Separation of two actual completion address cells with no common coarse
endpoint. The finite flat-potential estimate passes along the existing
address-tail limits, with the fine-depth scaling cancelling exactly.
Candidate source: no compilation is claimed. -/

namespace EIGS
open Filter Topology
open scoped Classical
noncomputable section
set_option maxHeartbeats 4000000
variable {K : ℕ}

theorem xiAddressLimits_separated_of_nonincident_cells (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = rate • lengths)
    (lowerLength : ℝ) (lowerLengthPositive : 0 < lowerLength)
    (lengthLower : ∀ colour, lowerLength ≤ lengths colour)
    (coarse : ℕ) (first second : XiEdgeAddress system)
    (notTailIncident : ¬ (
      XiTail system coarse (xiAddressEdge system coarse second) = XiTail system coarse (xiAddressEdge system coarse first) ∨
      XiHead system coarse (xiAddressEdge system coarse second) = XiTail system coarse (xiAddressEdge system coarse first)))
    (notHeadIncident : ¬ (
      XiTail system coarse (xiAddressEdge system coarse second) = XiHead system coarse (xiAddressEdge system coarse first) ∨
      XiHead system coarse (xiAddressEdge system coarse second) = XiHead system coarse (xiAddressEdge system coarse first))) :
    lowerLength * rate⁻¹ ^ coarse ≤
      dist (xiAddressLimit system rulesConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair first)
        (xiAddressLimit system rulesConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair second) := by
  have ratePositive := zero_lt_one.trans rateGreaterThanOne
  have finiteBound (steps : ℕ) : lowerLength * rate⁻¹ ^ coarse ≤
      dist (xiAddressTailApproximation system rulesConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair
        (coarse + steps) first)
        (xiAddressTailApproximation system rulesConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair
          (coarse + steps) second) := by
    have radiusBound : ∀ colour,
        rate ^ steps * lowerLength ≤ ((system.ruleFamily rulesConnected).metricLengths^[steps] lengths) colour := by
      intro colour
      rw [system.metricLengths_iterate_eigenpair rulesConnected ratePositive.le eigenpair]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (lengthLower colour) (pow_nonneg ratePositive.le steps)
    have finiteSeparation := xiWeightedDistance_nonincident_cells system rulesConnected coarse steps
      (fun colour => (lengthsPositive colour).le) (rate ^ steps * lowerLength)
      (mul_pos (pow_pos ratePositive steps) lowerLengthPositive) radiusBound
      (xiAddressEdge system (coarse + steps) first) (xiAddressEdge system (coarse + steps) second)
      (by simpa only [xiEdgeAncestor_address] using notTailIncident)
      (by simpa only [xiEdgeAncestor_address] using notHeadIncident)
    have cancellation : rate⁻¹ ^ (coarse + steps) * (rate ^ steps * lowerLength) =
        lowerLength * rate⁻¹ ^ coarse := by
      rw [pow_add]
      calc
        _ = (lowerLength * rate⁻¹ ^ coarse) * (rate⁻¹ ^ steps * rate ^ steps) := by ring
        _ = _ := by simp only [inv_pow, inv_mul_cancel₀ (pow_ne_zero steps ratePositive.ne'), mul_one]
    have scaled := mul_le_mul_of_nonneg_left finiteSeparation
      (pow_nonneg (inv_nonneg.mpr ratePositive.le) (coarse + steps))
    rw [cancellation] at scaled
    change lowerLength * rate⁻¹ ^ coarse ≤
      dist (xiCompletionEmbedding system rulesConnected lengths lengthsPositive rate ratePositive eigenpair
        (coarse + steps) (XiTail system (coarse + steps) (xiAddressEdge system (coarse + steps) first)))
        (xiCompletionEmbedding system rulesConnected lengths lengthsPositive rate ratePositive eigenpair
          (coarse + steps) (XiTail system (coarse + steps) (xiAddressEdge system (coarse + steps) second)))
    rw [xiCompletionEmbedding_dist_eq_scaled_weighted]
    exact scaled
  have shifted : Tendsto (fun steps : ℕ => coarse + steps) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat coarse
  have distanceLimit :=
    ((xiAddressTailApproximation_tendsto system rulesConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair
      first).comp shifted).dist
    ((xiAddressTailApproximation_tendsto system rulesConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair
      second).comp shifted)
  exact le_of_tendsto distanceLimit (Filter.Eventually.of_forall finiteBound)

end
end EIGS

#print axioms EIGS.xiAddressLimits_separated_of_nonincident_cells
