import RequestProject.Section31.EIGSFiniteCellMetricSeparation
import RequestProject.Section31.EIGSIncidentStarCompletionMesh
import RequestProject.Section2MultiStepSpectralBall

/-! An actual small completion ball, pulled back to any fine vertex set,
lies in the union of two coarse endpoint stars. The center is arbitrary,
including vertices that only occur as heads of oriented edges. The flat
potential is zero on both endpoints of the entire selected descendant
cell, so no address surjectivity or ball containment is assumed. -/

namespace EIGS
open Metric
open scoped Classical
noncomputable section
set_option maxHeartbeats 4000000
variable {K : ℕ}

theorem xiWeightedDistance_cell_endpoint_to_outside_two_stars (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected) (coarse steps : ℕ)
    (selected : XiEdge system.toRuleData coarse)
    {lengths : Fin K → ℝ} (lengthsNonnegative : 0 ≤ lengths)
    (radius : ℝ) (radiusPositive : 0 < radius)
    (radiusBound : ∀ colour,
      radius ≤ ((system.ruleFamily connected).metricLengths^[steps] lengths) colour)
    (sourceEdge : XiEdge system.toRuleData (coarse + steps))
    (sourceAncestor : xiEdgeAncestor system coarse steps sourceEdge = selected)
    (source : XiVtx system (coarse + steps))
    (sourceEndpoint : source = XiTail system (coarse + steps) sourceEdge ∨
      source = XiHead system (coarse + steps) sourceEdge)
    (target : XiVtx system (coarse + steps))
    (outsideTail : ¬ xiIncidentStar system coarse (XiTail system coarse selected) steps target)
    (outsideHead : ¬ xiIncidentStar system coarse (XiHead system coarse selected) steps target) :
    radius ≤ (XiNetwork system (coarse + steps)).weightedDistance lengths source target := by
  let potential : XiVtx system coarse → ℝ := fun vertex =>
    if vertex = XiTail system coarse selected ∨ vertex = XiHead system coarse selected then 0 else radius
  have potentialBounds (vertex : XiVtx system coarse) :
      0 ≤ potential vertex ∧ potential vertex ≤ radius := by
    dsimp only [potential]
    split_ifs <;> constructor <;> linarith
  have baseLipschitz : (XiNetwork system coarse).EdgeLipschitz
      ((system.ruleFamily connected).metricLengths^[steps] lengths) potential := by
    intro edge
    change |potential (XiTail system coarse edge) - potential (XiHead system coarse edge)| ≤
      ((system.ruleFamily connected).metricLengths^[steps] lengths) (XiCol system.toRuleData coarse edge)
    apply abs_le.mpr
    have tailBounds := potentialBounds (XiTail system coarse edge)
    have headBounds := potentialBounds (XiHead system coarse edge)
    have colourBound := radiusBound (XiCol system.toRuleData coarse edge)
    constructor <;> linarith
  have refinedLipschitz := xiZeroFlatMetricPotential_lipschitz system connected coarse steps potential
    lengthsNonnegative baseLipschitz
  have sourceZeros := xiZeroFlatMetricPotential_zero_descendant_endpoints system connected
    coarse steps potential selected (by simp [potential]) (by simp [potential]) lengths sourceEdge sourceAncestor
  have sourceZero : xiZeroFlatMetricPotential system connected coarse potential steps lengths source = 0 := by
    rcases sourceEndpoint with rfl | rfl
    · exact sourceZeros.1
    · exact sourceZeros.2
  have targetLower := xiZeroFlatMetricPotential_lower_outside_two_stars system connected
    coarse steps potential (XiTail system coarse selected) (XiHead system coarse selected)
    radius radiusPositive (fun vertex notTail notHead => by simp [potential, notTail, notHead])
    lengthsNonnegative target outsideTail outsideHead
  have difference := (XiNetwork system (coarse + steps)).potential_difference_le_weightedDistance
    (xiSimpleGraph_connected system connected (coarse + steps)) refinedLipschitz source target
  rw [sourceZero, zero_sub, abs_neg] at difference
  exact targetLower.trans ((le_abs_self _).trans difference)

theorem xiCompletionFineBall_subset_two_stars (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (lowerLength : ℝ) (lowerLengthPositive : 0 < lowerLength)
    (lengthLower : ∀ colour, lowerLength ≤ lengths colour)
    (coarse steps : ℕ) (source : XiVtx system (coarse + steps)) :
    ∃ selected : XiEdge system.toRuleData coarse,
      ∀ target : XiVtx system (coarse + steps),
      dist (xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair (coarse + steps) source)
        (xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair (coarse + steps) target) <
        lowerLength * rate⁻¹ ^ coarse →
      xiIncidentStar system coarse (XiTail system coarse selected) steps target ∨
        xiIncidentStar system coarse (XiHead system coarse selected) steps target := by
  have ratePositive := zero_lt_one.trans rateGreaterThanOne
  letI : Nontrivial (XiVtx system (coarse + steps)) :=
    ⟨⟨xiPositiveTerminal system _, xiNegativeTerminal system _, xiTerminals_distinct system _⟩⟩
  obtain ⟨neighbor, adjacent⟩ :=
    (xiSimpleGraph_connected system connected (coarse + steps)).preconnected.exists_adj_of_nontrivial source
  have incident : ∃ edge : XiEdge system.toRuleData (coarse + steps),
      source = XiTail system (coarse + steps) edge ∨ source = XiHead system (coarse + steps) edge := by
    rcases adjacent.2 with ⟨edge, tail, head⟩ | ⟨edge, tail, head⟩
    · exact ⟨edge, Or.inl tail.symm⟩
    · exact ⟨edge, Or.inr head.symm⟩
  obtain ⟨sourceEdge, sourceEndpoint⟩ := incident
  let selected := xiEdgeAncestor system coarse steps sourceEdge
  refine ⟨selected, ?_⟩
  intro target near
  by_contra outside
  have radiusBound : ∀ colour,
      rate ^ steps * lowerLength ≤ ((system.ruleFamily connected).metricLengths^[steps] lengths) colour := by
    intro colour
    rw [system.metricLengths_iterate_eigenpair connected ratePositive.le eigenpair]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (lengthLower colour) (pow_nonneg ratePositive.le steps)
  have separated := xiWeightedDistance_cell_endpoint_to_outside_two_stars system connected coarse steps
    selected (fun colour => (lengthsPositive colour).le) (rate ^ steps * lowerLength)
    (mul_pos (pow_pos ratePositive steps) lowerLengthPositive) radiusBound sourceEdge rfl source
    sourceEndpoint target (not_or.mp outside).1 (not_or.mp outside).2
  have cancellation : rate⁻¹ ^ (coarse + steps) * (rate ^ steps * lowerLength) =
      lowerLength * rate⁻¹ ^ coarse := by
    rw [pow_add]
    calc
      _ = (lowerLength * rate⁻¹ ^ coarse) * (rate⁻¹ ^ steps * rate ^ steps) := by ring
      _ = _ := by simp only [inv_pow, inv_mul_cancel₀ (pow_ne_zero steps ratePositive.ne'), mul_one]
  have scaled := mul_le_mul_of_nonneg_left separated
    (pow_nonneg (inv_nonneg.mpr ratePositive.le) (coarse + steps))
  rw [cancellation] at scaled
  rw [xiCompletionEmbedding_dist_eq_scaled_weighted] at near
  exact (not_lt_of_ge scaled) near

end
end EIGS

#print axioms EIGS.xiWeightedDistance_cell_endpoint_to_outside_two_stars
#print axioms EIGS.xiCompletionFineBall_subset_two_stars
