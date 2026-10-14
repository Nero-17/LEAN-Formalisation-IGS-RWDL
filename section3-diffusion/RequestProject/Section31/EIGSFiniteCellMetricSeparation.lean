import RequestProject.Section31.EIGSZeroFlatMetricPotential

/-! A whole descendant cell is separated from the complement of its two
coarse endpoint stars. The distance bound is derived using the constructed
flat metric potential, not supplied as an assumption. Candidate source:
no compilation is claimed. -/

namespace EIGS
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000
variable {K : ℕ}

theorem xiWeightedDistance_cell_to_outside_two_stars (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (coarse steps : ℕ)
    (selected : XiEdge system.toRuleData coarse)
    {lengths : Fin K → ℝ} (lengthsNonnegative : 0 ≤ lengths)
    (radius : ℝ) (radiusPositive : 0 < radius)
    (radiusBound : ∀ colour,
      radius ≤ ((system.ruleFamily rulesConnected).metricLengths^[steps] lengths) colour)
    (sourceEdge : XiEdge system.toRuleData (coarse + steps))
    (sourceAncestor : xiEdgeAncestor system coarse steps sourceEdge = selected)
    (target : XiVtx system (coarse + steps))
    (outsideTail : ¬ xiIncidentStar system coarse (XiTail system coarse selected) steps target)
    (outsideHead : ¬ xiIncidentStar system coarse (XiHead system coarse selected) steps target) :
    radius ≤ (XiNetwork system (coarse + steps)).weightedDistance lengths
      (XiTail system (coarse + steps) sourceEdge) target := by
  let potential : XiVtx system coarse → ℝ := fun vertex =>
    if vertex = XiTail system coarse selected ∨ vertex = XiHead system coarse selected then 0 else radius
  have potentialBounds (vertex : XiVtx system coarse) :
      0 ≤ potential vertex ∧ potential vertex ≤ radius := by
    dsimp only [potential]
    split_ifs <;> constructor <;> linarith
  have baseLipschitz : (XiNetwork system coarse).EdgeLipschitz
      ((system.ruleFamily rulesConnected).metricLengths^[steps] lengths) potential := by
    intro edge
    change |potential (XiTail system coarse edge) - potential (XiHead system coarse edge)| ≤
      ((system.ruleFamily rulesConnected).metricLengths^[steps] lengths) (XiCol system.toRuleData coarse edge)
    apply abs_le.mpr
    have tailBounds := potentialBounds (XiTail system coarse edge)
    have headBounds := potentialBounds (XiHead system coarse edge)
    have colourBound := radiusBound (XiCol system.toRuleData coarse edge)
    constructor <;> linarith
  have refinedLipschitz := xiZeroFlatMetricPotential_lipschitz system rulesConnected coarse steps potential
    lengthsNonnegative baseLipschitz
  have sourceZero := (xiZeroFlatMetricPotential_zero_descendant_endpoints system rulesConnected
    coarse steps potential selected (by simp [potential]) (by simp [potential])
    lengths sourceEdge sourceAncestor).1
  have targetLower := xiZeroFlatMetricPotential_lower_outside_two_stars system rulesConnected
    coarse steps potential (XiTail system coarse selected) (XiHead system coarse selected)
    radius radiusPositive (fun vertex notTail notHead => by simp [potential, notTail, notHead])
    lengthsNonnegative target outsideTail outsideHead
  have difference := (XiNetwork system (coarse + steps)).potential_difference_le_weightedDistance
    (xiSimpleGraph_connected system rulesConnected (coarse + steps)) refinedLipschitz
    (XiTail system (coarse + steps) sourceEdge) target
  rw [sourceZero, zero_sub, abs_neg] at difference
  exact targetLower.trans ((le_abs_self _).trans difference)

theorem xiWeightedDistance_nonincident_cells (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (coarse steps : ℕ)
    {lengths : Fin K → ℝ} (lengthsNonnegative : 0 ≤ lengths)
    (radius : ℝ) (radiusPositive : 0 < radius)
    (radiusBound : ∀ colour,
      radius ≤ ((system.ruleFamily rulesConnected).metricLengths^[steps] lengths) colour)
    (sourceEdge targetEdge : XiEdge system.toRuleData (coarse + steps))
    (notTailIncident : ¬ (
      XiTail system coarse (xiEdgeAncestor system coarse steps targetEdge) =
        XiTail system coarse (xiEdgeAncestor system coarse steps sourceEdge) ∨
      XiHead system coarse (xiEdgeAncestor system coarse steps targetEdge) =
        XiTail system coarse (xiEdgeAncestor system coarse steps sourceEdge)))
    (notHeadIncident : ¬ (
      XiTail system coarse (xiEdgeAncestor system coarse steps targetEdge) =
        XiHead system coarse (xiEdgeAncestor system coarse steps sourceEdge) ∨
      XiHead system coarse (xiEdgeAncestor system coarse steps targetEdge) =
        XiHead system coarse (xiEdgeAncestor system coarse steps sourceEdge))) :
    radius ≤ (XiNetwork system (coarse + steps)).weightedDistance lengths
      (XiTail system (coarse + steps) sourceEdge) (XiTail system (coarse + steps) targetEdge) := by
  apply xiWeightedDistance_cell_to_outside_two_stars system rulesConnected coarse steps
    (xiEdgeAncestor system coarse steps sourceEdge) lengthsNonnegative radius radiusPositive radiusBound
    sourceEdge rfl (XiTail system (coarse + steps) targetEdge)
  · intro inside
    exact notTailIncident (xiIncidentStar_endpoint_has_incident_ancestor system coarse steps
      (XiTail system coarse (xiEdgeAncestor system coarse steps sourceEdge)) targetEdge (Or.inl inside))
  · intro inside
    exact notHeadIncident (xiIncidentStar_endpoint_has_incident_ancestor system coarse steps
      (XiHead system coarse (xiEdgeAncestor system coarse steps sourceEdge)) targetEdge (Or.inl inside))

end
end EIGS

#print axioms EIGS.xiWeightedDistance_cell_to_outside_two_stars
#print axioms EIGS.xiWeightedDistance_nonincident_cells
