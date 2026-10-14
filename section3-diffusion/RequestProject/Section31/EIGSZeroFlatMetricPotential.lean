import RequestProject.Section31.SelectedFlatMetricPotential
import RequestProject.Section2StarCounts

/-! Iterated actual metric potentials which remain zero on every descendant
of an initially zero edge. Outside two specified incident stars, a positive
initial lower bound is preserved. This gives the finite-graph ingredients
for separation of disjoint coarse cells; no separation estimate is assumed.
Candidate source: no compilation is claimed. -/

namespace EIGS
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000
variable {K : ℕ}

def xiZeroFlatMetricPotential (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (coarse : ℕ)
    (potential : XiVtx system coarse → ℝ) :
    (steps : ℕ) → (Fin K → ℝ) → XiVtx system (coarse + steps) → ℝ
  | 0, _ => potential
  | steps + 1, lengths =>
      let previous := xiZeroFlatMetricPotential system rulesConnected coarse potential steps
        ((system.ruleFamily rulesConnected).metricLengths lengths)
      (XiNetwork system (coarse + steps)).substSelectedFlatMetricPotential
        (system.ruleFamily rulesConnected) lengths previous
        (fun edge => previous (XiTail system (coarse + steps) edge) = 0 ∧
          previous (XiHead system (coarse + steps) edge) = 0)

theorem xiZeroFlatMetricPotential_lipschitz (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (coarse steps : ℕ)
    (potential : XiVtx system coarse → ℝ) {lengths : Fin K → ℝ}
    (lengthsNonnegative : 0 ≤ lengths)
    (baseLipschitz : (XiNetwork system coarse).EdgeLipschitz
      ((system.ruleFamily rulesConnected).metricLengths^[steps] lengths) potential) :
    (XiNetwork system (coarse + steps)).EdgeLipschitz lengths
      (xiZeroFlatMetricPotential system rulesConnected coarse potential steps lengths) := by
  induction steps generalizing lengths with
  | zero => exact baseLipschitz
  | succ steps induction =>
    have previousLipschitz := induction
      (Network.metricLengths_nonnegative (system.ruleFamily rulesConnected) rulesConnected lengthsNonnegative)
      (by simpa only [Function.iterate_succ_apply] using baseLipschitz)
    apply (XiNetwork system (coarse + steps)).substSelectedFlatMetricPotential_lipschitz
      (system.ruleFamily rulesConnected) rulesConnected lengthsNonnegative _ _
      (fun edge zeroEndpoints => zeroEndpoints.1.trans zeroEndpoints.2.symm) previousLipschitz

theorem xiZeroFlatMetricPotential_succ_zero_copy (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (coarse steps : ℕ)
    (potential : XiVtx system coarse → ℝ) (lengths : Fin K → ℝ)
    (edge : XiEdge system.toRuleData (coarse + steps))
    (tailZero : xiZeroFlatMetricPotential system rulesConnected coarse potential steps
      ((system.ruleFamily rulesConnected).metricLengths lengths) (XiTail system (coarse + steps) edge) = 0)
    (headZero : xiZeroFlatMetricPotential system rulesConnected coarse potential steps
      ((system.ruleFamily rulesConnected).metricLengths lengths) (XiHead system (coarse + steps) edge) = 0)
    (vertex : (system.rule (XiCol system.toRuleData (coarse + steps) edge)).V) :
    xiZeroFlatMetricPotential system rulesConnected coarse potential (steps + 1) lengths
      (embedRuleVtx system (coarse + steps) edge (XiTail system (coarse + steps) edge)
        (XiHead system (coarse + steps) edge) vertex) = 0 := by
  let previous := xiZeroFlatMetricPotential system rulesConnected coarse potential steps
    ((system.ruleFamily rulesConnected).metricLengths lengths)
  change (XiNetwork system (coarse + steps)).substSelectedFlatMetricPotential
    (system.ruleFamily rulesConnected) lengths previous
    (fun edge => previous (XiTail system (coarse + steps) edge) = 0 ∧
      previous (XiHead system (coarse + steps) edge) = 0)
    ((XiNetwork system (coarse + steps)).substEmbed (system.ruleFamily rulesConnected) edge vertex) = 0
  rw [(XiNetwork system (coarse + steps)).substSelectedFlatMetricPotential_constant_on_selected_copy
    (system.ruleFamily rulesConnected) lengths previous _
    (fun edge zeroEndpoints => zeroEndpoints.1.trans zeroEndpoints.2.symm)
    edge ⟨tailZero, headZero⟩ vertex]
  exact tailZero

theorem xiZeroFlatMetricPotential_zero_descendant_endpoints (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (coarse steps : ℕ)
    (potential : XiVtx system coarse → ℝ) (selected : XiEdge system.toRuleData coarse)
    (tailZero : potential (XiTail system coarse selected) = 0)
    (headZero : potential (XiHead system coarse selected) = 0)
    (lengths : Fin K → ℝ) (edge : XiEdge system.toRuleData (coarse + steps))
    (descendant : xiEdgeAncestor system coarse steps edge = selected) :
    xiZeroFlatMetricPotential system rulesConnected coarse potential steps lengths
        (XiTail system (coarse + steps) edge) = 0 ∧
      xiZeroFlatMetricPotential system rulesConnected coarse potential steps lengths
        (XiHead system (coarse + steps) edge) = 0 := by
  induction steps generalizing lengths with
  | zero =>
    change edge = selected at descendant
    subst edge
    exact ⟨tailZero, headZero⟩
  | succ steps induction =>
    have parentZero := induction ((system.ruleFamily rulesConnected).metricLengths lengths) edge.1 descendant
    constructor
    · change xiZeroFlatMetricPotential system rulesConnected coarse potential (steps + 1) lengths
        (XiTail system ((coarse + steps) + 1) edge) = 0
      rw [XiTail_succ]
      exact xiZeroFlatMetricPotential_succ_zero_copy system rulesConnected coarse steps potential lengths
        edge.1 parentZero.1 parentZero.2 _
    · change xiZeroFlatMetricPotential system rulesConnected coarse potential (steps + 1) lengths
        (XiHead system ((coarse + steps) + 1) edge) = 0
      rw [XiHead_succ]
      exact xiZeroFlatMetricPotential_succ_zero_copy system rulesConnected coarse steps potential lengths
        edge.1 parentZero.1 parentZero.2 _

theorem xiZeroFlatMetricPotential_lower_outside_two_stars (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (coarse steps : ℕ)
    (potential : XiVtx system coarse → ℝ) (first second : XiVtx system coarse)
    (radius : ℝ) (radiusPositive : 0 < radius)
    (initialLower : ∀ vertex, vertex ≠ first → vertex ≠ second → radius ≤ potential vertex)
    {lengths : Fin K → ℝ} (lengthsNonnegative : 0 ≤ lengths)
    (vertex : XiVtx system (coarse + steps))
    (outsideFirst : ¬ xiIncidentStar system coarse first steps vertex)
    (outsideSecond : ¬ xiIncidentStar system coarse second steps vertex) :
    radius ≤ xiZeroFlatMetricPotential system rulesConnected coarse potential steps lengths vertex := by
  induction steps generalizing lengths with
  | zero => exact initialLower vertex outsideFirst outsideSecond
  | succ steps induction =>
    have previousNonnegative := Network.metricLengths_nonnegative
      (system.ruleFamily rulesConnected) rulesConnected lengthsNonnegative
    cases vertex with
    | inl vertex => exact induction previousNonnegative vertex outsideFirst outsideSecond
    | inr privateVertex =>
      obtain ⟨edge, interior⟩ := privateVertex
      have firstOutside := not_or.mp outsideFirst
      have secondOutside := not_or.mp outsideSecond
      have tailLower := induction previousNonnegative (XiTail system (coarse + steps) edge)
        firstOutside.1 secondOutside.1
      have headLower := induction previousNonnegative (XiHead system (coarse + steps) edge)
        firstOutside.2 secondOutside.2
      have notFlat : ¬ (xiZeroFlatMetricPotential system rulesConnected coarse potential steps
          ((system.ruleFamily rulesConnected).metricLengths lengths) (XiTail system (coarse + steps) edge) = 0 ∧
        xiZeroFlatMetricPotential system rulesConnected coarse potential steps
          ((system.ruleFamily rulesConnected).metricLengths lengths) (XiHead system (coarse + steps) edge) = 0) := by
        intro zeroEndpoints
        linarith [zeroEndpoints.1]
      dsimp only [xiZeroFlatMetricPotential, Network.substSelectedFlatMetricPotential, Network.substMetricPotential]
      rw [if_neg notFlat]
      exact le_min
        (tailLower.trans (le_add_of_nonneg_right
          ((system.ruleNetwork (XiCol system.toRuleData (coarse + steps) edge)).weightedDistance_nonnegative
            (rulesConnected _) lengthsNonnegative _ _)))
        (headLower.trans (le_add_of_nonneg_right
          ((system.ruleNetwork (XiCol system.toRuleData (coarse + steps) edge)).weightedDistance_nonnegative
            (rulesConnected _) lengthsNonnegative _ _)))

end
end EIGS

#print axioms EIGS.xiZeroFlatMetricPotential_lipschitz
#print axioms EIGS.xiZeroFlatMetricPotential_succ_zero_copy
#print axioms EIGS.xiZeroFlatMetricPotential_zero_descendant_endpoints
#print axioms EIGS.xiZeroFlatMetricPotential_lower_outside_two_stars
