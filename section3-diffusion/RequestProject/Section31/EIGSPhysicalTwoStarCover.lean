import RequestProject.Section31.EIGSPhysicalClosedCellImage
import RequestProject.Section31.EIGSAddressCellMetricSeparation
import RequestProject.Section31.EIGSOriginalCountableRealisation
import RequestProject.Section31.BallMassDiameterScaling

/-! The exact physical two-star covering statement. Both the centre and the
target range over the whole metric completion, and the centre belongs to a
prescribed physical closed cell. The stars are finite unions of physical
closed descendant cells. The diameter-normalized version uses the same sets. -/

namespace EIGS
open Filter Topology Metric
open scoped Classical
noncomputable section
set_option maxHeartbeats 4000000
variable {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)

theorem xiAddressLimit_surjective (mass : XiMassParameters system) :
    Function.Surjective
      (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair) := by
  have closedRange : IsClosed (Set.range
      (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)) :=
    (isCompact_range (continuous_xiAddressLimit system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair)).isClosed
  apply Set.range_eq_univ.mp
  rw [← closedRange.closure_eq]
  exact (xiAddressLimit_denseRange system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair mass).closure_range

def xiPhysicalClosedStar (level : ℕ) (vertex : XiVtx system level) :
    Set (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
  {point | ∃ edge : XiEdge system.toRuleData level,
    (XiTail system level edge = vertex ∨ XiHead system level edge = vertex) ∧
    point ∈ xiPhysicalClosedCell system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair level edge}

theorem xiPhysicalClosedStar_isClosed (level : ℕ) (vertex : XiVtx system level) :
    IsClosed (xiPhysicalClosedStar system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair level vertex) := by
  classical
  have identity : xiPhysicalClosedStar system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair level vertex =
      ⋃ edge : XiEdge system.toRuleData level,
        if XiTail system level edge = vertex ∨ XiHead system level edge = vertex then
          xiPhysicalClosedCell system connected lengths lengthsPositive rate
            rateGreaterThanOne eigenpair level edge else ∅ := by
    ext point
    simp only [xiPhysicalClosedStar, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨edge, incident, membership⟩
      exact ⟨edge, by simpa only [if_pos incident] using membership⟩
    · rintro ⟨edge, membership⟩
      split_ifs at membership with incident
      · exact ⟨edge, incident, membership⟩
      · exact False.elim membership
  rw [identity]
  apply isClosed_iUnion_of_finite
  intro edge
  split_ifs
  · exact xiPhysicalClosedCell_isClosed system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair level edge
  · exact isClosed_empty

theorem xiPhysicalCell_ball_subset_two_stars (mass : XiMassParameters system)
    (lowerLength : ℝ) (lowerLengthPositive : 0 < lowerLength)
    (lengthLower : ∀ colour, lowerLength ≤ lengths colour)
    (level : ℕ) (edge : XiEdge system.toRuleData level)
    (center : XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair)
    (centerInCell : center ∈ xiPhysicalClosedCell system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair level edge) :
    Metric.ball center (lowerLength * rate⁻¹ ^ level) ⊆
      xiPhysicalClosedStar system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
        level (XiTail system level edge) ∪
      xiPhysicalClosedStar system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
        level (XiHead system level edge) := by
  rw [xiPhysicalClosedCell_eq_addressCylinderImage system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair mass level edge] at centerInCell
  obtain ⟨first, through, rfl⟩ := centerInCell
  change xiAddressEdge system level first = edge at through
  intro target near
  obtain ⟨second, rfl⟩ := xiAddressLimit_surjective system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair mass target
  have targetInCell := xiAddressLimit_mem_physicalClosedCell system connected lengths lengthsPositive
    rate rateGreaterThanOne eigenpair level (xiAddressEdge system level second) second rfl
  by_contra outside
  have notTailIncident : ¬ (XiTail system level (xiAddressEdge system level second) =
      XiTail system level (xiAddressEdge system level first) ∨
      XiHead system level (xiAddressEdge system level second) =
        XiTail system level (xiAddressEdge system level first)) := by
    intro incident
    apply outside
    exact Or.inl ⟨xiAddressEdge system level second, by simpa only [through] using incident,
      targetInCell⟩
  have notHeadIncident : ¬ (XiTail system level (xiAddressEdge system level second) =
      XiHead system level (xiAddressEdge system level first) ∨
      XiHead system level (xiAddressEdge system level second) =
        XiHead system level (xiAddressEdge system level first)) := by
    intro incident
    apply outside
    exact Or.inr ⟨xiAddressEdge system level second, by simpa only [through] using incident,
      targetInCell⟩
  have separation := xiAddressLimits_separated_of_nonincident_cells system connected lengths lengthsPositive
    rate rateGreaterThanOne eigenpair lowerLength lowerLengthPositive lengthLower level first second
    notTailIncident notHeadIncident
  exact (not_lt_of_ge separation) (by simpa only [Metric.mem_ball, dist_comm] using near)

theorem exists_xiPhysicalCell_diameter_ball_subset_two_stars (mass : XiMassParameters system) :
    ∃ coefficient : ℝ, 0 < coefficient ∧
    ∀ (level : ℕ) (edge : XiEdge system.toRuleData level)
      (center : XiMetricCompletion system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair),
      center ∈ xiPhysicalClosedCell system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair level edge →
      @Metric.ball _ (MeasuredGHP.xiCompletionDiameterMetricSpace system connected lengths
        lengthsPositive rate rateGreaterThanOne eigenpair).toPseudoMetricSpace center
          (coefficient * rate⁻¹ ^ level) ⊆
        xiPhysicalClosedStar system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
          level (XiTail system level edge) ∪
        xiPhysicalClosedStar system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
          level (XiHead system level edge) := by
  obtain ⟨lowerLength, lowerPositive, lowerBound⟩ :=
    exists_positive_colour_length_lower_bound system lengths lengthsPositive
  let diameter := xiCompletionDiameter system connected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) eigenpair
  have diameterPositive : 0 < diameter := xiCompletionDiameter_positive system connected lengths
    lengthsPositive rate rateGreaterThanOne eigenpair
  refine ⟨lowerLength / diameter, div_pos lowerPositive diameterPositive, ?_⟩
  intro level edge center membership
  have identity := @MeasuredGHP.diameterNormalized_ball_eq_native
    (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair)
    (xiCompletionMetricSpace system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair)
    diameterPositive center ((lowerLength / diameter) * rate⁻¹ ^ level)
  have cancellation : diameter * ((lowerLength / diameter) * rate⁻¹ ^ level) =
      lowerLength * rate⁻¹ ^ level := by field_simp
  change @Metric.ball _ (MeasuredGHP.xiCompletionDiameterMetricSpace system connected lengths
    lengthsPositive rate rateGreaterThanOne eigenpair).toPseudoMetricSpace center
      ((lowerLength / diameter) * rate⁻¹ ^ level) =
        Metric.ball center (diameter * ((lowerLength / diameter) * rate⁻¹ ^ level)) at identity
  rw [cancellation] at identity
  rw [identity]
  exact xiPhysicalCell_ball_subset_two_stars system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair mass lowerLength lowerPositive lowerBound level edge center membership

end

theorem exists_xiPhysicalCell_diameter_two_star_cover_of_rules {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
    let rateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
    ∃ coefficient : ℝ, 0 < coefficient ∧
    ∀ (level : ℕ) (edge : XiEdge system.toRuleData level) (center : parameters.LimitSpace),
      center ∈ xiPhysicalClosedCell system connected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair level edge →
      @Metric.ball _ (MeasuredGHP.xiCompletionDiameterMetricSpace system connected parameters.lengths
        parameters.lengthsPositive (system.distanceSpectralRadius connected) rateGreaterThanOne
        parameters.eigenpair).toPseudoMetricSpace center
          (coefficient * (system.distanceSpectralRadius connected)⁻¹ ^ level) ⊆
        xiPhysicalClosedStar system connected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair
          level (XiTail system level edge) ∪
        xiPhysicalClosedStar system connected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair
          level (XiHead system level edge) := by
  intro parameters rateGreaterThanOne
  exact exists_xiPhysicalCell_diameter_ball_subset_two_stars system connected parameters.lengths
    parameters.lengthsPositive (system.distanceSpectralRadius connected) rateGreaterThanOne
    parameters.eigenpair (xiMassParametersOfRules system connected distancePositive)

end EIGS

#print axioms EIGS.xiAddressLimit_surjective
#print axioms EIGS.xiPhysicalClosedStar_isClosed
#print axioms EIGS.xiPhysicalCell_ball_subset_two_stars
#print axioms EIGS.exists_xiPhysicalCell_diameter_ball_subset_two_stars
#print axioms EIGS.exists_xiPhysicalCell_diameter_two_star_cover_of_rules
