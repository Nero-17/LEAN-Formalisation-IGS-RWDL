import RequestProject.Section31.EIGSAddressCellMetricSeparation
import RequestProject.Section31.EIGSAddressIncidentStar

/-! Actual physical completion-ball mass from coarse endpoint incidence.
The address pullback of a sufficiently small ball is bounded by the two
endpoint star weights, using the constructed cell separation theorem.
No physical-ball mass estimate is an input. Candidate source: no compilation
is claimed. -/

namespace EIGS
open MeasureTheory Filter Topology
open scoped Classical
noncomputable section
set_option maxHeartbeats 4000000
variable {K : ℕ}

theorem exists_xiCompletionBall_incidence_mass_bound (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = rate • lengths)
    (mass : XiMassParameters system)
    (lowerLength : ℝ) (lowerLengthPositive : 0 < lowerLength)
    (lengthLower : ∀ colour, lowerLength ≤ lengths colour) :
    ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ (coarse : ℕ) (reference : XiEdgeAddress system) (radius : ℝ),
      radius < lowerLength * rate⁻¹ ^ coarse →
      (xiLimitMeasure system rulesConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).real
        (Metric.closedBall
          (xiAddressLimit system rulesConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair reference) radius) ≤
      coefficient / mass.rate ^ coarse *
        ((xiVertexIncidenceCount system coarse (XiTail system coarse (xiAddressEdge system coarse reference)) : ℝ) +
          (xiVertexIncidenceCount system coarse (XiHead system coarse (xiAddressEdge system coarse reference)) : ℝ)) := by
  obtain ⟨_, coefficient, _, coefficientPositive, massBounds⟩ :=
    exists_xiAddressStarWeight_mass_comparison system mass
  refine ⟨coefficient, coefficientPositive, ?_⟩
  intro coarse reference radius radiusBound
  let center := xiAddressLimit system rulesConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair reference
  let region : Set (XiEdgeAddress system) :=
    (xiAddressLimit system rulesConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair) ⁻¹'
      Metric.closedBall center radius
  have regionMeasurable : MeasurableSet region := isClosed_closedBall.measurableSet.preimage
    (measurable_xiAddressLimit system rulesConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
  have starIntegrable (vertex : XiVtx system coarse) :
      Integrable (xiAddressStarWeight system coarse vertex) mass.addressMeasure :=
    (show Integrable (xiEdgeStarMultiplicity system coarse vertex)
      (mass.addressMeasure.map (xiAddressEdge system coarse)) from Integrable.of_finite).comp_measurable
        (measurable_xiAddressEdge system coarse)
  have pointwise (address : XiEdgeAddress system) :
      region.indicator (fun _ => (1 : ℝ)) address ≤
        xiAddressStarWeight system coarse (XiTail system coarse (xiAddressEdge system coarse reference)) address +
        xiAddressStarWeight system coarse (XiHead system coarse (xiAddressEdge system coarse reference)) address := by
    by_cases inside : address ∈ region
    · rw [Set.indicator_of_mem inside]
      have near : dist center
          (xiAddressLimit system rulesConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair address) ≤ radius := by
        simpa only [region, Set.mem_preimage, Metric.mem_closedBall, dist_comm] using inside
      have incident :
          (XiTail system coarse (xiAddressEdge system coarse address) =
            XiTail system coarse (xiAddressEdge system coarse reference) ∨
           XiHead system coarse (xiAddressEdge system coarse address) =
            XiTail system coarse (xiAddressEdge system coarse reference)) ∨
          (XiTail system coarse (xiAddressEdge system coarse address) =
            XiHead system coarse (xiAddressEdge system coarse reference) ∨
           XiHead system coarse (xiAddressEdge system coarse address) =
            XiHead system coarse (xiAddressEdge system coarse reference)) := by
        by_contra neither
        have separated := xiAddressLimits_separated_of_nonincident_cells system rulesConnected lengths
          lengthsPositive rate rateGreaterThanOne eigenpair lowerLength lowerLengthPositive lengthLower
          coarse reference address (not_or.mp neither).1 (not_or.mp neither).2
        exact (not_lt_of_ge separated) (near.trans_lt radiusBound)
      rcases incident with (incidence | incidence) | (incidence | incidence) <;>
        unfold xiAddressStarWeight xiEdgeStarMultiplicity <;>
        simp only [incidence, if_true] <;> split_ifs <;> norm_num
    · rw [Set.indicator_of_notMem inside]
      exact add_nonneg
        (xiEdgeStarMultiplicity_bounds system coarse (XiTail system coarse (xiAddressEdge system coarse reference)) _).1
        (xiEdgeStarMultiplicity_bounds system coarse (XiHead system coarse (xiAddressEdge system coarse reference)) _).1
  have indicatorIdentity :
      (∫ address, region.indicator (fun _ => (1 : ℝ)) address ∂mass.addressMeasure) = mass.addressMeasure.real region := by
    simpa only [smul_eq_mul, mul_one] using
      (integral_indicator_const (μ := mass.addressMeasure) (1 : ℝ) regionMeasurable)
  have additionIdentity :
      (∫ address,
        xiAddressStarWeight system coarse (XiTail system coarse (xiAddressEdge system coarse reference)) address +
        xiAddressStarWeight system coarse (XiHead system coarse (xiAddressEdge system coarse reference)) address
          ∂mass.addressMeasure) =
      (∫ address, xiAddressStarWeight system coarse (XiTail system coarse (xiAddressEdge system coarse reference)) address
        ∂mass.addressMeasure) +
      (∫ address, xiAddressStarWeight system coarse (XiHead system coarse (xiAddressEdge system coarse reference)) address
        ∂mass.addressMeasure) := by
    simpa only [Pi.add_apply] using integral_add
      (starIntegrable (XiTail system coarse (xiAddressEdge system coarse reference)))
      (starIntegrable (XiHead system coarse (xiAddressEdge system coarse reference)))
  have compared := integral_mono ((integrable_const (1 : ℝ)).indicator regionMeasurable)
    ((starIntegrable (XiTail system coarse (xiAddressEdge system coarse reference))).add
      (starIntegrable (XiHead system coarse (xiAddressEdge system coarse reference)))) pointwise
  rw [indicatorIdentity, additionIdentity] at compared
  have ballEquality :
      (xiLimitMeasure system rulesConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).real
        (Metric.closedBall center radius) = mass.addressMeasure.real region := by
    change (mass.addressMeasure.map
      (xiAddressLimit system rulesConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair)).real
        (Metric.closedBall center radius) = _
    simp only [measureReal_def, Measure.map_apply
      (measurable_xiAddressLimit system rulesConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
      isClosed_closedBall.measurableSet, region]
  rw [ballEquality]
  exact (compared.trans (add_le_add
    ((massBounds coarse (XiTail system coarse (xiAddressEdge system coarse reference))).2)
    ((massBounds coarse (XiHead system coarse (xiAddressEdge system coarse reference))).2))).trans_eq (by ring)

end
end EIGS

#print axioms EIGS.exists_xiCompletionBall_incidence_mass_bound
