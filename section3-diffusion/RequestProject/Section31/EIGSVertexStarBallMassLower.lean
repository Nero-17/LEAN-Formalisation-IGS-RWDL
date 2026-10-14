import RequestProject.Section31.EIGSAddressIncidentStar

/-! An actual completion ball contains every address in a finite vertex's
incident star. Endpoint multiplicity is at most two, so the integral of
the star weight yields a lower physical ball mass without disjointness
of completion images as an assumption. -/

namespace EIGS
open MeasureTheory Metric
open scoped Classical
noncomputable section
variable {K : ℕ}

theorem exists_xiVertexStarBallMassLower (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (mass : XiMassParameters system) :
    ∃ coefficient radiusFactor : ℝ, 0 < coefficient ∧ 0 < radiusFactor ∧
      ∀ level (vertex : XiVtx system level),
        coefficient / mass.rate ^ level * (xiVertexIncidenceCount system level vertex : ℝ) ≤
          (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).real
            (Metric.ball (xiCompletionEmbedding system connected lengths lengthsPositive rate
              (zero_lt_one.trans rateGreaterThanOne) eigenpair level vertex) (radiusFactor * rate⁻¹ ^ level)) := by
  obtain ⟨lower, upper, lowerPositive, upperPositive, massBounds⟩ :=
    exists_xiAddressStarWeight_mass_comparison system mass
  have ratePositive := zero_lt_one.trans rateGreaterThanOne
  have denominatorPositive : 0 < 1 - rate⁻¹ :=
    sub_pos.mpr ((inv_lt_one₀ ratePositive).mpr rateGreaterThanOne)
  let meshConstant := xiMaximumColourLength system lengths +
    (xiRuleRadius system lengths * rate⁻¹) / (1 - rate⁻¹)
  have meshNonnegative : 0 ≤ meshConstant := by
    dsimp only [meshConstant]
    exact add_nonneg
      ((lengthsPositive system.initCol).le.trans (xiColourLength_le_maximum system lengths system.initCol))
      (div_nonneg (mul_nonneg (xiRuleRadius_nonnegative system (fun colour => (lengthsPositive colour).le))
        (inv_nonneg.mpr ratePositive.le)) denominatorPositive.le)
  refine ⟨lower / 2, meshConstant + 1, by positivity, by positivity, ?_⟩
  intro level vertex
  let region : Set (XiEdgeAddress system) :=
    (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair) ⁻¹'
      Metric.ball (xiCompletionEmbedding system connected lengths lengthsPositive rate ratePositive eigenpair level vertex)
        ((meshConstant + 1) * rate⁻¹ ^ level)
  have regionMeasurable : MeasurableSet region := measurableSet_ball.preimage
    (measurable_xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
  have weightIntegrable : Integrable (xiAddressStarWeight system level vertex) mass.addressMeasure :=
    (show Integrable (xiEdgeStarMultiplicity system level vertex)
      (mass.addressMeasure.map (xiAddressEdge system level)) from Integrable.of_finite).comp_measurable
        (measurable_xiAddressEdge system level)
  have pointwise (address : XiEdgeAddress system) : xiAddressStarWeight system level vertex address ≤
      region.indicator (fun _ => (2 : ℝ)) address := by
    by_cases supported : xiAddressStarWeight system level vertex address ≠ 0
    · have mesh := xiAddressStarWeight_support_mesh system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair level vertex address supported
      have inside : address ∈ region := by
        apply Metric.mem_ball.mpr
        change dist _ _ < (meshConstant + 1) * rate⁻¹ ^ level
        have powerPositive := pow_pos (inv_pos.mpr ratePositive) level
        change dist _ _ ≤ meshConstant * rate⁻¹ ^ level at mesh
        nlinarith
      rw [Set.indicator_of_mem inside]
      exact (xiEdgeStarMultiplicity_bounds system level vertex (xiAddressEdge system level address)).2
    · rw [not_ne_iff.mp supported]
      exact Set.indicator_nonneg (fun _ _ => by norm_num) address
  have integralBound := integral_mono weightIntegrable
    ((integrable_const (2 : ℝ)).indicator regionMeasurable) pointwise
  have indicatorIdentity :
      (∫ address, region.indicator (fun _ => (2 : ℝ)) address ∂mass.addressMeasure) =
        2 * mass.addressMeasure.real region := by
    simpa only [smul_eq_mul, mul_comm] using
      (integral_indicator_const (μ := mass.addressMeasure) (2 : ℝ) regionMeasurable)
  rw [indicatorIdentity] at integralBound
  have ballIdentity :
      (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).real
        (Metric.ball (xiCompletionEmbedding system connected lengths lengthsPositive rate ratePositive eigenpair level vertex)
          ((meshConstant + 1) * rate⁻¹ ^ level)) = mass.addressMeasure.real region := by
    rw [xiLimitMeasure, measureReal_def, Measure.map_apply
      (measurable_xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
      measurableSet_ball]
    rfl
  rw [ballIdentity]
  have combined := ((massBounds level vertex).1).trans integralBound
  have coefficientIdentity : lower / mass.rate ^ level *
      (xiVertexIncidenceCount system level vertex : ℝ) =
      2 * ((lower / 2) / mass.rate ^ level * (xiVertexIncidenceCount system level vertex : ℝ)) := by ring
  rw [coefficientIdentity] at combined
  nlinarith only [combined]

end
end EIGS

#print axioms EIGS.exists_xiVertexStarBallMassLower
