import RequestProject.Section31.EIGSAddressSupport
import RequestProject.Section31.EIGSHarmonicLipschitzApproximation

/-! Quantitative lower mass of actual completion balls, uniformly at every
point. Density selects a nearby address at each scale; a whole cylinder is
then contained in the ball. Surjectivity of the address map is unnecessary.
Candidate source; compilation is not claimed. -/

namespace EIGS

open MeasureTheory Filter Topology Metric Set
open scoped Classical
noncomputable section
variable {K : ℕ}

theorem exists_xiAllPointGeometricBallMassLower (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (mass : XiMassParameters system) :
    ∃ massLower radiusFactor : ℝ, 0 < massLower ∧ 0 < radiusFactor ∧
      ∀ level (point : XiMetricCompletion system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair),
        massLower / mass.rate ^ level ≤
          (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).real
            (Metric.ball point (radiusFactor * rate⁻¹ ^ level)) := by
  obtain ⟨amplitudeLower, amplitudeLowerPositive, amplitudeBound⟩ :=
    exists_positive_colour_length_lower_bound system mass.amplitude mass.amplitude_positive
  have ratePositive : 0 < rate := zero_lt_one.trans rateGreaterThanOne
  have denominatorPositive : 0 < 1 - rate⁻¹ :=
    sub_pos.mpr ((inv_lt_one₀ ratePositive).mpr rateGreaterThanOne)
  have radiusNonnegative := xiRuleRadius_nonnegative system (fun colour => (lengthsPositive colour).le)
  let radiusFactor := 1 + 2 * (xiRuleRadius system lengths * rate⁻¹) / (1 - rate⁻¹)
  have radiusFactorPositive : 0 < radiusFactor := by
    dsimp only [radiusFactor]
    positivity
  refine ⟨amplitudeLower / mass.amplitude system.initCol, radiusFactor,
    div_pos amplitudeLowerPositive (mass.amplitude_positive _), radiusFactorPositive, ?_⟩
  intro level point
  obtain ⟨reference, referenceNear⟩ := Metric.denseRange_iff.mp
    (xiAddressLimit_denseRange system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)
    point (rate⁻¹ ^ level) (pow_pos (inv_pos.mpr ratePositive) level)
  have cylinderInside :
      {address | xiAddressEdge system level address = xiAddressEdge system level reference} ⊆
      (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair) ⁻¹'
        Metric.ball point (radiusFactor * rate⁻¹ ^ level) := by
    intro address agreement
    have close := xiAddressLimits_same_edge_close system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair level reference address agreement.symm
    have triangle := dist_triangle point
      (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair reference)
      (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair address)
    have radiusIdentity : radiusFactor * rate⁻¹ ^ level = rate⁻¹ ^ level +
        2 * ((xiRuleRadius system lengths * rate⁻¹) * rate⁻¹ ^ level / (1 - rate⁻¹)) := by
      dsimp only [radiusFactor]
      ring
    change dist _ point < _
    rw [dist_comm, radiusIdentity]
    linarith only [referenceNear, close, triangle]
  have cylinderMass : mass.addressMeasure.real
      {address | xiAddressEdge system level address = xiAddressEdge system level reference} =
      mass.amplitude (XiCol system.toRuleData level (xiAddressEdge system level reference)) /
        (mass.rate ^ level * mass.amplitude system.initCol) := by
    rw [measureReal_def, mass.addressMeasure_cylinder, ENNReal.toReal_ofReal]
    exact (mass.edgeWeight_positive level _).le
  have ballMass :
      (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).real
        (Metric.ball point (radiusFactor * rate⁻¹ ^ level)) =
      mass.addressMeasure.real
        ((xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair) ⁻¹'
          Metric.ball point (radiusFactor * rate⁻¹ ^ level)) := by
    rw [xiLimitMeasure, measureReal_def, Measure.map_apply
      (measurable_xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
      measurableSet_ball]
    rfl
  rw [ballMass]
  calc
    (amplitudeLower / mass.amplitude system.initCol) / mass.rate ^ level =
        amplitudeLower / (mass.rate ^ level * mass.amplitude system.initCol) := by
      rw [div_div, mul_comm (mass.amplitude system.initCol) (mass.rate ^ level)]
    _ ≤ mass.amplitude (XiCol system.toRuleData level (xiAddressEdge system level reference)) /
        (mass.rate ^ level * mass.amplitude system.initCol) :=
      div_le_div_of_nonneg_right (amplitudeBound _)
        (mul_pos (pow_pos mass.rate_positive level) (mass.amplitude_positive system.initCol)).le
    _ = mass.addressMeasure.real
        {address | xiAddressEdge system level address = xiAddressEdge system level reference} := cylinderMass.symm
    _ ≤ _ := ENNReal.toReal_mono (measure_ne_top mass.addressMeasure _) (measure_mono cylinderInside)

end
end EIGS

#print axioms EIGS.exists_xiAllPointGeometricBallMassLower
