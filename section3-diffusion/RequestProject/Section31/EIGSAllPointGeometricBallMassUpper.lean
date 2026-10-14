import RequestProject.Section31.EIGSUniformVertexIncidenceBound
import RequestProject.Section31.EIGSCompletionBallIncidenceMass

/-! Actual uniform geometric ball upper masses. Density is used only to
choose a nearby address at each scale, and a larger address-centered ball
is controlled by its two endpoint incidence counts. -/

namespace EIGS
open MeasureTheory Metric
open scoped Classical
noncomputable section
variable {K : ℕ}

theorem exists_xiAllPointGeometricBallMassUpper (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (mass : XiMassParameters system) (primitiveDegree : (degreeMatrix system).IsPrimitive) :
    ∃ coefficient radiusFactor : ℝ, 0 < coefficient ∧ 0 < radiusFactor ∧
      ∀ level (point : XiMetricCompletion system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair),
        (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).real
          (Metric.ball point (radiusFactor * rate⁻¹ ^ level)) ≤
        coefficient * (finiteRealMatrixSpectralRadius (degreeMatrix system) / mass.rate) ^ level := by
  obtain ⟨minimumColour, _, minimumBound⟩ := Finset.univ.exists_min_image lengths
    ⟨system.initCol, Finset.mem_univ _⟩
  obtain ⟨massConstant, massConstantPositive, ballBound⟩ :=
    exists_xiCompletionBall_incidence_mass_bound system connected lengths lengthsPositive
      rate rateGreaterThanOne eigenpair mass (lengths minimumColour) (lengthsPositive minimumColour)
      (fun colour => minimumBound colour (Finset.mem_univ _))
  obtain ⟨degreeConstant, degreeConstantPositive, incidenceBound⟩ :=
    exists_xiUniformVertex_incidence_bound system connected primitiveDegree
  have minimumPositive := lengthsPositive minimumColour
  let radiusFactor := lengths minimumColour / 4
  have radiusFactorPositive : 0 < radiusFactor := by dsimp only [radiusFactor]; positivity
  refine ⟨2 * massConstant * degreeConstant, radiusFactor, by positivity, radiusFactorPositive, ?_⟩
  intro level point
  have powerPositive : 0 < rate⁻¹ ^ level :=
    pow_pos (inv_pos.mpr (zero_lt_one.trans rateGreaterThanOne)) level
  obtain ⟨reference, referenceNear⟩ := Metric.denseRange_iff.mp
    (xiAddressLimit_denseRange system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)
    point (radiusFactor * rate⁻¹ ^ level) (mul_pos radiusFactorPositive powerPositive)
  have containment : Metric.ball point (radiusFactor * rate⁻¹ ^ level) ⊆
      Metric.closedBall (xiAddressLimit system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair reference) (2 * radiusFactor * rate⁻¹ ^ level) := by
    intro other inside
    have near := Metric.mem_ball.mp inside
    have triangle := dist_triangle other point
      (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair reference)
    apply Metric.mem_closedBall.mpr
    linarith only [near, referenceNear, triangle]
  have radiusFit : 2 * radiusFactor * rate⁻¹ ^ level < lengths minimumColour * rate⁻¹ ^ level := by
    apply mul_lt_mul_of_pos_right _ powerPositive
    dsimp only [radiusFactor]
    linarith [lengthsPositive minimumColour]
  have massBound := ballBound level reference (2 * radiusFactor * rate⁻¹ ^ level) radiusFit
  have degreeBound := add_le_add
    (incidenceBound level (XiTail system level (xiAddressEdge system level reference)))
    (incidenceBound level (XiHead system level (xiAddressEdge system level reference)))
  have comparison := mul_le_mul_of_nonneg_left degreeBound
    (div_pos massConstantPositive (pow_pos mass.rate_positive level)).le
  exact (measureReal_mono containment).trans (massBound.trans (comparison.trans_eq (by
    rw [div_pow]
    ring)))

end
end EIGS

#print axioms EIGS.exists_xiAllPointGeometricBallMassUpper
