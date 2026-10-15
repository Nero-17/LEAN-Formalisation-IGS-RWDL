import RequestProject.Section31.EIGSCompletionBallIncidenceMass
import RequestProject.Section31.GeometricLogarithmicHeatTimeChoice

/-! Uniform power ball upper bounds from bounded actual incidence counts.
The same radius cutoff and constant apply to every completion point.
No primitive degree matrix or degree rate greater than one is required.
Candidate source, awaiting compilation. -/

namespace IGS.Sec31
noncomputable section

theorem uniform_geometric_ball_mass_upper_all_radii {Point : Type*}
    (volume : Point → ℝ → ℝ) (volumeMonotone : ∀ point, Monotone (volume point))
    (rate massRate exponent radiusScale coefficient : ℝ)
    (rateGreaterThanOne : 1 < rate) (exponentNonnegative : 0 ≤ exponent)
    (growthIdentity : massRate = rate ^ exponent)
    (radiusScalePositive : 0 < radiusScale) (coefficientPositive : 0 < coefficient)
    (levelUpper : ∀ level point,
      volume point (radiusScale * rate⁻¹ ^ level) ≤ coefficient / massRate ^ level) :
    ∃ upperConstant radiusThreshold : ℝ, 0 < upperConstant ∧ 0 < radiusThreshold ∧
      ∀ point radius, 0 < radius → radius ≤ radiusThreshold →
        volume point radius ≤ upperConstant * radius ^ exponent := by
  have ratePositive := zero_lt_one.trans rateGreaterThanOne
  have massPositive : 0 < massRate := by
    rw [growthIdentity]
    exact Real.rpow_pos_of_pos ratePositive _
  refine ⟨coefficient * (rate / radiusScale) ^ exponent,
    min radiusScale (Real.exp (-1)),
    mul_pos coefficientPositive (Real.rpow_pos_of_pos (div_pos ratePositive radiusScalePositive) _),
    lt_min radiusScalePositive (Real.exp_pos _), ?_⟩
  intro point radius radiusPositive radiusSmall
  obtain ⟨level, _, powerLower, powerUpper, _⟩ :=
    geometric_heat_time_level_with_log_bound rate radiusScale radius rateGreaterThanOne
      radiusScalePositive radiusPositive 0
      (by simpa only [pow_zero, div_one] using radiusSmall.trans (min_le_left _ _))
      (radiusSmall.trans (min_le_right _ _))
  have radiusAtLevel : radius ≤ radiusScale * rate⁻¹ ^ level := by
    rw [inv_pow, ← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos ratePositive level)).mpr
    simpa only [mul_comm] using (le_div_iff₀ radiusPositive).mp powerLower
  have baseLower : radiusScale / (rate * radius) ≤ rate ^ level := by
    have divided : (radiusScale / radius) / rate < rate ^ level :=
      (div_lt_iff₀ ratePositive).mpr (by simpa only [pow_succ] using powerUpper)
    simpa only [div_div, mul_comm radius rate] using divided.le
  have basePositive : 0 < radiusScale / (rate * radius) := by positivity
  have massLower : (radiusScale / (rate * radius)) ^ exponent ≤ massRate ^ level := by
    calc
      _ ≤ (rate ^ level) ^ exponent :=
        Real.rpow_le_rpow basePositive.le baseLower exponentNonnegative
      _ = massRate ^ level := by
        rw [growthIdentity, ← Real.rpow_mul_natCast ratePositive.le,
          mul_comm exponent, Real.rpow_natCast_mul ratePositive.le]
  have comparison : coefficient / massRate ^ level ≤
      coefficient / (radiusScale / (rate * radius)) ^ exponent :=
    div_le_div_of_nonneg_left coefficientPositive.le
      (Real.rpow_pos_of_pos basePositive _) massLower
  have profileIdentity : coefficient / (radiusScale / (rate * radius)) ^ exponent =
      (coefficient * (rate / radiusScale) ^ exponent) * radius ^ exponent := by
    rw [Real.div_rpow radiusScalePositive.le (mul_pos ratePositive radiusPositive).le,
      Real.mul_rpow ratePositive.le radiusPositive.le,
      Real.div_rpow ratePositive.le radiusScalePositive.le]
    field_simp <;> ring
  exact ((volumeMonotone point radiusAtLevel).trans (levelUpper level point)).trans
    (comparison.trans_eq profileIdentity)

end
end IGS.Sec31

namespace EIGS
open MeasureTheory Metric
open scoped Classical
noncomputable section
variable {K : ℕ}

theorem exists_xiBoundedIncidenceGeometricBallMassUpper (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (mass : XiMassParameters system) (incidenceConstant : ℝ) (incidencePositive : 0 < incidenceConstant)
    (incidenceBound : ∀ level (vertex : XiVtx system level),
      (xiVertexIncidenceCount system level vertex : ℝ) ≤ incidenceConstant) :
    ∃ coefficient radiusFactor : ℝ, 0 < coefficient ∧ 0 < radiusFactor ∧
      ∀ level (point : XiMetricCompletion system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair),
        (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).real
          (Metric.ball point (radiusFactor * rate⁻¹ ^ level)) ≤ coefficient / mass.rate ^ level := by
  obtain ⟨minimumColour, _, minimumBound⟩ := Finset.univ.exists_min_image lengths
    ⟨system.initCol, Finset.mem_univ _⟩
  obtain ⟨massConstant, massConstantPositive, ballBound⟩ :=
    exists_xiCompletionBall_incidence_mass_bound system connected lengths lengthsPositive
      rate rateGreaterThanOne eigenpair mass (lengths minimumColour) (lengthsPositive minimumColour)
      (fun colour => minimumBound colour (Finset.mem_univ _))
  let radiusFactor := lengths minimumColour / 4
  have radiusFactorPositive : 0 < radiusFactor := by dsimp only [radiusFactor]; positivity
  refine ⟨2 * massConstant * incidenceConstant, radiusFactor, by positivity, radiusFactorPositive, ?_⟩
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
  exact (measureReal_mono containment).trans (massBound.trans (comparison.trans_eq (by ring)))

end
end EIGS

#print axioms IGS.Sec31.uniform_geometric_ball_mass_upper_all_radii
#print axioms EIGS.exists_xiBoundedIncidenceGeometricBallMassUpper
