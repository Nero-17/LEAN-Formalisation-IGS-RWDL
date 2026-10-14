import RequestProject.Section31.EIGSVertexStarBallMassLower
import RequestProject.Section31.EIGSIncidenceResistanceDecayWithoutPrimitive
import RequestProject.Section2SpectralGrowth

/-! Finite-born physical lower ball masses from the actual incident star
and actual Perron degree growth. Both the birth-level radius factor and
the birth-level mass factor are retained in the constants. -/

namespace EIGS
open MeasureTheory Metric
open scoped Classical
noncomputable section
variable {K : ℕ}

theorem exists_xiFiniteBornGeometricBallMassLower (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (mass : XiMassParameters system) (primitiveDegree : (degreeMatrix system).IsPrimitive) :
    ∀ birth (vertex : XiVtx system birth),
      ∃ coefficient radiusFactor : ℝ, 0 < coefficient ∧ 0 < radiusFactor ∧ ∀ age,
        coefficient / (mass.rate / finiteRealMatrixSpectralRadius (degreeMatrix system)) ^ age ≤
          (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).real
            (Metric.ball (xiCompletionEmbedding system connected lengths lengthsPositive rate
              (zero_lt_one.trans rateGreaterThanOne) eigenpair birth vertex) (radiusFactor * rate⁻¹ ^ age)) := by
  obtain ⟨starConstant, starRadius, starConstantPositive, starRadiusPositive, starBound⟩ :=
    exists_xiVertexStarBallMassLower system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
  obtain ⟨degreePositive, degreeGrowth⟩ :=
    degree_spectral_growth_from_primitive_rules system connected primitiveDegree
  intro birth vertex
  obtain ⟨degreeLower, degreeUpper, degreeLowerPositive, degreeUpperPositive, growthBound⟩ :=
    degreeGrowth birth vertex
  refine ⟨starConstant * degreeLower / mass.rate ^ birth, starRadius * rate⁻¹ ^ birth,
    div_pos (mul_pos starConstantPositive degreeLowerPositive) (pow_pos mass.rate_positive birth),
    mul_pos starRadiusPositive (pow_pos (inv_pos.mpr (zero_lt_one.trans rateGreaterThanOne)) birth), ?_⟩
  intro age
  have incidenceLower : degreeLower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age ≤
      (xiVertexIncidenceCount system (birth + age) (xiForward system birth age vertex) : ℝ) := by
    rw [xiVertexIncidenceCount_eq_degree_state_sum]
    exact (growthBound age).1
  have actual := starBound (birth + age) (xiForward system birth age vertex)
  have radiusIdentity : starRadius * rate⁻¹ ^ (birth + age) =
      (starRadius * rate⁻¹ ^ birth) * rate⁻¹ ^ age := by rw [pow_add]; ring
  rw [xiCompletionEmbedding_forward, radiusIdentity] at actual
  have scaled := mul_le_mul_of_nonneg_left incidenceLower
    (div_pos starConstantPositive (pow_pos mass.rate_positive (birth + age))).le
  have algebra :
      (starConstant * degreeLower / mass.rate ^ birth) /
          (mass.rate / finiteRealMatrixSpectralRadius (degreeMatrix system)) ^ age =
      starConstant / mass.rate ^ (birth + age) *
        (degreeLower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age) := by
    rw [div_pow, pow_add]
    field_simp [(pow_pos degreePositive age).ne', (pow_pos mass.rate_positive birth).ne',
      (pow_pos mass.rate_positive age).ne']
    <;> ring
  rw [algebra]
  exact scaled.trans actual

end
end EIGS

#print axioms EIGS.exists_xiFiniteBornGeometricBallMassLower
