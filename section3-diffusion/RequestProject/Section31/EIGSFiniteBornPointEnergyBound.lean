import RequestProject.Section31.EIGSPointEvaluation
import RequestProject.Section31.EIGSIncidenceResistanceDecayWithoutPrimitive
import RequestProject.Section31.EIGSIncidentStarCompletionMesh
import RequestProject.Section2SpectralGrowth

/-! The actual finite-born point estimate includes the degree correction.
The existing two-scale point-energy inequality and the actual primitive-degree
growth theorem supply every estimate. This is a finite-energy continuous-core
statement; heat-kernel rows and closed-domain extension are separate consumers.
No local Nash or point-estimate conclusion is assumed. -/

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped BigOperators Classical BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem exists_xiFiniteBorn_point_energy_bound (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (primitiveDegree : (degreeMatrix system).IsPrimitive) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
    ∀ (birth : ℕ) (vertex : XiVtx system birth),
      ∃ normConstant energyConstant : ℝ, 0 < normConstant ∧ 0 < energyConstant ∧
      ∀ age (target : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)),
      xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) ≠ ⊤ →
      target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair birth vertex) ^ 2 ≤
        normConstant * (mass.rate ^ (birth + age) /
          finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age) *
            ‖core.embed (BoundedContinuousFunction.mkOfCompact target)‖ ^ 2 +
        energyConstant * (1 / (finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age *
          resistanceRate ^ (birth + age))) *
          (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  obtain ⟨tailConstant, tailPositive, pointConstant, pointPositive, pointBound⟩ :=
    exists_xiContinuous_point_energy_bound system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector
      vectorPositive renormalizationEigenpair
  obtain ⟨degreePositive, growth⟩ :=
    degree_spectral_growth_from_primitive_rules system rulesConnected primitiveDegree
  have massPositive : 0 < mass.rate := mass.rate_positive
  dsimp only
  intro birth vertex
  obtain ⟨lower, upper, lowerPositive, upperPositive, growthBounds⟩ := growth birth vertex
  refine ⟨2 / (pointConstant * lower), 2 * tailConstant ^ 2 / (pointConstant * lower),
    by positivity, by positivity, ?_⟩
  intro age target targetFinite
  have incidenceLower : lower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age ≤
      (xiVertexIncidenceCount system (birth + age) (xiForward system birth age vertex) : ℝ) := by
    rw [xiVertexIncidenceCount_eq_degree_state_sum]
    exact (growthBounds age).1
  have actual := pointBound target targetFinite (birth + age) (xiForward system birth age vertex)
  rw [xiCompletionEmbedding_forward] at actual
  have normCoefficient :
      2 * mass.rate ^ (birth + age) /
          (pointConstant * (xiVertexIncidenceCount system (birth + age)
            (xiForward system birth age vertex) : ℝ)) ≤
        (2 / (pointConstant * lower)) * (mass.rate ^ (birth + age) /
          finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age) := by
    calc
      _ ≤ 2 * mass.rate ^ (birth + age) /
          (pointConstant * (lower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age)) :=
        div_le_div_of_nonneg_left (by positivity)
          (mul_pos pointPositive (mul_pos lowerPositive (pow_pos degreePositive age)))
          (mul_le_mul_of_nonneg_left incidenceLower pointPositive.le)
      _ = _ := by field_simp <;> ring
  have inverseCoefficient :
      1 / ((xiVertexIncidenceCount system (birth + age) (xiForward system birth age vertex) : ℝ) *
        resistanceRate ^ (birth + age)) ≤
      1 / (lower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age *
        resistanceRate ^ (birth + age)) :=
    one_div_le_one_div_of_le
      (mul_pos (mul_pos lowerPositive (pow_pos degreePositive age)) (pow_pos ratePositive (birth + age)))
      (mul_le_mul_of_nonneg_right incidenceLower (pow_pos ratePositive (birth + age)).le)
  have energyCoefficient :
      (2 * tailConstant ^ 2 / pointConstant) *
          (1 / ((xiVertexIncidenceCount system (birth + age) (xiForward system birth age vertex) : ℝ) *
            resistanceRate ^ (birth + age))) ≤
        (2 * tailConstant ^ 2 / (pointConstant * lower)) *
          (1 / (finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age *
            resistanceRate ^ (birth + age))) := by
    calc
      _ ≤ (2 * tailConstant ^ 2 / pointConstant) *
          (1 / (lower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age *
            resistanceRate ^ (birth + age))) :=
        mul_le_mul_of_nonneg_left inverseCoefficient (by positivity)
      _ = _ := by field_simp <;> ring
  exact actual.trans (add_le_add
    (mul_le_mul_of_nonneg_right normCoefficient (sq_nonneg _))
    (mul_le_mul_of_nonneg_right energyCoefficient ENNReal.toReal_nonneg))

end
end EIGS

#print axioms EIGS.exists_xiFiniteBorn_point_energy_bound
