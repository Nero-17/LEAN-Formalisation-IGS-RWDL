import RequestProject.Section31.EIGSUnitHarmonicFiniteBasis
import RequestProject.Section31.EIGSNativeResolventUniformHarmonicError
import RequestProject.Section31.EIGSUnitEnergyRecovery
import RequestProject.Section31.EIGSNonstationaryHarmonics

/-! The actual finite resolvents, at a fixed positive resolvent parameter,
admit continuous finite-grid approximations uniformly over all forcing
vectors after normalization by their pointwise sup norm. All interpolation
and coefficient bounds concern the actual finite solutions. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 3000000

variable {K : ℕ}

theorem xiUnitTraceExtension_eq_unitPotentialAt (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarse steps : ℕ) (values : XiVtx system coarse → ℝ) :
    xiUnitTraceExtension system rulesConnected coarse steps values =
      xiUnitPotentialAt system rulesConnected coarse (coarse + steps)
        (Nat.le_add_right _ _) values := by
  rw [xiUnitTraceExtension_eq_potentialValues, xiUnitPotentialAt_eq_potentialValues]

theorem xiNativeFiniteResolvent_finite_continuous_approximation
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (mass : XiMassParameters system) (normalization : ℝ)
    (normalizationPositive : 0 < normalization) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    ∀ (step : ℝ) (stepPositive : 0 < step) (tolerance : ℝ), 0 < tolerance →
      ∃ coarse : ℕ, ∃ basis : XiVtx system coarse → C(parameters.LimitSpace, ℝ),
        ∃ threshold : ℕ, ∀ steps, threshold ≤ coarse + steps →
          ∀ (forcing : Lp ℝ 2 (xiVertexSpeedMeasure system mass (coarse + steps)))
            (vertex : XiVtx system (coarse + steps)),
          let resistanceRate := system.resistanceSpectralRadius rulesConnected distancePositive
          let ratePositive := (system.resistanceSpectralRadius_positive_eigenpair
            rulesConnected distancePositive).1
          let solution := xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique
            plantingNonadjacent mass (coarse + steps) resistanceRate normalization ratePositive.le
              normalizationPositive.le step stepPositive forcing
          |solution vertex - ∑ boundary,
            solution (xiForward system coarse steps boundary) *
              basis boundary (parameters.vertexEmbedding (coarse + steps) vertex)| ≤
          tolerance * ‖fun target : XiVtx system (coarse + steps) => forcing target‖ := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  dsimp only
  obtain ⟨upper, upperPositive, harmonicError⟩ :=
    xiNativeFiniteResolvent_uniform_harmonic_error_spectral system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive mass normalization normalizationPositive
  have resistancePositive := (system.resistanceSpectralRadius_positive_eigenpair
    rulesConnected distancePositive).1
  have timeRateGreaterThanOne :
      1 < mass.rate * system.resistanceSpectralRadius rulesConnected distancePositive := by
    rw [XiMassParameters.rate_eq_spectralRadius system mass]
    exact massResistanceSpectralProduct_gt_one system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  have timeRatePositive := zero_lt_one.trans timeRateGreaterThanOne
  intro step stepPositive tolerance tolerancePositive
  have halfPositive : 0 < tolerance / 2 := by positivity
  have tailConvergence : Tendsto (fun coarse : ℕ =>
      (upper / step) *
        (mass.rate * system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse)
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr timeRatePositive.le)
        ((inv_lt_one₀ timeRatePositive).mpr timeRateGreaterThanOne)).const_mul (upper / step)
  obtain ⟨coarse, coarseSmall⟩ :=
    (tailConvergence.eventually (gt_mem_nhds halfPositive)).exists
  obtain ⟨basis, basisApproximation⟩ :=
    exists_xiUnitPotential_finite_basis_uniform_approximation_of_rules system rulesConnected
      rulesLoopless rulesUnique plantingNonadjacent distancePositive coarse
  obtain ⟨threshold, basisSmall⟩ := basisApproximation (tolerance / 2) halfPositive
  refine ⟨coarse, basis, threshold, ?_⟩
  intro steps afterThreshold forcing vertex
  let solution := xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass (coarse + steps)
      (system.resistanceSpectralRadius rulesConnected distancePositive) normalization
      resistancePositive.le normalizationPositive.le step stepPositive forcing
  change |solution vertex - ∑ boundary,
    solution (xiForward system coarse steps boundary) *
      basis boundary (parameters.vertexEmbedding (coarse + steps) vertex)| ≤ _
  have boundaryNorm : ‖fun boundary : XiVtx system coarse =>
      solution (xiForward system coarse steps boundary)‖ ≤
      ‖fun target : XiVtx system (coarse + steps) => forcing target‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro boundary
    rw [Real.norm_eq_abs]
    exact xiNativeFiniteResolvent_sup_bound system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent mass (coarse + steps) _ normalization resistancePositive.le
        normalizationPositive.le step stepPositive forcing (xiForward system coarse steps boundary)
  have firstError :
      |solution vertex - xiUnitPotentialAt system rulesConnected coarse (coarse + steps)
        (Nat.le_add_right _ _) (fun boundary => solution (xiForward system coarse steps boundary)) vertex| ≤
      (tolerance / 2) * ‖fun target : XiVtx system (coarse + steps) => forcing target‖ := by
    have actualError := harmonicError coarse steps step stepPositive forcing vertex
    dsimp only at actualError
    rw [xiUnitTraceExtension_eq_unitPotentialAt] at actualError
    apply actualError.trans
    calc
      _ = ((upper / step) *
          (mass.rate * system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse) *
          ‖fun target : XiVtx system (coarse + steps) => forcing target‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right coarseSmall.le (norm_nonneg _)
  have secondError := basisSmall (coarse + steps) afterThreshold (Nat.le_add_right _ _)
    (fun boundary => solution (xiForward system coarse steps boundary)) vertex
  have secondBound := secondError.trans
    (mul_le_mul_of_nonneg_left boundaryNorm halfPositive.le)
  apply (abs_sub_le (solution vertex)
    (xiUnitPotentialAt system rulesConnected coarse (coarse + steps) (Nat.le_add_right _ _)
      (fun boundary => solution (xiForward system coarse steps boundary)) vertex)
    (∑ boundary, solution (xiForward system coarse steps boundary) *
      basis boundary (parameters.vertexEmbedding (coarse + steps) vertex))).trans
  calc
    _ ≤ (tolerance / 2) * ‖fun target : XiVtx system (coarse + steps) => forcing target‖ +
      (tolerance / 2) * ‖fun target : XiVtx system (coarse + steps) => forcing target‖ :=
      add_le_add firstError secondBound
    _ = _ := by ring

end
end EIGS

#print axioms EIGS.xiUnitTraceExtension_eq_unitPotentialAt
#print axioms EIGS.xiNativeFiniteResolvent_finite_continuous_approximation
