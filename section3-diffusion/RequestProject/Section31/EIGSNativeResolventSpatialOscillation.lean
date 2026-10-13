import RequestProject.Section31.EIGSNativeResolventFiniteGridApproximation
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.ProperSpace

/-! A uniform spatial modulus for the actual native finite resolvents at a
fixed positive resolvent parameter. The modulus is derived from the actual
continuous finite-grid approximation, and is uniform over all sufficiently
fine graph levels and all forcing vectors after sup-norm normalization. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem finite_continuous_basis_compact_coefficients
    {Space Index : Type*} [MetricSpace Space] [CompactSpace Space] [Fintype Index]
    (basis : Index → C(Space, ℝ)) (bound : ℝ) :
    IsCompact ((fun coefficients : Index → ℝ => ∑ index, coefficients index • basis index) ''
      Metric.closedBall (0 : Index → ℝ) bound) := by
  apply (isCompact_closedBall (0 : Index → ℝ) bound).image
  fun_prop

theorem finite_continuous_basis_weighted_modulus
    {Space Index : Type*} [MetricSpace Space] [CompactSpace Space] [Fintype Index]
    (basis : Index → C(Space, ℝ)) (tolerance : ℝ) (tolerancePositive : 0 < tolerance) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ (coefficients : Index → ℝ) (first second : Space),
      dist first second < radius →
      |(∑ index, coefficients index * basis index first) -
        (∑ index, coefficients index * basis index second)| ≤ tolerance * ‖coefficients‖ := by
  have jointContinuous : UniformContinuous (fun point : Space => fun index => basis index point) :=
    uniformContinuous_pi.mpr fun index =>
      CompactSpace.uniformContinuous_of_continuous (basis index).continuous
  have denominatorPositive : 0 < (Fintype.card Index : ℝ) + 1 := by positivity
  have coordinateTolerancePositive : 0 < tolerance / ((Fintype.card Index : ℝ) + 1) :=
    div_pos tolerancePositive denominatorPositive
  obtain ⟨radius, radiusPositive, close⟩ := Metric.uniformContinuous_iff.mp jointContinuous
    (tolerance / ((Fintype.card Index : ℝ) + 1)) coordinateTolerancePositive
  refine ⟨radius, radiusPositive, ?_⟩
  intro coefficients first second pointsClose
  have coordinateBound : ∀ index,
      |basis index first - basis index second| ≤ tolerance / ((Fintype.card Index : ℝ) + 1) := by
    intro index
    rw [← Real.dist_eq]
    exact (dist_le_pi_dist (fun index => basis index first)
      (fun index => basis index second) index).trans (close pointsClose).le
  have sumBound : (∑ index, |basis index first - basis index second|) ≤ tolerance := by
    calc
      _ ≤ ∑ _index : Index, tolerance / ((Fintype.card Index : ℝ) + 1) :=
        Finset.sum_le_sum fun index _ => coordinateBound index
      _ = (Fintype.card Index : ℝ) * (tolerance / ((Fintype.card Index : ℝ) + 1)) := by simp
      _ ≤ tolerance := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ denominatorPositive).mpr
        nlinarith
  have difference :
      (∑ index, coefficients index * basis index first) -
        (∑ index, coefficients index * basis index second) =
      ∑ index, coefficients index * (basis index first - basis index second) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro index _
    ring
  rw [difference]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ index, ‖coefficients‖ * |basis index first - basis index second| := by
      apply Finset.sum_le_sum
      intro index _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm coefficients index) (abs_nonneg _)
    _ = ‖coefficients‖ * ∑ index, |basis index first - basis index second| :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ ‖coefficients‖ * tolerance := mul_le_mul_of_nonneg_left sumBound (norm_nonneg _)
    _ = _ := mul_comm _ _

variable {K : ℕ}

theorem xiNativeFiniteResolvent_eventual_spatial_oscillation
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
      ∃ threshold : ℕ, ∃ radius : ℝ, 0 < radius ∧
        ∀ level, threshold ≤ level →
          ∀ (forcing : Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
            (first second : XiVtx system level),
          dist (parameters.vertexEmbedding level first) (parameters.vertexEmbedding level second) < radius →
          let resistanceRate := system.resistanceSpectralRadius rulesConnected distancePositive
          let ratePositive := (system.resistanceSpectralRadius_positive_eigenpair
            rulesConnected distancePositive).1
          let solution := xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique
            plantingNonadjacent mass level resistanceRate normalization ratePositive.le
              normalizationPositive.le step stepPositive forcing
          |solution first - solution second| ≤
            tolerance * ‖fun target : XiVtx system level => forcing target‖ := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  dsimp only
  have distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI : CompactSpace parameters.LimitSpace :=
    xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
  have resistancePositive := (system.resistanceSpectralRadius_positive_eigenpair
    rulesConnected distancePositive).1
  intro step stepPositive tolerance tolerancePositive
  have thirdPositive : 0 < tolerance / 3 := by positivity
  obtain ⟨coarse, basis, fineThreshold, approximation⟩ :=
    xiNativeFiniteResolvent_finite_continuous_approximation system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive mass normalization normalizationPositive
        step stepPositive (tolerance / 3) thirdPositive
  obtain ⟨radius, radiusPositive, basisModulus⟩ :=
    finite_continuous_basis_weighted_modulus basis (tolerance / 3) thirdPositive
  refine ⟨max coarse fineThreshold, radius, radiusPositive, ?_⟩
  intro level afterThreshold
  have afterCoarse : coarse ≤ level := (le_max_left _ _).trans afterThreshold
  have afterFineThreshold : fineThreshold ≤ level := (le_max_right _ _).trans afterThreshold
  obtain ⟨steps, rfl⟩ := Nat.exists_eq_add_of_le afterCoarse
  intro forcing first second pointsClose
  let solution := xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass (coarse + steps)
      (system.resistanceSpectralRadius rulesConnected distancePositive) normalization
      resistancePositive.le normalizationPositive.le step stepPositive forcing
  change |solution first - solution second| ≤ _
  have boundaryNorm : ‖fun boundary : XiVtx system coarse =>
      solution (xiForward system coarse steps boundary)‖ ≤
      ‖fun target : XiVtx system (coarse + steps) => forcing target‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro boundary
    rw [Real.norm_eq_abs]
    exact xiNativeFiniteResolvent_sup_bound system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent mass (coarse + steps) _ normalization resistancePositive.le
        normalizationPositive.le step stepPositive forcing (xiForward system coarse steps boundary)
  have firstError := approximation steps afterFineThreshold forcing first
  have secondError := approximation steps afterFineThreshold forcing second
  dsimp only at firstError secondError
  change |solution first - ∑ boundary, solution (xiForward system coarse steps boundary) *
    basis boundary (parameters.vertexEmbedding (coarse + steps) first)| ≤ _ at firstError
  change |solution second - ∑ boundary, solution (xiForward system coarse steps boundary) *
    basis boundary (parameters.vertexEmbedding (coarse + steps) second)| ≤ _ at secondError
  have middleError := basisModulus (fun boundary => solution (xiForward system coarse steps boundary))
    (parameters.vertexEmbedding (coarse + steps) first)
    (parameters.vertexEmbedding (coarse + steps) second) pointsClose
  have middleBound := middleError.trans
    (mul_le_mul_of_nonneg_left boundaryNorm thirdPositive.le)
  have triangle := abs_sub_le (solution first)
    (∑ boundary, solution (xiForward system coarse steps boundary) *
      basis boundary (parameters.vertexEmbedding (coarse + steps) first)) (solution second)
  have innerTriangle := abs_sub_le
    (∑ boundary, solution (xiForward system coarse steps boundary) *
      basis boundary (parameters.vertexEmbedding (coarse + steps) first))
    (∑ boundary, solution (xiForward system coarse steps boundary) *
      basis boundary (parameters.vertexEmbedding (coarse + steps) second)) (solution second)
  rw [abs_sub_comm (∑ boundary, solution (xiForward system coarse steps boundary) *
    basis boundary (parameters.vertexEmbedding (coarse + steps) second)) (solution second)] at innerTriangle
  linarith

end
end EIGS

#print axioms EIGS.finite_continuous_basis_compact_coefficients
#print axioms EIGS.finite_continuous_basis_weighted_modulus
#print axioms EIGS.xiNativeFiniteResolvent_eventual_spatial_oscillation
