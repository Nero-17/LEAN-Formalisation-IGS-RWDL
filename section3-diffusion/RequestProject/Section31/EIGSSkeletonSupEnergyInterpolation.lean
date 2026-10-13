import RequestProject.Section31.EIGSPointEvaluation
import RequestProject.Section31.EIGSL2EnergyDensity

/-! Two-scale supremum interpolation on the actual finite vertex skeletons.
The stronger estimate weights each vertex by its actual incidence. Every
constant and the resistance eigenpair in the original-rule consumer are
constructed internally. These are finite-skeleton estimates, not a global
ultracontractive bound or an assertion that a heat kernel already exists. -/

namespace IGS.Sec31

 theorem pi_norm_sq_le_of_pointwise_sq_le
    {Index : Type*} [Fintype Index] (values : Index → ℝ) (bound : ℝ)
    (boundNonnegative : 0 ≤ bound) (pointBound : ∀ index, (values index) ^ 2 ≤ bound) :
    ‖values‖ ^ 2 ≤ bound := by
  have normBound : ‖values‖ ≤ Real.sqrt bound := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg bound)).mpr
    intro index
    apply (sq_le_sq₀ (norm_nonneg (values index)) (Real.sqrt_nonneg bound)).1
    simpa only [Real.norm_eq_abs, sq_abs, Real.sq_sqrt boundNonnegative] using pointBound index
  nlinarith [norm_nonneg values, Real.sqrt_nonneg bound, Real.sq_sqrt boundNonnegative]

end IGS.Sec31

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 3000000
variable {K : ℕ}

theorem exists_xiSkeleton_sup_energy_interpolation (system : EIGSData K)
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
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
    ∃ l2Constant : ℝ, 0 < l2Constant ∧ ∃ energyConstant : ℝ, 0 < energyConstant ∧
      ∀ (target : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)),
      xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) ≠ ⊤ →
      ∀ level,
      (‖fun vertex : XiVtx system level => Real.sqrt (xiVertexIncidenceCount system level vertex : ℝ) *
          target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex)‖ ^ 2 ≤
        l2Constant * mass.rate ^ level * ‖core.embed (BoundedContinuousFunction.mkOfCompact target)‖ ^ 2 +
        energyConstant / resistanceRate ^ level *
          (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal) ∧
      (‖fun vertex : XiVtx system level =>
          target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex)‖ ^ 2 ≤
        l2Constant * mass.rate ^ level * ‖core.embed (BoundedContinuousFunction.mkOfCompact target)‖ ^ 2 +
        energyConstant / resistanceRate ^ level *
          (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal) := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  obtain ⟨tailConstant, tailPositive, pointConstant, pointPositive, pointBound⟩ :=
    exists_xiContinuous_point_energy_bound system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  refine ⟨2 / pointConstant, by positivity, 2 * tailConstant ^ 2 / pointConstant, by positivity, ?_⟩
  intro target targetFinite level
  let bound := (2 / pointConstant) * mass.rate ^ level *
      ‖core.embed (BoundedContinuousFunction.mkOfCompact target)‖ ^ 2 +
    (2 * tailConstant ^ 2 / pointConstant) / resistanceRate ^ level *
      (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal
  have boundNonnegative : 0 ≤ bound := by
    have massPositive := mass.rate_positive
    dsimp only [bound]
    positivity
  have incidenceBound (vertex : XiVtx system level) :
      (xiVertexIncidenceCount system level vertex : ℝ) *
        target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex) ^ 2 ≤ bound := by
    have incidencePositive : 0 < (xiVertexIncidenceCount system level vertex : ℝ) := by
      exact_mod_cast xiVertexIncidenceCount_positive system rulesConnected level vertex
    have pointControl := mul_le_mul_of_nonneg_left (pointBound target targetFinite level vertex) incidencePositive.le
    have coefficientIdentity :
        (xiVertexIncidenceCount system level vertex : ℝ) *
          ((2 * mass.rate ^ level / (pointConstant * (xiVertexIncidenceCount system level vertex : ℝ))) *
            ‖core.embed (BoundedContinuousFunction.mkOfCompact target)‖ ^ 2 +
          (2 * tailConstant ^ 2 / pointConstant) *
            (1 / ((xiVertexIncidenceCount system level vertex : ℝ) * resistanceRate ^ level)) *
            (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
              (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
                (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal) = bound := by
      dsimp only [bound]
      field_simp [pointPositive.ne', incidencePositive.ne', (pow_pos ratePositive level).ne']
      <;> ring
    rw [coefficientIdentity] at pointControl
    exact pointControl
  constructor
  · apply pi_norm_sq_le_of_pointwise_sq_le _ bound boundNonnegative
    intro vertex
    have incidenceNonnegative : 0 ≤ (xiVertexIncidenceCount system level vertex : ℝ) := Nat.cast_nonneg _
    rw [mul_pow, Real.sq_sqrt incidenceNonnegative]
    exact incidenceBound vertex
  · apply pi_norm_sq_le_of_pointwise_sq_le _ bound boundNonnegative
    intro vertex
    have incidenceAtLeastOne : (1 : ℝ) ≤ (xiVertexIncidenceCount system level vertex : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (xiVertexIncidenceCount_positive system rulesConnected level vertex)
    have unweightedBound : target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex) ^ 2 ≤
        (xiVertexIncidenceCount system level vertex : ℝ) *
          target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex) ^ 2 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right incidenceAtLeastOne
        (sq_nonneg (target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex)))
    exact unweightedBound.trans (incidenceBound vertex)

theorem exists_xiSkeleton_sup_energy_interpolation_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
    let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
      ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
    ∃ l2Constant : ℝ, 0 < l2Constant ∧ ∃ energyConstant : ℝ, 0 < energyConstant ∧
      ∀ (target : C(XiMetricCompletion system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
        (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair, ℝ)),
      xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (target ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
          (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair) ≠ ⊤ →
      ∀ level,
      (‖fun vertex : XiVtx system level => Real.sqrt (xiVertexIncidenceCount system level vertex : ℝ) *
          target (xiCompletionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
            (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair level vertex)‖ ^ 2 ≤
        l2Constant * mass.rate ^ level * ‖core.embed (BoundedContinuousFunction.mkOfCompact target)‖ ^ 2 +
        energyConstant / resistanceRate ^ level *
          (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (target ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
              (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair)).toReal) ∧
      (‖fun vertex : XiVtx system level =>
          target (xiCompletionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
            (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair level vertex)‖ ^ 2 ≤
        l2Constant * mass.rate ^ level * ‖core.embed (BoundedContinuousFunction.mkOfCompact target)‖ ^ 2 +
        energyConstant / resistanceRate ^ level *
          (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (target ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
              (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair)).toReal) := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj (system.plant_ne colour) (plantingNonadjacent colour)
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair, _, _⟩ :=
    exists_xiDenseLpQuadraticEnergy_of_rules system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  dsimp only
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair, ?_⟩
  exact exists_xiSkeleton_sup_energy_interpolation system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair

end
end EIGS

#print axioms IGS.Sec31.pi_norm_sq_le_of_pointwise_sq_le
#print axioms EIGS.exists_xiSkeleton_sup_energy_interpolation
#print axioms EIGS.exists_xiSkeleton_sup_energy_interpolation_of_rules
