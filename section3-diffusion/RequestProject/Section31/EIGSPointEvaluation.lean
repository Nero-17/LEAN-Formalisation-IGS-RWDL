import RequestProject.Section31.EIGSContinuousProjectionTail
import RequestProject.Section31.EIGSHarmonicPointL2Lower
import RequestProject.Section31.EIGSNativeDiscreteEnergy
import RequestProject.Section31.ProjectionPointBound

/-! Two-scale point evaluation for the actual continuous finite-energy domain.
Every harmonic comparison function is constructed from the actual target.
The mass factors cancel from the energy coefficient. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

set_option maxHeartbeats 2400000

variable {K : ℕ}

theorem exists_xiContinuous_point_energy_bound (system : EIGSData K)
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
    ∃ tailConstant : ℝ, 0 < tailConstant ∧ ∃ pointConstant : ℝ, 0 < pointConstant ∧
      ∀ (target : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)),
      xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) ≠ ⊤ →
      ∀ level (vertex : XiVtx system level),
      (target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex)) ^ 2 ≤
        (2 * mass.rate ^ level / (pointConstant * (xiVertexIncidenceCount system level vertex : ℝ))) *
          ‖core.embed (BoundedContinuousFunction.mkOfCompact target)‖ ^ 2 +
        (2 * tailConstant ^ 2 / pointConstant) *
          (1 / ((xiVertexIncidenceCount system level vertex : ℝ) * resistanceRate ^ level)) *
          (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  obtain ⟨tailConstant, tailConstantPositive, tailBound⟩ := exists_xiContinuousHarmonic_native_tail system
    rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance
    lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair
  obtain ⟨pointConstant, pointConstantPositive, pointBound⟩ := exists_xiContinuousHarmonic_point_L2_bound system
    rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
    distancePositive oneColourDistance resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  refine ⟨tailConstant, tailConstantPositive, pointConstant, pointConstantPositive, ?_⟩
  intro target targetFinite level vertex
  obtain ⟨approximation, approximationAgreement, _⟩ := exists_xiContinuousHarmonic_joint_recovery system
    rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
    distancePositive oneColourDistance resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair target targetFinite
  have extensionValues : ∀ offset (finiteVertex : XiVtx system (level + offset)),
      approximation level (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair (level + offset) finiteVertex) =
      xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair level
        (fun vertex => target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex)) offset finiteVertex := by
    intro offset finiteVertex
    exact (approximationAgreement level (xiVertexEmbedding system (level + offset) finiteVertex)).trans
      (xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair level _ offset finiteVertex)
  have actualPointBound := pointBound level _ (approximation level) extensionValues vertex
  have actualTailBound := tailBound target targetFinite level (approximation level) (approximationAgreement level)
  have projectionBound : ‖core.embed (BoundedContinuousFunction.mkOfCompact (approximation level))‖ ≤
      ‖core.embed (BoundedContinuousFunction.mkOfCompact target)‖ +
        tailConstant * (Real.sqrt (mass.rate * resistanceRate))⁻¹ ^ level *
        Real.sqrt ((xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
          (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal) := by
    calc
      _ = ‖core.embed (BoundedContinuousFunction.mkOfCompact target) -
          (core.embed (BoundedContinuousFunction.mkOfCompact target) -
            core.embed (BoundedContinuousFunction.mkOfCompact (approximation level)))‖ := by rw [sub_sub_cancel]
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add le_rfl actualTailBound)
  have incidencePositive : 0 < (xiVertexIncidenceCount system level vertex : ℝ) := by
    exact_mod_cast xiVertexIncidenceCount_positive system rulesConnected level vertex
  have coefficientPositive : 0 < pointConstant / mass.rate ^ level *
      (xiVertexIncidenceCount system level vertex : ℝ) :=
    mul_pos (div_pos pointConstantPositive (pow_pos mass.rate_positive level)) incidencePositive
  have evaluationBound := IGS.Sec31.point_square_le_of_projection_bounds
    (target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex))
    ‖core.embed (BoundedContinuousFunction.mkOfCompact target)‖
    ‖core.embed (BoundedContinuousFunction.mkOfCompact (approximation level))‖
    ((xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal)
    (pointConstant / mass.rate ^ level * (xiVertexIncidenceCount system level vertex : ℝ))
    (tailConstant * (Real.sqrt (mass.rate * resistanceRate))⁻¹ ^ level)
    coefficientPositive (norm_nonneg _) (norm_nonneg _) ENNReal.toReal_nonneg
    (mul_nonneg tailConstantPositive.le (pow_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) _))
    actualPointBound projectionBound
  have normCoefficient : 2 / (pointConstant / mass.rate ^ level *
      (xiVertexIncidenceCount system level vertex : ℝ)) =
      2 * mass.rate ^ level / (pointConstant * (xiVertexIncidenceCount system level vertex : ℝ)) := by
    field_simp
  rw [normCoefficient, IGS.Sec31.projection_point_energy_coefficient mass.rate resistanceRate
    tailConstant pointConstant (xiVertexIncidenceCount system level vertex : ℝ)
    mass.rate_positive ratePositive pointConstantPositive incidencePositive level] at evaluationBound
  exact evaluationBound

end EIGS

#print axioms EIGS.exists_xiContinuous_point_energy_bound
