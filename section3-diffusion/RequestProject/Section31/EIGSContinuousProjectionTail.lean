import RequestProject.Section31.EIGSNativeProjectionTailOfRules
import RequestProject.Section31.EIGSContinuousTailEnergy
import RequestProject.Section31.EIGSUnitPerronRecovery
import RequestProject.Section31.EIGSUnitL2Recovery
import RequestProject.Section31.EIGSHarmonicJointDensity
import RequestProject.Section31.VaryingCoreRecovery

/-! The actual discrete projection tail passes to the actual limit L² space.
The continuous harmonic extensions and unit-potential convergence are constructed
from the same rule system and resistance eigenpair. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction BigOperators

set_option maxHeartbeats 2400000

variable {K : ℕ}

theorem exists_xiContinuousHarmonic_native_tail (system : EIGSData K)
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
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (target : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)),
      xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) ≠ ⊤ →
      ∀ coarseLevel
        (extension : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)),
      (∀ vertex, extension (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) =
        xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
          renormalizationEigenpair coarseLevel
          (fun finiteVertex => target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair coarseLevel finiteVertex)) vertex) →
      ‖core.embed (BoundedContinuousFunction.mkOfCompact target) -
        core.embed (BoundedContinuousFunction.mkOfCompact extension)‖ ≤
        constant * (Real.sqrt (mass.rate * resistanceRate))⁻¹ ^ coarseLevel *
          Real.sqrt ((xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal) := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  have vectorBound : ∀ colour, resistanceVector colour ≤ ∑ edgeColour, resistanceVector edgeColour :=
    fun colour => Finset.single_le_sum (fun edgeColour _ => (vectorPositive edgeColour).le) (Finset.mem_univ colour)
  have vectorSumPositive : 0 < ∑ colour, resistanceVector colour :=
    (vectorPositive system.initCol).trans_le (vectorBound system.initCol)
  obtain ⟨constant, constantPositive, discreteTail⟩ := exists_xiUnitProjection_native_tail_for_eigenpair
    system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive mass resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair 1 zero_lt_one
  obtain ⟨normalization, normalizationPositive, unitRecovery⟩ :=
    exists_xiUnitPotential_uniform_energy_convergence_for_eigenpair system rulesConnected distancePositive
      oneColourDistance resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  refine ⟨constant * Real.sqrt (∑ colour, resistanceVector colour),
    mul_pos constantPositive (Real.sqrt_pos.2 vectorSumPositive), ?_⟩
  intro target targetFinite coarseLevel extension extensionAgreement
  have uniformConvergence : Tendsto (xiUnitPotentialUniformError system rulesConnected coarseLevel
      (fun vertex => target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair coarseLevel vertex))
      (extension ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)) atTop (nhds 0) := by
    have agreement : extension ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair =
        xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
          renormalizationEigenpair coarseLevel
          (fun vertex => target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair coarseLevel vertex)) := funext extensionAgreement
    rw [agreement]
    exact (unitRecovery coarseLevel _).1
  have strongExtension := xiUnitNativeL2_strong_of_uniform system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass coarseLevel
    (fun vertex => target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair coarseLevel vertex)) extension uniformConvergence
  have normConvergence := core.strong_norm_sub_tendsto
    (core.strong_restrict (BoundedContinuousFunction.mkOfCompact target)) strongExtension
  apply le_of_tendsto normConvergence
  filter_upwards [eventually_ge_atTop coarseLevel] with fineLevel levelsOrdered
  rw [show core.restrict fineLevel (BoundedContinuousFunction.mkOfCompact target) = _ from
    xiSpeedL2Core_restrict_eq_finiteSpeedL2 system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass (BoundedContinuousFunction.mkOfCompact target) fineLevel,
    xiUnitNativeL2_at_level system rulesConnected mass coarseLevel fineLevel levelsOrdered]
  have sampledBoundary :
      (fun vertex => target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair fineLevel
        (xiVertexInclusion system coarseLevel fineLevel levelsOrdered vertex))) =
      (fun vertex => target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair coarseLevel vertex)) := by
    funext vertex
    simp only [xiCompletionEmbedding, Function.comp_apply, xiVertexEmbedding_inclusion]
  have projectionIdentity := xiUnitEnergyProjection_eq_potentialAt system rulesConnected coarseLevel fineLevel levelsOrdered
    (fun vertex => target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair fineLevel vertex))
  rw [sampledBoundary] at projectionIdentity
  rw [← projectionIdentity]
  apply (discreteTail coarseLevel fineLevel levelsOrdered _).trans
  have energyBound := xiCompletion_sampled_unit_energy_le_extendedWeightedEnergy system rulesConnected
    lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair
    resistanceRate ratePositive resistanceVector vectorPositive (∑ colour, resistanceVector colour) vectorBound
    target targetFinite fineLevel
  have squareRootBound := Real.sqrt_le_sqrt energyBound
  rw [Real.sqrt_mul vectorSumPositive.le] at squareRootBound
  calc
    _ ≤ constant * (Real.sqrt (mass.rate * resistanceRate))⁻¹ ^ coarseLevel *
        (Real.sqrt (∑ colour, resistanceVector colour) *
          Real.sqrt ((xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal)) :=
      mul_le_mul_of_nonneg_left squareRootBound (mul_nonneg constantPositive.le (pow_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) _))
    _ = _ := by ring

end EIGS

#print axioms EIGS.exists_xiContinuousHarmonic_native_tail
