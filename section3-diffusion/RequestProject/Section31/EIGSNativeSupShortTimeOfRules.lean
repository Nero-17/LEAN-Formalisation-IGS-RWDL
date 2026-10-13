import RequestProject.Section31.EIGSNativeSupTransition
import RequestProject.Section31.EIGSAsymptoticPathModulus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Uniform short-time approximation of continuous functions by the actual
floor-clock Xi transition operators. The proof uses the native all-start
path-modulus probability estimate. A measurable two-endpoint bad event is
contained in the full modulus bad event, so no extra measurability premise
for the latter is needed. -/

namespace IGS.Sec31

open MeasureTheory Set Filter
open scoped Topology ENNReal

theorem integral_abs_le_small_add_bad_probability {Sample : Type*} [MeasurableSpace Sample]
    (law : Measure Sample) [IsProbabilityMeasure law] (values : Sample → ℝ)
    (valuesIntegrable : Integrable values law) (bad : Set Sample) (badMeasurable : MeasurableSet bad)
    (small bound : ℝ) (smallNonnegative : 0 ≤ small)
    (outsideBound : ∀ sample ∉ bad, |values sample| ≤ small)
    (globalBound : ∀ sample, |values sample| ≤ bound) :
    |∫ sample, values sample ∂law| ≤ small + bound * (law bad).toReal := by
  have upperIntegrable : Integrable (fun sample => small + bad.indicator (fun _ => bound) sample) law :=
    (integrable_const small).add ((integrable_const bound).indicator badMeasurable)
  calc
    |∫ sample, values sample ∂law| ≤ ∫ sample, |values sample| ∂law := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm values
    _ ≤ ∫ sample, small + bad.indicator (fun _ => bound) sample ∂law := by
      apply integral_mono valuesIntegrable.abs upperIntegrable
      intro sample
      change |values sample| ≤ small + bad.indicator (fun _ => bound) sample
      by_cases membership : sample ∈ bad
      · rw [Set.indicator_of_mem membership]
        exact (globalBound sample).trans (le_add_of_nonneg_left smallNonnegative)
      · rw [Set.indicator_of_notMem membership, add_zero]
        exact outsideBound sample membership
    _ = small + bound * (law bad).toReal := by
      rw [integral_add (integrable_const small)
        ((integrable_const bound).indicator badMeasurable), integral_const,
          integral_indicator badMeasurable, setIntegral_const]
      simp only [smul_eq_mul, measureReal_def, measure_univ, ENNReal.toReal_one, one_mul]
      ring

end IGS.Sec31

namespace EIGS

open MeasureTheory ProbabilityTheory Filter Topology Set
open IGS.Sec31 IGS.Sec31.DiscreteMarkov
open scoped Classical NNReal ENNReal UniformConvergence
noncomputable section
set_option maxHeartbeats 4000000

variable {K : ℕ}

theorem xiNativeSupTransition_short_time_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    letI : CompactSpace parameters.LimitSpace :=
      xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
    ∀ (function : C(parameters.LimitSpace, ℝ)) (error : ℝ), 0 < error →
      ∃ window : ℝ, 0 < window ∧ window < 1 ∧ ∃ threshold : ℕ,
        ∀ level ≥ threshold, ∀ time : ℝ, 0 ≤ time → time ≤ window →
          ‖(xiNativeSupTransition system rulesConnected level ^
              Nat.floor (time * xiNativeFiniteJumpRate system level
                (system.resistanceSpectralRadius rulesConnected distancePositive) normalization))
              (fun vertex => function (parameters.vertexEmbedding level vertex)) -
            (fun vertex => function (parameters.vertexEmbedding level vertex))‖ ≤ error := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI : CompactSpace parameters.LimitSpace :=
    xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  dsimp only
  intro function error errorPositive
  obtain ⟨spatialWindow, spatialWindowPositive, functionSmall⟩ :=
    Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous function.continuous)
      (error / 2) (by positivity)
  have probabilityPositive : 0 < error / (4 * ‖function‖ + 4) := by positivity
  obtain ⟨coarse, window, windowPositive, windowSmall, modulusBound⟩ :=
    exists_xiAsymptoticPathModulus_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive normalization normalizationPositive
        1 (spatialWindow / 2) (error / (4 * ‖function‖ + 4)) 1
          (by norm_num) (by positivity) probabilityPositive (by norm_num)
  refine ⟨window, windowPositive, windowSmall, coarse, ?_⟩
  intro level levelLarge time timeNonnegative timeSmall
  obtain ⟨steps, rfl⟩ := Nat.exists_eq_add_of_le levelLarge
  let values : XiVtx system (coarse + steps) → ℝ :=
    fun vertex => function (parameters.vertexEmbedding (coarse + steps) vertex)
  let jumps := Nat.floor (time * xiNativeFiniteJumpRate system (coarse + steps)
    (system.resistanceSpectralRadius rulesConnected distancePositive) normalization)
  apply (pi_norm_le_iff_of_nonneg errorPositive.le).mpr
  intro source
  change ‖(xiNativeSupTransition system rulesConnected (coarse + steps) ^ jumps) values source - values source‖ ≤ error
  rw [Real.norm_eq_abs]
  let kernel := xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent (coarse + steps)
  let law := pathLaw kernel (Measure.dirac source)
  letI : IsProbabilityMeasure law := by dsimp only [law, kernel]; infer_instance
  let bad : Set (ℕ → XiVtx system (coarse + steps)) :=
    {path | spatialWindow / 2 < dist (parameters.vertexEmbedding (coarse + steps) (path 0))
      (parameters.vertexEmbedding (coarse + steps) (path jumps))}
  have distanceMeasurable : Measurable (fun path : ℕ → XiVtx system (coarse + steps) =>
      dist (parameters.vertexEmbedding (coarse + steps) (path 0))
        (parameters.vertexEmbedding (coarse + steps) (path jumps))) := by
    have pairMeasurable : Measurable (fun path : ℕ → XiVtx system (coarse + steps) =>
        (path 0, path jumps)) :=
      (measurable_pi_apply 0).prodMk (measurable_pi_apply jumps)
    have endpointDistanceMeasurable : Measurable
        (fun endpoints : XiVtx system (coarse + steps) × XiVtx system (coarse + steps) =>
          dist (parameters.vertexEmbedding (coarse + steps) endpoints.1)
            (parameters.vertexEmbedding (coarse + steps) endpoints.2)) :=
      measurable_of_countable _
    simpa only [Function.comp_apply] using endpointDistanceMeasurable.comp pairMeasurable
  have badMeasurable : MeasurableSet bad := measurableSet_lt measurable_const distanceMeasurable
  have badSubset : bad ⊆ xiActualPathModulusEvent system rulesConnected distancePositive parameters
      normalization (coarse + steps) 1 window (spatialWindow / 2) := by
    intro path membership
    refine ⟨0, by norm_num, time, ⟨timeNonnegative, timeSmall.trans windowSmall.le⟩, ?_, ?_⟩
    · simpa only [sub_zero, abs_of_nonneg timeNonnegative] using timeSmall
    · simpa only [zero_mul, Nat.floor_zero] using membership
  have probabilityBound : (law bad).toReal ≤ error / (4 * ‖function‖ + 4) := by
    have nativeBound := modulusBound steps (⟨Measure.dirac source, inferInstance⟩ :
      ProbabilityMeasure (XiVtx system (coarse + steps)))
    apply (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono badSubset)).trans
    simpa only [law, kernel, parameters, xiNativeDiscreteKernel] using nativeBound.le
  have endpointIntegrable (index : ℕ) : Integrable (fun path => values (path index)) law := by
    apply Integrable.of_bound
      ((measurable_of_countable values).comp (measurable_pi_apply index)).aestronglyMeasurable ‖function‖
    exact Eventually.of_forall fun path =>
      function.norm_coe_le_norm (parameters.vertexEmbedding (coarse + steps) (path index))
  have endpointExpectation (index : ℕ) :
      (∫ path, values (path index) ∂law) =
        (xiNativeSupTransition system rulesConnected (coarse + steps) ^ index) values source :=
    xiNativeSupTransition_pathLaw_endpoint_expectation system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent (coarse + steps) index values source
  have expectationDifference : (∫ path, values (path jumps) - values (path 0) ∂law) =
      (xiNativeSupTransition system rulesConnected (coarse + steps) ^ jumps) values source - values source := by
    rw [integral_sub (endpointIntegrable jumps) (endpointIntegrable 0), endpointExpectation, endpointExpectation]
    simp only [pow_zero, ContinuousLinearMap.one_apply]
  rw [← expectationDifference]
  have globalBound (path : ℕ → XiVtx system (coarse + steps)) :
      |values (path jumps) - values (path 0)| ≤ 2 * ‖function‖ := by
    have triangle := norm_sub_le (values (path jumps)) (values (path 0))
    rw [Real.norm_eq_abs] at triangle
    apply triangle.trans
    calc
      ‖values (path jumps)‖ + ‖values (path 0)‖ ≤ ‖function‖ + ‖function‖ :=
        add_le_add (function.norm_coe_le_norm _) (function.norm_coe_le_norm _)
      _ = 2 * ‖function‖ := by ring
  have outsideBound (path : ℕ → XiVtx system (coarse + steps)) (outside : path ∉ bad) :
      |values (path jumps) - values (path 0)| ≤ error / 2 := by
    have close : dist (parameters.vertexEmbedding (coarse + steps) (path 0))
        (parameters.vertexEmbedding (coarse + steps) (path jumps)) < spatialWindow :=
      (le_of_not_gt outside).trans_lt (half_lt_self spatialWindowPositive)
    have small := functionSmall close
    simpa only [Real.dist_eq, abs_sub_comm] using small.le
  have budgetBound : 2 * ‖function‖ * (error / (4 * ‖function‖ + 4)) ≤ error / 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 4 * ‖function‖ + 4)).mpr
    nlinarith
  have boundNonnegative : 0 ≤ (2 : ℝ) * ‖function‖ :=
    mul_nonneg (by norm_num) (norm_nonneg function)
  calc
    |∫ path, values (path jumps) - values (path 0) ∂law| ≤
        error / 2 + (2 * ‖function‖) * (law bad).toReal :=
      integral_abs_le_small_add_bad_probability law _
        ((endpointIntegrable jumps).sub (endpointIntegrable 0)) bad badMeasurable
          (error / 2) (2 * ‖function‖) (by positivity) outsideBound globalBound
    _ ≤ error / 2 + (2 * ‖function‖) * (error / (4 * ‖function‖ + 4)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left probabilityBound boundNonnegative)
    _ ≤ error := by linarith

end
end EIGS

#print axioms IGS.Sec31.integral_abs_le_small_add_bad_probability
#print axioms EIGS.xiNativeSupTransition_short_time_of_rules
