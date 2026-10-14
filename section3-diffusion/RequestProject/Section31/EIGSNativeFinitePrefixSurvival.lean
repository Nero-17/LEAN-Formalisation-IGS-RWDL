import RequestProject.Section31.EIGSNativeFloorDisplacementStay
import RequestProject.Section31.EIGSFiniteHorizonStepPathLawOfRules
import RequestProject.Section31.EIGSMovingStartApproximation
import RequestProject.Section31.FiniteSupportWeakBallSurvival

/-! The actual finite maximal displacement tail bounds failure of an entire
countable prefix, uniformly along every convergent moving start. Candidate
source; the global exit-survival consumer is a separate subsequent leaf. -/

namespace EIGS
open Set Filter Topology MeasureTheory ProbabilityTheory IGS.Sec31
open IGS.Sec31.DiscreteMarkov
open scoped Classical NNReal ENNReal UniformConvergence
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem exists_xiNativeFinitePrefixSurvival_of_rules (system : EIGSData K)
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
    letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair
    letI : MeasurableSpace parameters.LimitSpace := borel _
    letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
    let rates := xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive
      normalization normalizationPositive
    ∃ fraction : ℝ, 0 < fraction ∧ ∃ count : ℕ,
    ∀ (coarse : ℕ) (horizon : ℝ≥0),
      (horizon : ℝ) ≤ fraction *
        (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse →
    ∀ (times : ℕ → Icc (0 : ℝ) (horizon : ℝ))
      (center : parameters.LimitSpace) (starts : ∀ level, XiVtx system level),
      Tendsto (fun level => parameters.vertexEmbedding level (starts level)) atTop (𝓝 center) →
      let radius := (count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
        (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse)
      ∀ᶠ steps in atTop,
        (finiteHorizonStepLaw horizon rates parameters.vertexEmbedding
          (fun level => xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
          (fun level => (⟨Measure.dirac (starts level), inferInstance⟩ : ProbabilityMeasure (XiVtx system level)))
          (coarse + steps) : Measure
            (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates parameters.vertexEmbedding)))
          (finiteSupportDensePrefixClosedSet
            (finiteHorizonStepPaths horizon rates parameters.vertexEmbedding) times center (2 * radius))ᶜ ≤
              ENNReal.ofReal (1 / 4) := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI : MeasurableSpace parameters.LimitSpace := borel _
  letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  let rates := xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive
    normalization normalizationPositive
  dsimp only
  obtain ⟨fraction, fractionPositive, count, tails⟩ :=
    exists_xiNativeFloorDisplacementStay_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive normalization normalizationPositive
  refine ⟨fraction, fractionPositive, count, ?_⟩
  intro coarse horizon horizonBound times center starts startsConverge
  let radius := (count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
    (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse)
  have radiusPositive : 0 < radius := by
    have ruleRadiusNonnegative := xiRuleRadius_nonnegative system
      (fun colour => (parameters.lengthsPositive colour).le)
    dsimp only [radius]
    positivity
  have shifted : Tendsto (fun steps : ℕ => coarse + steps) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat coarse
  have startsNear : ∀ᶠ steps in atTop,
      dist (parameters.vertexEmbedding (coarse + steps) (starts (coarse + steps))) center ≤ radius := by
    have distanceConverges : Tendsto (fun steps : ℕ =>
        dist (parameters.vertexEmbedding (coarse + steps) (starts (coarse + steps))) center)
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_apply, dist_self] using (startsConverge.comp shifted).dist
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => center) atTop (𝓝 center))
    exact (distanceConverges.eventually (gt_mem_nhds radiusPositive)).mono (fun _ near => near.le)
  filter_upwards [startsNear] with steps sourceNear
  let transition := xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent (coarse + steps)
  let law := pathLaw transition (Measure.dirac (starts (coarse + steps)))
  let discreteHorizon := Nat.floor ((horizon : ℝ) * (rates (coarse + steps) : ℝ))
  let bad := xiAnchoredCoarseDisplacementEvent system rulesConnected parameters coarse steps 0 discreteHorizon count
  have sourceAtZero : ∀ᵐ path ∂law, path 0 = starts (coarse + steps) := by
    have mapped : ∀ᵐ vertex ∂law.map (fun path => path 0), vertex = starts (coarse + steps) := by
      change ∀ᵐ vertex ∂(pathLaw transition (Measure.dirac (starts (coarse + steps)))).map
        (fun path => path 0), vertex = starts (coarse + steps)
      rw [pathLaw_coordinate_zero]
      simp
    exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable mapped
  have tail : law.real bad ≤ (1 / 4 : ℝ) :=
    tails coarse steps horizon horizon.property horizonBound
      (⟨Measure.dirac (starts (coarse + steps)), inferInstance⟩ : ProbabilityMeasure (XiVtx system (coarse + steps)))
  have tailExtended : law bad ≤ ENNReal.ofReal (1 / 4) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top law bad)]
    exact ENNReal.ofReal_le_ofReal tail
  rw [finiteHorizonStepLaw_eq_map, Measure.map_apply
    (finiteHorizonStepMap_measurable horizon rates parameters.vertexEmbedding (coarse + steps))
    (finiteSupportDensePrefixClosedSet_isClosed
      (finiteHorizonStepPaths horizon rates parameters.vertexEmbedding) times center (2 * radius)).isOpen_compl.measurableSet]
  apply (measure_mono_ae ?_).trans tailExtended
  filter_upwards [sourceAtZero] with path initialEquality
  intro prefixFailed
  change ¬ ∀ index, dist (parameters.vertexEmbedding (coarse + steps)
    (path (Nat.floor ((times index).val * (rates (coarse + steps) : ℝ))))) center ≤ 2 * radius at prefixFailed
  obtain ⟨index, escaped⟩ := not_forall.mp prefixFailed
  have floorBound : Nat.floor ((times index).val * (rates (coarse + steps) : ℝ)) ≤ discreteHorizon :=
    Nat.floor_mono (mul_le_mul_of_nonneg_right (times index).property.2 (rates (coarse + steps)).property)
  have triangle := dist_triangle
    (parameters.vertexEmbedding (coarse + steps)
      (path (Nat.floor ((times index).val * (rates (coarse + steps) : ℝ)))))
    (parameters.vertexEmbedding (coarse + steps) (starts (coarse + steps))) center
  change ∃ observed, observed ≤ discreteHorizon ∧ radius <
    dist (parameters.vertexEmbedding (coarse + steps) (path (0 + observed)))
      (parameters.vertexEmbedding (coarse + steps) (path 0))
  refine ⟨_, floorBound, ?_⟩
  rw [Nat.zero_add, initialEquality]
  exact lt_of_not_ge (by intro notLarge; exact escaped (by linarith))

end
end EIGS

#print axioms EIGS.exists_xiNativeFinitePrefixSurvival_of_rules
