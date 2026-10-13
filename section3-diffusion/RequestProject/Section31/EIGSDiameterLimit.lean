import RequestProject.Section31.EIGSFiniteDiameter
import RequestProject.Section31.PositiveScaledMetric

/-! Actual finite-level diameters and the original-unit diameter limit. -/

namespace EIGS

open Filter Topology Metric Set
open scoped BigOperators

variable {K : ℕ}

noncomputable def xiFiniteLevelDiameter (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (ratePositive : 0 < rate) (level : ℕ) : ℝ :=
  letI := xiLevelMetricSpace system connected lengths lengthsPositive rate ratePositive level
  Metric.diam (univ : Set (XiVtx system level))

noncomputable def xiCompletionDiameter (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (ratePositive : 0 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths) : ℝ :=
  Metric.diam (univ : Set (XiMetricCompletion system connected lengths lengthsPositive rate ratePositive eigenpair))

theorem xiFiniteLevelDiameter_positive (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (ratePositive : 0 < rate) (level : ℕ) :
    0 < xiFiniteLevelDiameter system connected lengths lengthsPositive rate ratePositive level := by
  letI := xiLevelMetricSpace system connected lengths lengthsPositive rate ratePositive level
  have vertexNontrivial : ∀ level, Nontrivial (XiVtx system level) := by
    intro level
    induction level with
    | zero => exact inferInstanceAs (Nontrivial Bool)
    | succ level induction_hypothesis =>
      change Nontrivial (XiVtx system level ⊕ _)
      rcases induction_hypothesis.exists_pair_ne with ⟨first, second, distinct⟩
      exact ⟨⟨Sum.inl first, Sum.inl second, fun equality => distinct (Sum.inl.inj equality)⟩⟩
  letI := vertexNontrivial level
  exact Metric.diam_pos Set.nontrivial_univ Set.finite_univ.isBounded

theorem xiCompletionDiameter_positive (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths) :
    0 < xiCompletionDiameter system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair := by
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  letI := xiLevelMetricSpace system connected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) 0
  have pointsDistinct : xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair 0 true ≠
      xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair 0 false := by
    exact (xiCompletionEmbedding_isometry system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair 0).injective.ne (by
        change (true : Bool) ≠ false
        decide)
  exact (dist_pos.mpr pointsDistinct).trans_le
    (Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _))

theorem xiFiniteLevelDiameter_tendsto (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths) :
    Tendsto (xiFiniteLevelDiameter system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne)) atTop
      (nhds (xiCompletionDiameter system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair)) := by
  apply Metric.tendsto_atTop.mpr
  intro tolerance tolerancePositive
  have smallRadius := (xiFiniteNetRadius_tendsto_zero system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair).eventually (gt_mem_nhds (show (0 : ℝ) < tolerance / 2 by positivity))
  obtain ⟨threshold, radiusBound⟩ := eventually_atTop.mp smallRadius
  refine ⟨threshold, ?_⟩
  intro level levelBound
  rw [Real.dist_eq]
  have diameterBound := xiFiniteLevel_diameter_error_le system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair level
  change |xiFiniteLevelDiameter system connected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) level -
    xiCompletionDiameter system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair| ≤ _ at diameterBound
  linarith only [diameterBound, radiusBound level levelBound]

theorem xiSimpleGraph_normalized_diameter_limit (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate) (normalized : (∑ colour, lengths colour) = 1)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths) :
    ∃ scale : ℝ, ∃ scalePositive : 0 < scale,
      (∀ tolerance > 0, ∃ threshold, ∀ level ≥ threshold, ∀ source sink : XiVtx system level,
        |(((XiSimpleGraph system level).dist source sink : ℝ) / rate ^ level) / scale -
          xiScaledWeightedDistance system lengths rate level source sink| < tolerance) ∧
      Tendsto (xiFiniteLevelDiameter system connected (fun _ => scale⁻¹)
        (fun _ => inv_pos.mpr scalePositive) rate (zero_lt_one.trans rateGreaterThanOne)) atTop
        (nhds (xiCompletionDiameter system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair)) := by
  obtain ⟨scale, scalePositive, uniformConvergence⟩ := xiSimpleGraph_uniform_metric_limit system connected
    loopless unique plantingNonadjacent distancePositive lengths lengthsPositive rate rateGreaterThanOne normalized eigenpair
  have scaledConvergence : ∀ tolerance > 0, ∃ threshold, ∀ level ≥ threshold,
      ∀ source sink : XiVtx system level,
        |(((XiSimpleGraph system level).dist source sink : ℝ) / rate ^ level) / scale -
          xiScaledWeightedDistance system lengths rate level source sink| < tolerance := by
    intro tolerance tolerancePositive
    obtain ⟨threshold, bound⟩ := uniformConvergence (tolerance * scale) (mul_pos tolerancePositive scalePositive)
    refine ⟨threshold, ?_⟩
    intro level levelBound source sink
    have identity :
        (((XiSimpleGraph system level).dist source sink : ℝ) / rate ^ level) / scale -
          xiScaledWeightedDistance system lengths rate level source sink =
        (((XiSimpleGraph system level).dist source sink : ℝ) / rate ^ level -
          scale * xiScaledWeightedDistance system lengths rate level source sink) / scale := by
      field_simp <;> ring
    rw [identity, abs_div, abs_of_pos scalePositive]
    exact (div_lt_iff₀ scalePositive).mpr (bound level levelBound source sink)
  refine ⟨scale, scalePositive, scaledConvergence, Metric.tendsto_atTop.mpr ?_⟩
  intro tolerance tolerancePositive
  obtain ⟨distortionThreshold, distortionBound⟩ := scaledConvergence (tolerance / 2) (by positivity)
  have smallRadius := (xiFiniteNetRadius_tendsto_zero system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair).eventually (gt_mem_nhds (show (0 : ℝ) < tolerance / 4 by positivity))
  obtain ⟨radiusThreshold, radiusBound⟩ := eventually_atTop.mp smallRadius
  refine ⟨max distortionThreshold radiusThreshold, ?_⟩
  intro level levelBound
  have finiteComparison := finite_diameter_distortion_le
    (xiLevelMetricSpace system connected (fun _ => scale⁻¹) (fun _ => inv_pos.mpr scalePositive)
      rate (zero_lt_one.trans rateGreaterThanOne) level)
    (xiLevelMetricSpace system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) level)
    (show 0 ≤ tolerance / 2 by positivity) (fun source sink => by
      rw [xiNormalizedUnitLevel_dist_eq system connected loopless rate
        (zero_lt_one.trans rateGreaterThanOne) scale scalePositive]
      exact (distortionBound level ((le_max_left _ _).trans levelBound) source sink).le)
  have weightedComparison := xiFiniteLevel_diameter_error_le system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair level
  change |xiFiniteLevelDiameter system connected (fun _ => scale⁻¹)
    (fun _ => inv_pos.mpr scalePositive) rate (zero_lt_one.trans rateGreaterThanOne) level -
    xiFiniteLevelDiameter system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) level| ≤ tolerance / 2 at finiteComparison
  change |xiFiniteLevelDiameter system connected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) level -
    xiCompletionDiameter system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair| ≤ _ at weightedComparison
  rw [Real.dist_eq]
  have triangle := abs_sub_le
    (xiFiniteLevelDiameter system connected (fun _ => scale⁻¹) (fun _ => inv_pos.mpr scalePositive)
      rate (zero_lt_one.trans rateGreaterThanOne) level)
    (xiFiniteLevelDiameter system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) level)
    (xiCompletionDiameter system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair)
  linarith only [finiteComparison, weightedComparison, triangle,
    radiusBound level ((le_max_right _ _).trans levelBound)]

end EIGS

#print axioms EIGS.xiCompletionDiameter_positive
#print axioms EIGS.xiFiniteLevelDiameter_positive
#print axioms EIGS.xiFiniteLevelDiameter_tendsto
#print axioms EIGS.xiSimpleGraph_normalized_diameter_limit
