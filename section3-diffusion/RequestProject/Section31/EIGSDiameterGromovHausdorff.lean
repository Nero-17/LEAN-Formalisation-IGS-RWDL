import RequestProject.Section31.EIGSDiameterLimit
import RequestProject.Section31.DiameterNormalizedGH

/-! The actual finite unit graphs normalized by their own metric diameter.
The preliminary common Perron scale is cancelled by this normalization. -/

namespace EIGS

open Filter Topology Metric Set GromovHausdorff
open scoped BigOperators

variable {K : ℕ}

noncomputable def xiDiameterFiniteGHPoint (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (rate : ℝ) (ratePositive : 0 < rate) (scale : ℝ) (scalePositive : 0 < scale) (level : ℕ) : GHSpace :=
  letI := xiLevelMetricSpace system connected (fun _ => scale⁻¹)
    (fun _ => inv_pos.mpr scalePositive) rate ratePositive level
  letI : Nonempty (XiVtx system level) :=
    ⟨by simpa only [Nat.zero_add] using xiLiftVertices system 0 level true⟩
  diameterNormalizedGHPoint (XiVtx system level)
    (xiFiniteLevelDiameter_positive system connected (fun _ => scale⁻¹)
      (fun _ => inv_pos.mpr scalePositive) rate ratePositive level)

noncomputable def xiDiameterLimitGHPoint (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths) : GHSpace :=
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  letI : Nonempty (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
    ⟨xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair 0 true⟩
  diameterNormalizedGHPoint
    (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair)
    (xiCompletionDiameter_positive system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)

theorem xiSimpleGraph_diameter_gromovHausdorff_limit (system : EIGSData K)
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
      Tendsto (xiDiameterFiniteGHPoint system connected rate
        (zero_lt_one.trans rateGreaterThanOne) scale scalePositive) atTop
        (nhds (xiDiameterLimitGHPoint system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)) := by
  obtain ⟨scale, scalePositive, uniformConvergence, diameterConvergence⟩ :=
    xiSimpleGraph_normalized_diameter_limit system connected loopless unique plantingNonadjacent
      distancePositive lengths lengthsPositive rate rateGreaterThanOne normalized eigenpair
  have diameterPositive := xiCompletionDiameter_positive system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair
  refine ⟨scale, scalePositive, Metric.tendsto_atTop.mpr ?_⟩
  intro tolerance tolerancePositive
  have errorPositive : 0 < tolerance * xiCompletionDiameter system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair / 4 := by positivity
  obtain ⟨threshold, distortionBound⟩ := uniformConvergence _ errorPositive
  have distortionEventually : ∀ᶠ level in atTop, ∀ source sink : XiVtx system level,
      |(((XiSimpleGraph system level).dist source sink : ℝ) / rate ^ level) / scale -
        xiScaledWeightedDistance system lengths rate level source sink| ≤
      tolerance * xiCompletionDiameter system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair / 4 :=
    eventually_atTop.mpr ⟨threshold, fun level bound source sink => (distortionBound level bound source sink).le⟩
  have diameterErrorEventually : ∀ᶠ level in atTop,
      |xiFiniteLevelDiameter system connected (fun _ => scale⁻¹) (fun _ => inv_pos.mpr scalePositive)
          rate (zero_lt_one.trans rateGreaterThanOne) level -
        xiCompletionDiameter system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair| ≤
      tolerance * xiCompletionDiameter system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair / 4 := by
    obtain ⟨threshold, bound⟩ := Metric.tendsto_atTop.mp diameterConvergence _ errorPositive
    exact eventually_atTop.mpr ⟨threshold, fun level levelBound => by
      simpa only [Real.dist_eq] using (bound level levelBound).le⟩
  have diameterLowerEventually : ∀ᶠ level in atTop,
      xiCompletionDiameter system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair / 2 ≤
      xiFiniteLevelDiameter system connected (fun _ => scale⁻¹) (fun _ => inv_pos.mpr scalePositive)
        rate (zero_lt_one.trans rateGreaterThanOne) level :=
    (diameterConvergence.eventually (lt_mem_nhds (show
      xiCompletionDiameter system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair / 2 <
      xiCompletionDiameter system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair by linarith only [diameterPositive]))).mono
      (fun _ bound => bound.le)
  have meshEventually := (xiFiniteNetRadius_tendsto_zero system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair).eventually (gt_mem_nhds errorPositive)
  apply eventually_atTop.mp
  filter_upwards [distortionEventually, diameterErrorEventually, diameterLowerEventually, meshEventually]
    with level distortion diameterError diameterLower meshBound
  letI := xiLevelMetricSpace system connected (fun _ => scale⁻¹)
    (fun _ => inv_pos.mpr scalePositive) rate (zero_lt_one.trans rateGreaterThanOne) level
  letI : Nonempty (XiVtx system level) :=
    ⟨by simpa only [Nat.zero_add] using xiLiftVertices system 0 level true⟩
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  letI : Nonempty (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
    ⟨xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair 0 true⟩
  have comparison := diameterNormalizedGHPoint_dist_le
    (xiFiniteLevelDiameter_positive system connected (fun _ => scale⁻¹)
      (fun _ => inv_pos.mpr scalePositive) rate (zero_lt_one.trans rateGreaterThanOne) level)
    diameterPositive
    (xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair level)
    (tolerance * xiCompletionDiameter system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair / 4)
    (tolerance * xiCompletionDiameter system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair / 4)
    (xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1))
    errorPositive.le errorPositive.le diameterLower
    (fun source sink => by
      rw [xiNormalizedUnitLevel_dist_eq system connected loopless rate
        (zero_lt_one.trans rateGreaterThanOne) scale scalePositive]
      have weightedDistance : dist
          (xiCompletionEmbedding system connected lengths lengthsPositive rate
            (zero_lt_one.trans rateGreaterThanOne) eigenpair level source)
          (xiCompletionEmbedding system connected lengths lengthsPositive rate
            (zero_lt_one.trans rateGreaterThanOne) eigenpair level sink) =
          xiScaledWeightedDistance system lengths rate level source sink := by
        letI := xiLevelMetricSpace system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) level
        exact (xiCompletionEmbedding_isometry system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair level).dist_eq source sink
      rw [weightedDistance]
      exact distortion source sink)
    diameterError
    (fun point => xiCompletion_finite_net system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair level point)
  change dist (xiDiameterFiniteGHPoint system connected rate
    (zero_lt_one.trans rateGreaterThanOne) scale scalePositive level)
    (xiDiameterLimitGHPoint system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair) ≤ _ at comparison
  have meshQuotient : (xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1)) /
      xiCompletionDiameter system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair < tolerance / 4 :=
    (div_lt_iff₀ diameterPositive).mpr (by linarith only [meshBound])
  have errorQuotient :
      ((tolerance * xiCompletionDiameter system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair / 4) +
      (tolerance * xiCompletionDiameter system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair / 4)) /
      xiCompletionDiameter system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair = tolerance / 2 := by
    field_simp [ne_of_gt diameterPositive]
    <;> ring
  change dist _ _ < tolerance
  change dist _ _ ≤ ((tolerance * xiCompletionDiameter system connected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) eigenpair / 4) +
    (tolerance * xiCompletionDiameter system connected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) eigenpair / 4)) /
    xiCompletionDiameter system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair +
    (xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1)) /
      xiCompletionDiameter system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair at comparison
  rw [errorQuotient] at comparison
  linarith only [comparison, meshQuotient, tolerancePositive]

end EIGS

#print axioms EIGS.xiSimpleGraph_diameter_gromovHausdorff_limit
