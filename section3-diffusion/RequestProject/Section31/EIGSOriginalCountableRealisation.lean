import RequestProject.Section31.EIGSOriginalMeasuredGHP
import RequestProject.Section31.FiniteProjectionCommonRealisation

/-! A common ambient for the actual original graphs divided by their own
diameters, with the weighted completion divided by its own diameter.
The input projection distortion is proved from the actual metric and diameter
limits. Neither GHP convergence alone nor equality of the normalized and
native distances is used. This file does not change the original walk clock
or identify any path-law limit. -/

namespace EIGS.MeasuredGHP
noncomputable section
open Metric Set Filter Topology
open scoped BigOperators
set_option maxHeartbeats 6000000
variable {K : ℕ}

def xiOriginalGraphDiameterMetricSpace (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected) (level : ℕ) :
    MetricSpace (XiVtx system level) :=
  normalizedMetric (XiVtx system level)
    (xiLevelMetricSpace system connected (fun _ => (1 : ℝ)⁻¹)
      (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level)
    (xiFiniteLevelDiameter_positive system connected (fun _ => (1 : ℝ)⁻¹)
      (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level)

def xiCompletionDiameterMetricSpace (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths) :
    MetricSpace (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
  normalizedMetric _ inferInstance
    (xiCompletionDiameter_positive system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)

theorem xiOriginalDiameter_projection_distortion_zero (system : EIGSData K)
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
    letI : ∀ level, MetricSpace (XiVtx system level) := xiOriginalGraphDiameterMetricSpace system connected
    letI := xiCompletionDiameterMetricSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ level in atTop, ∀ first last : XiVtx system level,
      |dist first last - dist
        (xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair level first)
        (xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair level last)| < epsilon := by
  obtain ⟨scale, scalePositive, metricLimit, diameterLimit⟩ :=
    xiSimpleGraph_normalized_diameter_limit system connected loopless unique plantingNonadjacent
      distancePositive lengths lengthsPositive rate rateGreaterThanOne normalized eigenpair
  have diameterPositive := xiCompletionDiameter_positive system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair
  letI originalRealisationCompletionCompact := xiCompletion_compactSpace system connected lengths
    lengthsPositive rate rateGreaterThanOne eigenpair
  intro epsilon positive
  let error : ℝ := epsilon * xiCompletionDiameter system connected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) eigenpair / 8
  have errorPositive : 0 < error := by dsimp [error]; positivity
  obtain ⟨threshold, metricSmall⟩ := metricLimit error errorPositive
  have metricEventually : ∀ᶠ level in atTop, ∀ first last : XiVtx system level,
      |(((XiSimpleGraph system level).dist first last : ℝ) / rate ^ level) / scale -
        xiScaledWeightedDistance system lengths rate level first last| ≤ error :=
    eventually_atTop.mpr ⟨threshold, fun level after first last => (metricSmall level after first last).le⟩
  have diameterEventually : ∀ᶠ level in atTop,
      |xiFiniteLevelDiameter system connected (fun _ => scale⁻¹) (fun _ => inv_pos.mpr scalePositive)
          rate (zero_lt_one.trans rateGreaterThanOne) level -
        xiCompletionDiameter system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair| ≤ error := by
    filter_upwards [(Metric.tendsto_nhds.mp diameterLimit) error errorPositive] with level near
    simpa only [Real.dist_eq] using near.le
  have diameterLowerEventually : ∀ᶠ level in atTop,
      xiCompletionDiameter system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair / 2 ≤
      xiFiniteLevelDiameter system connected (fun _ => scale⁻¹) (fun _ => inv_pos.mpr scalePositive)
        rate (zero_lt_one.trans rateGreaterThanOne) level :=
    (diameterLimit.eventually (lt_mem_nhds (by linarith :
      xiCompletionDiameter system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair / 2 <
      xiCompletionDiameter system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair))).mono (fun _ near => near.le)
  filter_upwards [metricEventually, diameterEventually, diameterLowerEventually]
    with level metricBound diameterBound diameterLower
  intro first last
  have nativeDistance : dist
      (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level first)
      (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level last) =
      xiScaledWeightedDistance system lengths rate level first last := by
    letI originalRealisationWeightedLevelMetric := xiLevelMetricSpace system connected lengths lengthsPositive
      rate (zero_lt_one.trans rateGreaterThanOne) level
    exact (xiCompletionEmbedding_isometry system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair level).dist_eq first last
  have nativeDistanceNonnegative : 0 ≤ xiScaledWeightedDistance system lengths rate level first last := by
    rw [← nativeDistance]
    exact dist_nonneg
  have nativeDistanceBound : xiScaledWeightedDistance system lengths rate level first last ≤
      xiCompletionDiameter system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair := by
    rw [← nativeDistance]
    exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)
  have normalizedBound := normalized_distance_error_le diameterPositive diameterLower
    nativeDistanceNonnegative nativeDistanceBound errorPositive.le errorPositive.le
    (metricBound first last) diameterBound
  have scaledDistance : @dist (XiVtx system level)
      (xiLevelMetricSpace system connected (fun _ => scale⁻¹) (fun _ => inv_pos.mpr scalePositive)
        rate (zero_lt_one.trans rateGreaterThanOne) level).toDist first last =
      (((XiSimpleGraph system level).dist first last : ℝ) / rate ^ level) / scale :=
    xiNormalizedUnitLevel_dist_eq system connected loopless rate (zero_lt_one.trans rateGreaterThanOne)
      scale scalePositive level first last
  have metricEquality := xiNormalizedUnitMetric_eq_original system connected rate
    (zero_lt_one.trans rateGreaterThanOne) scale scalePositive level
  change |@dist (XiVtx system level) (xiOriginalGraphDiameterMetricSpace system connected level).toDist first last -
    @dist (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair)
      (xiCompletionDiameterMetricSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair).toDist
      (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level first)
      (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level last)| < epsilon
  unfold xiOriginalGraphDiameterMetricSpace
  rw [← metricEquality]
  change |(xiFiniteLevelDiameter system connected (fun _ => scale⁻¹) (fun _ => inv_pos.mpr scalePositive)
      rate (zero_lt_one.trans rateGreaterThanOne) level)⁻¹ *
      @dist (XiVtx system level) (xiLevelMetricSpace system connected (fun _ => scale⁻¹)
        (fun _ => inv_pos.mpr scalePositive) rate (zero_lt_one.trans rateGreaterThanOne) level).toDist first last -
    (xiCompletionDiameter system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair)⁻¹ *
      dist (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level first)
        (xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair level last)| < epsilon
  rw [scaledDistance, nativeDistance]
  have quotientIdentity : 2 * (error + error) /
      xiCompletionDiameter system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair = epsilon / 2 := by
    dsimp only [error]
    field_simp [diameterPositive.ne']
    <;> ring
  have finalBound : |((((XiSimpleGraph system level).dist first last : ℝ) / rate ^ level) / scale) /
        xiFiniteLevelDiameter system connected (fun _ => scale⁻¹) (fun _ => inv_pos.mpr scalePositive)
          rate (zero_lt_one.trans rateGreaterThanOne) level -
      xiScaledWeightedDistance system lengths rate level first last /
        xiCompletionDiameter system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair| ≤ epsilon / 2 := by
    rw [← quotientIdentity]
    exact normalizedBound
  simpa only [div_eq_mul_inv, mul_comm] using finalBound.trans_lt (half_lt_self positive)

theorem exists_xiOriginalDiameter_compact_common_realisation (system : EIGSData K)
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
    letI : ∀ level, MetricSpace (XiVtx system level) := xiOriginalGraphDiameterMetricSpace system connected
    letI := xiCompletionDiameterMetricSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
    ∃ (Ambient : Type) (ambientMetric : MetricSpace Ambient),
      letI := ambientMetric
      CompleteSpace Ambient ∧ CompactSpace Ambient ∧
      ∃ target : XiMetricCompletion system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair → Ambient, Isometry target ∧
      ∃ sources : ∀ level, XiVtx system level → Ambient,
        (∀ level, Isometry (sources level)) ∧
        ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ level in atTop, ∀ point,
          dist (sources level point) (target (xiCompletionEmbedding system connected lengths lengthsPositive rate
            (zero_lt_one.trans rateGreaterThanOne) eigenpair level point)) < epsilon := by
  letI originalCountableCompletionCompact := xiCompletion_compactSpace system connected lengths lengthsPositive
    rate rateGreaterThanOne eigenpair
  letI originalCountableVertexNonempty : ∀ level, Nonempty (XiVtx system level) := fun level =>
    ⟨by simpa only [Nat.zero_add] using xiLiftVertices system 0 level true⟩
  letI originalCountableCompletionNonempty : Nonempty (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
    ⟨xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair 0 true⟩
  letI originalCountableVertexMetric : ∀ level, MetricSpace (XiVtx system level) :=
    xiOriginalGraphDiameterMetricSpace system connected
  letI originalCountableCompletionMetric := xiCompletionDiameterMetricSpace system connected lengths lengthsPositive
    rate rateGreaterThanOne eigenpair
  obtain ⟨Ambient, ambientMetric, complete, compact, target, targetIsometry, sources, sourceIsometry,
      radii, radiiPositive, radiiZero, displacement, convergence⟩ :=
    CountableRealisation.exists_compact_common_realisation_of_projection_distortion (XiVtx system)
      (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair)
      (xiOriginalDiameter_projection_distortion_zero system connected loopless unique plantingNonadjacent
        distancePositive lengths lengthsPositive rate rateGreaterThanOne normalized eigenpair)
  exact ⟨Ambient, ambientMetric, complete, compact, target, targetIsometry, sources, sourceIsometry, convergence⟩

end
end EIGS.MeasuredGHP

#print axioms EIGS.MeasuredGHP.xiOriginalDiameter_projection_distortion_zero
#print axioms EIGS.MeasuredGHP.exists_xiOriginalDiameter_compact_common_realisation
