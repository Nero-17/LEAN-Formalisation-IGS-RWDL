import RequestProject.Section31.EIGSMeasuredGHP
import RequestProject.Section31.EIGSOriginalDiameterGrowth

/-! Measured GHP convergence for the original unweighted Xi graphs divided
by their own actual diameter. The common matching is the real Xi finite-level
map, with its distortion derived from the original uniform metric limit. -/
noncomputable section
namespace EIGS.MeasuredGHP
open MeasureTheory Filter Topology Metric Set TopologicalSpace
open scoped BigOperators

def normalizedMetric (Space : Type) (metric : MetricSpace Space)
    (diameterPositive : 0 < @Metric.diam Space metric.toPseudoMetricSpace univ) : MetricSpace Space :=
  @positiveScaledMetricSpace Space metric
    (@Metric.diam Space metric.toPseudoMetricSpace univ)⁻¹ (inv_pos.mpr diameterPositive)

/-- A total metric-valued wrapper permits nondependent equality transport.
Every actual graph application below proves the positive branch. -/
def normalizedMetricTotal (Space : Type) (metric : MetricSpace Space) : MetricSpace Space := by
  classical
  exact if positive : 0 < @Metric.diam Space metric.toPseudoMetricSpace univ then
    normalizedMetric Space metric positive else metric

theorem normalizedMetricTotal_eq (Space : Type) (metric : MetricSpace Space)
    (positive : 0 < @Metric.diam Space metric.toPseudoMetricSpace univ) :
    normalizedMetricTotal Space metric = normalizedMetric Space metric positive :=
  dif_pos positive

def finiteMeasuredGHPDistance {Vertex Second : Type} [Finite Vertex] [Nonempty Vertex]
    [MeasurableSpace Vertex] [DiscreteMeasurableSpace Vertex]
    [MetricSpace Second] [CompactSpace Second] [Nonempty Second]
    [MeasurableSpace Second] [BorelSpace Second]
    (metric : MetricSpace Vertex) (firstLaw : ProbabilityMeasure Vertex)
    (secondLaw : ProbabilityMeasure Second) : ℝ :=
  letI := metric
  measuredGHPDist firstLaw secondLaw

theorem normalizedMetric_scale_invariant (Space : Type) [original : MetricSpace Space]
    [CompactSpace Space] (diameterPositive : 0 < Metric.diam (univ : Set Space))
    (scale : ℝ) (scalePositive : 0 < scale) :
    normalizedMetric Space (positiveScaledMetricSpace Space scale scalePositive)
      (by rw [positiveScaledMetricSpace_diameter]; exact mul_pos scalePositive diameterPositive) =
      normalizedMetric Space original diameterPositive := by
  apply MetricSpace.ext
  ext source sink
  change (@Metric.diam Space (positiveScaledMetricSpace Space scale scalePositive).toPseudoMetricSpace univ)⁻¹ *
    (scale * dist source sink) = (Metric.diam (univ : Set Space))⁻¹ * dist source sink
  rw [positiveScaledMetricSpace_diameter, mul_inv_rev]
  field_simp

/-- The metric normalization changes neither the source Borel probabilities
nor the target weak topology; positiveScaledMetricSpace preserves topology. -/
def diameterMeasuredGHPDist {First Second : Type} [firstMetric : MetricSpace First]
    [secondMetric : MetricSpace Second] [CompactSpace First] [CompactSpace Second]
    [Nonempty First] [Nonempty Second]
    [MeasurableSpace First] [MeasurableSpace Second] [BorelSpace First] [BorelSpace Second]
    (firstLaw : ProbabilityMeasure First) (secondLaw : ProbabilityMeasure Second)
    (firstDiameterPositive : 0 < Metric.diam (univ : Set First))
    (secondDiameterPositive : 0 < Metric.diam (univ : Set Second)) : ℝ :=
  letI := normalizedMetric First firstMetric firstDiameterPositive
  letI := normalizedMetric Second secondMetric secondDiameterPositive
  measuredGHPDist firstLaw secondLaw

theorem diameterMeasuredGHPDist_nonnegative {First Second : Type} [firstMetric : MetricSpace First]
    [secondMetric : MetricSpace Second] [CompactSpace First] [CompactSpace Second]
    [Nonempty First] [Nonempty Second]
    [MeasurableSpace First] [MeasurableSpace Second] [BorelSpace First] [BorelSpace Second]
    (firstLaw : ProbabilityMeasure First) (secondLaw : ProbabilityMeasure Second)
    (firstDiameterPositive : 0 < Metric.diam (univ : Set First))
    (secondDiameterPositive : 0 < Metric.diam (univ : Set Second)) :
    0 ≤ diameterMeasuredGHPDist firstLaw secondLaw firstDiameterPositive secondDiameterPositive := by
  letI := normalizedMetric First firstMetric firstDiameterPositive
  letI := normalizedMetric Second secondMetric secondDiameterPositive
  exact measuredGHPDist_nonnegative _ _

theorem diameterMeasuredGHPDist_le_matching {First Second : Type}
    [firstMetric : MetricSpace First] [secondMetric : MetricSpace Second]
    [CompactSpace First] [CompactSpace Second] [Nonempty First] [Nonempty Second]
    [MeasurableSpace First] [MeasurableSpace Second] [BorelSpace First] [BorelSpace Second]
    (firstLaw : ProbabilityMeasure First) (secondLaw : ProbabilityMeasure Second)
    (firstDiameterPositive : 0 < Metric.diam (univ : Set First))
    (secondDiameterPositive : 0 < Metric.diam (univ : Set Second))
    (matching : First → Second) (matchingMeasurable : Measurable matching)
    (distanceError diameterError mesh : ℝ)
    (distanceErrorNonnegative : 0 ≤ distanceError) (diameterErrorNonnegative : 0 ≤ diameterError)
    (errorPositive : 0 < distanceError + diameterError) (meshNonnegative : 0 ≤ mesh)
    (diameterLower : Metric.diam (univ : Set Second) / 2 ≤ Metric.diam (univ : Set First))
    (distortion : ∀ first last, |dist first last - dist (matching first) (matching last)| ≤ distanceError)
    (diameterBound : |Metric.diam (univ : Set First) - Metric.diam (univ : Set Second)| ≤ diameterError)
    (cover : ∀ point : Second, ∃ original : First, dist point (matching original) ≤ mesh) :
    diameterMeasuredGHPDist firstLaw secondLaw firstDiameterPositive secondDiameterPositive ≤
      letI := normalizedMetric Second secondMetric secondDiameterPositive
      max ((distanceError + diameterError) / @Metric.diam Second secondMetric.toPseudoMetricSpace univ +
          mesh / @Metric.diam Second secondMetric.toPseudoMetricSpace univ)
        ((distanceError + diameterError) / @Metric.diam Second secondMetric.toPseudoMetricSpace univ +
          levyProkhorovDist (firstLaw.toMeasure.map matching) secondLaw.toMeasure) := by
  have normalizedDistortion : ∀ first last,
      |dist first last / Metric.diam (univ : Set First) -
        dist (matching first) (matching last) / Metric.diam (univ : Set Second)| ≤
        2 * ((distanceError + diameterError) / Metric.diam (univ : Set Second)) := by
    intro first last
    have bound := normalized_distance_error_le secondDiameterPositive diameterLower dist_nonneg
      (Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _))
      distanceErrorNonnegative diameterErrorNonnegative (distortion first last) diameterBound
    convert bound using 1 <;> ring
  letI := normalizedMetric First firstMetric firstDiameterPositive
  letI := normalizedMetric Second secondMetric secondDiameterPositive
  exact measuredGHPDist_le_approximate_matching firstLaw secondLaw matching matchingMeasurable
    ((distanceError + diameterError) / @Metric.diam Second secondMetric.toPseudoMetricSpace univ)
    (div_pos errorPositive secondDiameterPositive)
    (fun first last => by
      change |(@Metric.diam First firstMetric.toPseudoMetricSpace univ)⁻¹ *
          @dist First firstMetric.toDist first last -
        (@Metric.diam Second secondMetric.toPseudoMetricSpace univ)⁻¹ *
          @dist Second secondMetric.toDist (matching first) (matching last)| ≤ _
      simpa only [div_eq_mul_inv, mul_comm] using normalizedDistortion first last)
    (mesh / @Metric.diam Second secondMetric.toPseudoMetricSpace univ)
    (div_nonneg meshNonnegative secondDiameterPositive.le)
    (fun point => by
      obtain ⟨original, bound⟩ := cover point
      refine ⟨original, ?_⟩
      change (@Metric.diam Second secondMetric.toPseudoMetricSpace univ)⁻¹ *
        @dist Second secondMetric.toDist point (matching original) ≤ _
      simpa only [div_eq_mul_inv, mul_comm] using
        mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr secondDiameterPositive.le))

theorem xiNormalizedUnitMetric_eq_original {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (rate : ℝ) (ratePositive : 0 < rate) (scale : ℝ) (scalePositive : 0 < scale) (level : ℕ) :
    normalizedMetric (XiVtx system level)
      (xiLevelMetricSpace system connected (fun _ => scale⁻¹) (fun _ => inv_pos.mpr scalePositive)
        rate ratePositive level)
      (xiFiniteLevelDiameter_positive system connected (fun _ => scale⁻¹)
        (fun _ => inv_pos.mpr scalePositive) rate ratePositive level) =
    normalizedMetric (XiVtx system level)
      (xiLevelMetricSpace system connected (fun _ => (1 : ℝ)⁻¹) (fun _ => inv_pos.mpr zero_lt_one)
        1 zero_lt_one level)
      (xiFiniteLevelDiameter_positive system connected (fun _ => (1 : ℝ)⁻¹)
        (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level) := by
  letI := xiLevelMetricSpace system connected (fun _ => (1 : ℝ)⁻¹) (fun _ => inv_pos.mpr zero_lt_one)
    1 zero_lt_one level
  have factorPositive : 0 < rate⁻¹ ^ level * scale⁻¹ :=
    mul_pos (pow_pos (inv_pos.mpr ratePositive) _) (inv_pos.mpr scalePositive)
  have metricEquality : positiveScaledMetricSpace (XiVtx system level)
      (rate⁻¹ ^ level * scale⁻¹) factorPositive =
      xiLevelMetricSpace system connected (fun _ => scale⁻¹) (fun _ => inv_pos.mpr scalePositive)
        rate ratePositive level := by
    apply MetricSpace.ext
    ext first last
    change (rate⁻¹ ^ level * scale⁻¹) *
        ((1 : ℝ)⁻¹ ^ level * (XiNetwork system level).weightedDistance (fun _ => (1 : ℝ)⁻¹) first last) =
      rate⁻¹ ^ level * (XiNetwork system level).weightedDistance (fun _ => scale⁻¹) first last
    have lengthsEquality : (fun _ : Fin K => scale⁻¹) = scale⁻¹ • (fun _ : Fin K => (1 : ℝ)) := by
      ext colour
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    rw [lengthsEquality, Network.weightedDistance_smul _ _ (inv_nonneg.mpr scalePositive.le)]
    simp only [inv_one, one_pow, one_mul]
    ring
  have originalPositive := xiFiniteLevelDiameter_positive system connected (fun _ => (1 : ℝ)⁻¹)
    (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level
  have scaledPositive : 0 < @Metric.diam (XiVtx system level)
      (positiveScaledMetricSpace (XiVtx system level) (rate⁻¹ ^ level * scale⁻¹) factorPositive).toPseudoMetricSpace univ := by
    rw [positiveScaledMetricSpace_diameter]
    exact mul_pos factorPositive originalPositive
  calc
    _ = normalizedMetricTotal (XiVtx system level)
        (xiLevelMetricSpace system connected (fun _ => scale⁻¹) (fun _ => inv_pos.mpr scalePositive)
          rate ratePositive level) := (normalizedMetricTotal_eq _ _ _).symm
    _ = normalizedMetricTotal (XiVtx system level)
        (positiveScaledMetricSpace (XiVtx system level) (rate⁻¹ ^ level * scale⁻¹) factorPositive) :=
      congrArg (normalizedMetricTotal (XiVtx system level)) metricEquality.symm
    _ = normalizedMetric (XiVtx system level)
        (positiveScaledMetricSpace (XiVtx system level) (rate⁻¹ ^ level * scale⁻¹) factorPositive) scaledPositive :=
      normalizedMetricTotal_eq _ _ _
    _ = _ := normalizedMetric_scale_invariant (XiVtx system level) originalPositive
      (rate⁻¹ ^ level * scale⁻¹) factorPositive

section ActualDiameterSpaces
variable {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)

def xiDiameterTargetGHPDistance (mass : XiMassParameters system) (level : ℕ)
    (finiteMetric : MetricSpace (XiVtx system level))
    (finiteLaw : ProbabilityMeasure (XiVtx system level)) : ℝ :=
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  letI : Nonempty (XiVtx system level) :=
    ⟨by simpa only [Nat.zero_add] using xiLiftVertices system 0 level true⟩
  letI : Nonempty (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
    ⟨xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair 0 true⟩
  letI := normalizedMetric
    (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) inferInstance
    (xiCompletionDiameter_positive system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
  finiteMeasuredGHPDistance finiteMetric finiteLaw
    (xiLimitProbabilityMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)

def xiOriginalDiameterGHPDistance (mass : XiMassParameters system) (level : ℕ)
    (finiteLaw : ProbabilityMeasure (XiVtx system level)) : ℝ :=
  xiDiameterTargetGHPDistance system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass level
    (normalizedMetric (XiVtx system level)
      (xiLevelMetricSpace system connected (fun _ => (1 : ℝ)⁻¹) (fun _ => inv_pos.mpr zero_lt_one)
        1 zero_lt_one level)
      (xiFiniteLevelDiameter_positive system connected (fun _ => (1 : ℝ)⁻¹)
        (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level)) finiteLaw

def xiUnitDiameterGHPDistance (mass : XiMassParameters system) (scale : ℝ) (scalePositive : 0 < scale)
    (level : ℕ) (finiteLaw : ProbabilityMeasure (XiVtx system level)) : ℝ :=
  xiDiameterTargetGHPDistance system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass level
    (normalizedMetric (XiVtx system level)
      (xiLevelMetricSpace system connected (fun _ => scale⁻¹) (fun _ => inv_pos.mpr scalePositive)
        rate (zero_lt_one.trans rateGreaterThanOne) level)
      (xiFiniteLevelDiameter_positive system connected (fun _ => scale⁻¹)
        (fun _ => inv_pos.mpr scalePositive) rate (zero_lt_one.trans rateGreaterThanOne) level)) finiteLaw

theorem xiUnitDiameterGHPDistance_eq_original (mass : XiMassParameters system)
    (scale : ℝ) (scalePositive : 0 < scale) (level : ℕ)
    (finiteLaw : ProbabilityMeasure (XiVtx system level)) :
    xiUnitDiameterGHPDistance system connected lengths lengthsPositive rate rateGreaterThanOne
      eigenpair mass scale scalePositive level finiteLaw =
      xiOriginalDiameterGHPDistance system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass level finiteLaw :=
  congrArg (fun metric => xiDiameterTargetGHPDistance system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair mass level metric finiteLaw)
    (xiNormalizedUnitMetric_eq_original system connected rate (zero_lt_one.trans rateGreaterThanOne)
      scale scalePositive level)

theorem xiOriginalDiameterGHPDistance_nonnegative (mass : XiMassParameters system) (level : ℕ)
    (finiteLaw : ProbabilityMeasure (XiVtx system level)) :
    0 ≤ xiOriginalDiameterGHPDistance system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass level finiteLaw := by
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  letI : Nonempty (XiVtx system level) :=
    ⟨by simpa only [Nat.zero_add] using xiLiftVertices system 0 level true⟩
  letI : Nonempty (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
    ⟨xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair 0 true⟩
  letI := normalizedMetric
    (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) inferInstance
    (xiCompletionDiameter_positive system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
  letI := normalizedMetric (XiVtx system level)
    (xiLevelMetricSpace system connected (fun _ => (1 : ℝ)⁻¹) (fun _ => inv_pos.mpr zero_lt_one)
      1 zero_lt_one level)
    (xiFiniteLevelDiameter_positive system connected (fun _ => (1 : ℝ)⁻¹)
      (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level)
  exact measuredGHPDist_nonnegative _ _

def xiDiameterTargetLPDistance (mass : XiMassParameters system) (level : ℕ)
    (finiteLaw : ProbabilityMeasure (XiVtx system level)) : ℝ :=
  letI := normalizedMetric
    (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) inferInstance
    (xiCompletionDiameter_positive system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
  levyProkhorovDist
    (finiteLaw.toMeasure.map (xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair level))
    (xiLimitProbabilityMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).toMeasure

theorem xiDiameterTargetLP_tendsto_zero_of_actual_weak (mass : XiMassParameters system)
    (finiteLaws : ∀ level, ProbabilityMeasure (XiVtx system level))
    (imageLaws : ℕ → ProbabilityMeasure (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair))
    (images : ∀ level, (finiteLaws level).toMeasure.map
      (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level) = (imageLaws level).toMeasure)
    (weak : Tendsto imageLaws atTop (𝓝 (xiLimitProbabilityMeasure system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass))) :
    Tendsto (fun level => xiDiameterTargetLPDistance system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass level (finiteLaws level)) atTop (𝓝 0) := by
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  letI := normalizedMetric
    (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) inferInstance
    (xiCompletionDiameter_positive system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
  have convergence := levyProkhorovDist_tendsto_zero_of_weak imageLaws
    (xiLimitProbabilityMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass) weak
  have equality : (fun level => xiDiameterTargetLPDistance system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass level (finiteLaws level)) =
      (fun level => levyProkhorovDist (imageLaws level).toMeasure
        (xiLimitProbabilityMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).toMeasure) := by
    funext level
    change levyProkhorovDist ((finiteLaws level).toMeasure.map
      (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level)) _ = _
    rw [images level]
  rw [equality]
  exact convergence

theorem xiOriginalDiameterGHP_tendsto_zero_of_actual_weak
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalized : (∑ colour, lengths colour) = 1) (mass : XiMassParameters system)
    (finiteLaws : ∀ level, ProbabilityMeasure (XiVtx system level))
    (imageLaws : ℕ → ProbabilityMeasure (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair))
    (images : ∀ level, (finiteLaws level).toMeasure.map
      (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level) = (imageLaws level).toMeasure)
    (weak : Tendsto imageLaws atTop (𝓝 (xiLimitProbabilityMeasure system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass))) :
    Tendsto (fun level => xiOriginalDiameterGHPDistance system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass level (finiteLaws level)) atTop (𝓝 0) := by
  obtain ⟨scale, scalePositive, uniformConvergence, diameterConvergence⟩ :=
    xiSimpleGraph_normalized_diameter_limit system connected loopless unique plantingNonadjacent
      distancePositive lengths lengthsPositive rate rateGreaterThanOne normalized eigenpair
  have diameterPositive := xiCompletionDiameter_positive system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair
  have probabilityConvergence := xiDiameterTargetLP_tendsto_zero_of_actual_weak system connected
    lengths lengthsPositive rate rateGreaterThanOne eigenpair mass finiteLaws imageLaws images weak
  apply Metric.tendsto_atTop.mpr
  intro tolerance tolerancePositive
  let error := tolerance * xiCompletionDiameter system connected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) eigenpair / 8
  have errorPositive : 0 < error := by dsimp [error]; positivity
  obtain ⟨distortionThreshold, distortionBound⟩ := uniformConvergence error errorPositive
  have distortionEventually : ∀ᶠ level in atTop, ∀ first last : XiVtx system level,
      |(((XiSimpleGraph system level).dist first last : ℝ) / rate ^ level) / scale -
        xiScaledWeightedDistance system lengths rate level first last| ≤ error :=
    eventually_atTop.mpr ⟨distortionThreshold, fun level bound first last =>
      (distortionBound level bound first last).le⟩
  have diameterErrorEventually : ∀ᶠ level in atTop,
      |xiFiniteLevelDiameter system connected (fun _ => scale⁻¹) (fun _ => inv_pos.mpr scalePositive)
          rate (zero_lt_one.trans rateGreaterThanOne) level -
        xiCompletionDiameter system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair| ≤ error := by
    obtain ⟨threshold, bound⟩ := Metric.tendsto_atTop.mp diameterConvergence error errorPositive
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
    rateGreaterThanOne eigenpair).eventually (gt_mem_nhds (show
      0 < tolerance * xiCompletionDiameter system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair / 4 by positivity))
  have probabilityEventually := probabilityConvergence.eventually
    (gt_mem_nhds (show 0 < tolerance / 4 by positivity))
  apply eventually_atTop.mp
  filter_upwards [distortionEventually, diameterErrorEventually, diameterLowerEventually,
    meshEventually, probabilityEventually] with level distortion diameterError diameterLower meshBound probabilityBound
  letI := xiLevelMetricSpace system connected (fun _ => scale⁻¹) (fun _ => inv_pos.mpr scalePositive)
    rate (zero_lt_one.trans rateGreaterThanOne) level
  letI : Nonempty (XiVtx system level) :=
    ⟨by simpa only [Nat.zero_add] using xiLiftVertices system 0 level true⟩
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  letI : Nonempty (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
    ⟨xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair 0 true⟩
  have meshNonnegative : 0 ≤ xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1) := by
    obtain ⟨original, bound⟩ := xiCompletion_finite_net system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair level
      (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair 0 true)
    exact dist_nonneg.trans bound
  have comparison := diameterMeasuredGHPDist_le_matching (finiteLaws level)
    (xiLimitProbabilityMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)
    (xiFiniteLevelDiameter_positive system connected (fun _ => scale⁻¹)
      (fun _ => inv_pos.mpr scalePositive) rate (zero_lt_one.trans rateGreaterThanOne) level)
    diameterPositive
    (xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair level)
    Measurable.of_discrete error error
    (xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1))
    errorPositive.le errorPositive.le (add_pos errorPositive errorPositive) meshNonnegative diameterLower
    (fun first last => by
      rw [xiNormalizedUnitLevel_dist_eq system connected loopless rate
        (zero_lt_one.trans rateGreaterThanOne) scale scalePositive]
      have weightedDistance : dist
          (xiCompletionEmbedding system connected lengths lengthsPositive rate
            (zero_lt_one.trans rateGreaterThanOne) eigenpair level first)
          (xiCompletionEmbedding system connected lengths lengthsPositive rate
            (zero_lt_one.trans rateGreaterThanOne) eigenpair level last) =
          xiScaledWeightedDistance system lengths rate level first last := by
        letI := xiLevelMetricSpace system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) level
        exact (xiCompletionEmbedding_isometry system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair level).dist_eq first last
      rw [weightedDistance]
      exact distortion first last)
    diameterError
    (fun point => xiCompletion_finite_net system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair level point)
  change xiUnitDiameterGHPDistance system connected lengths lengthsPositive rate rateGreaterThanOne
      eigenpair mass scale scalePositive level (finiteLaws level) ≤
    max ((error + error) / xiCompletionDiameter system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair +
        (xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1)) /
          xiCompletionDiameter system connected lengths lengthsPositive rate
            (zero_lt_one.trans rateGreaterThanOne) eigenpair)
      ((error + error) / xiCompletionDiameter system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair +
        xiDiameterTargetLPDistance system connected lengths lengthsPositive rate rateGreaterThanOne
          eigenpair mass level (finiteLaws level)) at comparison
  rw [xiUnitDiameterGHPDistance_eq_original system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair mass scale scalePositive level (finiteLaws level)] at comparison
  have errorQuotient : (error + error) / xiCompletionDiameter system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair = tolerance / 4 := by
    dsimp [error]
    field_simp [ne_of_gt diameterPositive]
    <;> ring
  have meshQuotient : (xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1)) /
      xiCompletionDiameter system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair < tolerance / 4 :=
    (div_lt_iff₀ diameterPositive).mpr (by linarith only [meshBound])
  simp only [errorQuotient] at comparison
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (xiOriginalDiameterGHPDistance_nonnegative system connected
    lengths lengthsPositive rate rateGreaterThanOne eigenpair mass level (finiteLaws level))]
  exact comparison.trans_lt (max_lt_iff.mpr
    ⟨by linarith only [meshQuotient, tolerancePositive], by linarith only [probabilityBound, tolerancePositive]⟩)

theorem xiOriginalDiameterVertex_GHP_tendsto_zero
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalized : (∑ colour, lengths colour) = 1) (mass : XiMassParameters system) :
    Tendsto (fun level => xiOriginalDiameterGHPDistance system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass level (xiNativeVertexProbability system level)) atTop (𝓝 0) :=
  xiOriginalDiameterGHP_tendsto_zero_of_actual_weak system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair loopless unique plantingNonadjacent distancePositive normalized mass
    (xiNativeVertexProbability system)
    (xiVertexProbabilityMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
    (fun _ => rfl)
    (xiVertexProbabilityMeasure_tendsto system connected plantingNonadjacent distancePositive
      lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)

theorem xiOriginalDiameterSpeed_GHP_tendsto_zero
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalized : (∑ colour, lengths colour) = 1) (mass : XiMassParameters system) :
    Tendsto (fun level => xiOriginalDiameterGHPDistance system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass level (xiNativeSpeedProbability system mass level)) atTop (𝓝 0) :=
  xiOriginalDiameterGHP_tendsto_zero_of_actual_weak system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair loopless unique plantingNonadjacent distancePositive normalized mass
    (xiNativeSpeedProbability system mass)
    (xiSpeedProbabilityMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)
    (xiVertexSpeedMeasure_map system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)
    (xiSpeedProbabilityMeasure_tendsto system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)

end ActualDiameterSpaces

/-- The finite normalized metric is literally graph distance divided by the
actual original graph-metric diameter, with no Perron normalization retained. -/
theorem xiOriginalDiameter_dist_eq_graph {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (level : ℕ) (first last : XiVtx system level) :
    letI := normalizedMetric (XiVtx system level)
      (xiLevelMetricSpace system connected (fun _ => (1 : ℝ)⁻¹) (fun _ => inv_pos.mpr zero_lt_one)
        1 zero_lt_one level)
      (xiFiniteLevelDiameter_positive system connected (fun _ => (1 : ℝ)⁻¹)
        (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level)
    dist first last = ((XiSimpleGraph system level).dist first last : ℝ) /
      xiFiniteLevelDiameter system connected (fun _ => (1 : ℝ)⁻¹)
        (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level := by
  have unitDistance : @dist (XiVtx system level)
      (xiLevelMetricSpace system connected (fun _ => (1 : ℝ)⁻¹) (fun _ => inv_pos.mpr zero_lt_one)
        1 zero_lt_one level).toDist first last = ((XiSimpleGraph system level).dist first last : ℝ) := by
    simpa only [one_pow, div_one] using
      xiNormalizedUnitLevel_dist_eq system connected loopless 1 zero_lt_one 1 zero_lt_one level first last
  change (xiFiniteLevelDiameter system connected (fun _ => (1 : ℝ)⁻¹)
      (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level)⁻¹ *
      @dist (XiVtx system level)
        (xiLevelMetricSpace system connected (fun _ => (1 : ℝ)⁻¹) (fun _ => inv_pos.mpr zero_lt_one)
          1 zero_lt_one level).toDist first last = _
  rw [unitDistance]
  ring

section RuleOnlyConsumer
variable {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))

def xiCanonicalOriginalVertexGHPDistanceOfRules (level : ℕ) : ℝ :=
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  let mass := xiMassParametersOfRules system connected distancePositive
  let rateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  xiOriginalDiameterGHPDistance system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass level
    (xiNativeVertexProbability system level)

def xiCanonicalOriginalSpeedGHPDistanceOfRules (level : ℕ) : ℝ :=
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  let mass := xiMassParametersOfRules system connected distancePositive
  let rateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  xiOriginalDiameterGHPDistance system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass level
    (xiNativeSpeedProbability system mass level)

theorem xiCanonicalOriginalVertex_GHP_tendsto_zero_of_rules :
    Tendsto (xiCanonicalOriginalVertexGHPDistanceOfRules system connected loopless unique
      plantingNonadjacent distancePositive) atTop (𝓝 0) := by
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  have rateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  exact xiOriginalDiameterVertex_GHP_tendsto_zero system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair loopless unique plantingNonadjacent
    distancePositive parameters.normalized (xiMassParametersOfRules system connected distancePositive)

theorem xiCanonicalOriginalSpeed_GHP_tendsto_zero_of_rules :
    Tendsto (xiCanonicalOriginalSpeedGHPDistanceOfRules system connected loopless unique
      plantingNonadjacent distancePositive) atTop (𝓝 0) := by
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  have rateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  exact xiOriginalDiameterSpeed_GHP_tendsto_zero system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair loopless unique plantingNonadjacent
    distancePositive parameters.normalized (xiMassParametersOfRules system connected distancePositive)

end RuleOnlyConsumer
end EIGS.MeasuredGHP

#print axioms EIGS.MeasuredGHP.normalizedMetric_scale_invariant
#print axioms EIGS.MeasuredGHP.diameterMeasuredGHPDist_le_matching
#print axioms EIGS.MeasuredGHP.xiNormalizedUnitMetric_eq_original
#print axioms EIGS.MeasuredGHP.xiDiameterTargetLP_tendsto_zero_of_actual_weak
#print axioms EIGS.MeasuredGHP.xiOriginalDiameterGHP_tendsto_zero_of_actual_weak
#print axioms EIGS.MeasuredGHP.xiOriginalDiameterVertex_GHP_tendsto_zero
#print axioms EIGS.MeasuredGHP.xiOriginalDiameterSpeed_GHP_tendsto_zero
#print axioms EIGS.MeasuredGHP.xiOriginalDiameter_dist_eq_graph
#print axioms EIGS.MeasuredGHP.xiCanonicalOriginalVertex_GHP_tendsto_zero_of_rules
#print axioms EIGS.MeasuredGHP.xiCanonicalOriginalSpeed_GHP_tendsto_zero_of_rules
