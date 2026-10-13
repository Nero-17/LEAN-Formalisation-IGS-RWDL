import RequestProject.Section31.EIGSCanonicalMeasureLimit
import RequestProject.Section31.EIGSFiniteHausdorff
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! The standard common-isometric-embedding formula for measured GHP distance,
and genuine metric-measure approximation of the deterministic Xi completion.
The concrete finite metrics in this file are the actual compatible Perron
weighted metrics. Transferring the original unweighted diameter-normalized
metrics requires an additional measured distortion/gluing argument. -/
noncomputable section

namespace EIGS.MeasuredGHP
open MeasureTheory Filter Topology Metric Set TopologicalSpace

/-- A genuine common metric realization. The ambient space is allowed to vary;
it is not fixed to the supplied Xi completion. -/
structure CommonMetricEmbedding (First Second : Type)
    [MetricSpace First] [MetricSpace Second] where
  Ambient : Type
  metric : MetricSpace Ambient
  first : First → Ambient
  second : Second → Ambient
  first_isometry : letI := metric; Isometry first
  second_isometry : letI := metric; Isometry second

def productEmbedding (First Second : Type) [MetricSpace First] [MetricSpace Second]
    [Nonempty First] [Nonempty Second] : CommonMetricEmbedding First Second where
  Ambient := First × Second
  metric := inferInstance
  first := fun point => (point, Classical.choice (inferInstance : Nonempty Second))
  second := fun point => (Classical.choice (inferInstance : Nonempty First), point)
  first_isometry := by
    apply Isometry.of_dist_eq
    intro first last
    simp
  second_isometry := by
    apply Isometry.of_dist_eq
    intro first last
    simp

instance commonMetricEmbeddingNonempty (First Second : Type)
    [MetricSpace First] [MetricSpace Second] [Nonempty First] [Nonempty Second] :
    Nonempty (CommonMetricEmbedding First Second) := ⟨productEmbedding First Second⟩

/-- The usual maximum convention for the common-realization GHP cost.
Compactness and nonemptiness ensure the Hausdorff term is a genuine finite
distance. Borel source structures make the isometric measure images genuine. -/
def commonCost {First Second : Type} [MetricSpace First] [MetricSpace Second]
    [CompactSpace First] [CompactSpace Second] [Nonempty First] [Nonempty Second]
    [MeasurableSpace First] [MeasurableSpace Second] [BorelSpace First] [BorelSpace Second]
    (realization : CommonMetricEmbedding First Second)
    (firstLaw : ProbabilityMeasure First) (secondLaw : ProbabilityMeasure Second) : ℝ :=
  letI := realization.metric
  letI : MeasurableSpace realization.Ambient := borel _
  max (hausdorffDist (range realization.first) (range realization.second))
    (levyProkhorovDist (firstLaw.toMeasure.map realization.first)
      (secondLaw.toMeasure.map realization.second))

/-- The standard measured Gromov--Hausdorff--Prokhorov distance formula:
the infimum over all common metric spaces and both isometric embeddings.
No metric axioms on a quotient of measured spaces are asserted here. -/
def measuredGHPDist {First Second : Type} [MetricSpace First] [MetricSpace Second]
    [CompactSpace First] [CompactSpace Second] [Nonempty First] [Nonempty Second]
    [MeasurableSpace First] [MeasurableSpace Second] [BorelSpace First] [BorelSpace Second]
    (firstLaw : ProbabilityMeasure First) (secondLaw : ProbabilityMeasure Second) : ℝ :=
  sInf (range (fun realization : CommonMetricEmbedding First Second =>
    commonCost realization firstLaw secondLaw))

theorem commonCost_nonnegative {First Second : Type} [MetricSpace First] [MetricSpace Second]
    [CompactSpace First] [CompactSpace Second] [Nonempty First] [Nonempty Second]
    [MeasurableSpace First] [MeasurableSpace Second] [BorelSpace First] [BorelSpace Second]
    (realization : CommonMetricEmbedding First Second)
    (firstLaw : ProbabilityMeasure First) (secondLaw : ProbabilityMeasure Second) :
    0 ≤ commonCost realization firstLaw secondLaw := by
  letI := realization.metric
  letI : MeasurableSpace realization.Ambient := borel _
  exact le_max_of_le_left hausdorffDist_nonneg

theorem measuredGHPDist_nonnegative {First Second : Type}
    [MetricSpace First] [MetricSpace Second]
    [CompactSpace First] [CompactSpace Second] [Nonempty First] [Nonempty Second]
    [MeasurableSpace First] [MeasurableSpace Second] [BorelSpace First] [BorelSpace Second]
    (firstLaw : ProbabilityMeasure First) (secondLaw : ProbabilityMeasure Second) :
    0 ≤ measuredGHPDist firstLaw secondLaw := by
  apply le_csInf (range_nonempty _)
  rintro _ ⟨realization, rfl⟩
  exact commonCost_nonnegative realization firstLaw secondLaw

/-- Every actual common isometric realization bounds the standard infimum. -/
theorem measuredGHPDist_le_commonCost {First Second : Type}
    [MetricSpace First] [MetricSpace Second]
    [CompactSpace First] [CompactSpace Second] [Nonempty First] [Nonempty Second]
    [MeasurableSpace First] [MeasurableSpace Second] [BorelSpace First] [BorelSpace Second]
    (firstLaw : ProbabilityMeasure First) (secondLaw : ProbabilityMeasure Second)
    (realization : CommonMetricEmbedding First Second) :
    measuredGHPDist firstLaw secondLaw ≤ commonCost realization firstLaw secondLaw := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨otherRealization, rfl⟩
    exact commonCost_nonnegative otherRealization firstLaw secondLaw
  · exact mem_range_self realization

theorem levyProkhorovDist_tendsto_zero_of_weak {Ambient : Type*}
    [MetricSpace Ambient] [SeparableSpace Ambient] [MeasurableSpace Ambient] [BorelSpace Ambient]
    (probabilities : ℕ → ProbabilityMeasure Ambient) (limit : ProbabilityMeasure Ambient)
    (weak : Tendsto probabilities atTop (𝓝 limit)) :
    Tendsto (fun level => levyProkhorovDist (probabilities level).toMeasure limit.toMeasure)
      atTop (𝓝 0) := by
  have convergence :=
    (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.tendsto limit).comp weak
  exact tendsto_iff_dist_tendsto_zero.mp convergence

/-- Isometric Borel images cannot increase the genuine LP extended distance. -/
theorem levyProkhorovEDist_map_isometry_le {First Second : Type*}
    [MetricSpace First] [MetricSpace Second]
    [MeasurableSpace First] [MeasurableSpace Second] [BorelSpace First] [BorelSpace Second]
    (firstLaw secondLaw : Measure First) (embedding : First → Second)
    (isometric : Isometry embedding) :
    levyProkhorovEDist (firstLaw.map embedding) (secondLaw.map embedding) ≤
      levyProkhorovEDist firstLaw secondLaw := by
  have measurableEmbedding := isometric.continuous.measurable
  apply levyProkhorovEDist_le_of_forall
  intro radius measurableSet greater finite measurable
  have pullbackThickening : thickening radius.toReal (embedding ⁻¹' measurableSet) ⊆
      embedding ⁻¹' thickening radius.toReal measurableSet := by
    intro point close
    obtain ⟨other, member, bound⟩ := mem_thickening_iff.mp close
    apply mem_thickening_iff.mpr
    exact ⟨embedding other, member, by rw [isometric.dist_eq]; exact bound⟩
  constructor
  · rw [Measure.map_apply measurableEmbedding measurable,
      Measure.map_apply measurableEmbedding isOpen_thickening.measurableSet]
    exact (left_measure_le_of_levyProkhorovEDist_lt greater
      (measurableEmbedding measurable)).trans
      (add_le_add (measure_mono pullbackThickening) (le_refl radius))
  · rw [Measure.map_apply measurableEmbedding measurable,
      Measure.map_apply measurableEmbedding isOpen_thickening.measurableSet]
    exact (right_measure_le_of_levyProkhorovEDist_lt greater
      (measurableEmbedding measurable)).trans
      (add_le_add (measure_mono pullbackThickening) (le_refl radius))

theorem levyProkhorovDist_map_isometry_le {First Second : Type*}
    [MetricSpace First] [MetricSpace Second]
    [MeasurableSpace First] [MeasurableSpace Second] [BorelSpace First] [BorelSpace Second]
    (firstLaw secondLaw : Measure First) [IsFiniteMeasure firstLaw] [IsFiniteMeasure secondLaw]
    (embedding : First → Second) (isometric : Isometry embedding) :
    levyProkhorovDist (firstLaw.map embedding) (secondLaw.map embedding) ≤
      levyProkhorovDist firstLaw secondLaw :=
  ENNReal.toReal_mono (levyProkhorovEDist_ne_top firstLaw secondLaw)
    (levyProkhorovEDist_map_isometry_le firstLaw secondLaw embedding isometric)

/-- A genuine coupling bound for two measurable images of the same probability.
The common random point itself supplies the coupling; no LP bound is assumed. -/
theorem levyProkhorovDist_same_source_le {Domain Ambient : Type*}
    [MeasurableSpace Domain] [MetricSpace Ambient] [MeasurableSpace Ambient] [BorelSpace Ambient]
    (probability : ProbabilityMeasure Domain) (first second : Domain → Ambient)
    (firstMeasurable : Measurable first) (secondMeasurable : Measurable second)
    (radius : ℝ) (radiusNonnegative : 0 ≤ radius)
    (close : ∀ point, dist (first point) (second point) ≤ radius) :
    levyProkhorovDist (probability.toMeasure.map first) (probability.toMeasure.map second) ≤ radius := by
  letI : IsProbabilityMeasure (probability.toMeasure.map first) :=
    Measure.isProbabilityMeasure_map firstMeasurable.aemeasurable
  letI : IsProbabilityMeasure (probability.toMeasure.map second) :=
    Measure.isProbabilityMeasure_map secondMeasurable.aemeasurable
  apply levyProkhorovDist_le_of_forall_le _ _ radiusNonnegative
  intro tolerance measurableSet greater measurable
  rw [Measure.map_apply firstMeasurable measurable,
    Measure.map_apply secondMeasurable isOpen_thickening.measurableSet]
  have pullbackIncluded : first ⁻¹' measurableSet ⊆ second ⁻¹' thickening tolerance measurableSet := by
    intro point member
    apply mem_thickening_iff.mpr
    exact ⟨first point, member, by simpa only [dist_comm] using (close point).trans_lt greater⟩
  exact (measure_mono pullbackIncluded).trans (le_add_right le_rfl)

/-- The true metric gluing for an approximately isometric matching map. -/
def approximateCommonEmbedding {First Second : Type} [MetricSpace First] [MetricSpace Second]
    [Nonempty First] (matching : First → Second) (radius : ℝ) (radiusPositive : 0 < radius)
    (distortion : ∀ first last, |dist first last - dist (matching first) (matching last)| ≤ 2 * radius) :
    CommonMetricEmbedding First Second where
  Ambient := First ⊕ Second
  metric := glueMetricApprox id matching radius radiusPositive distortion
  first := Sum.inl
  second := Sum.inr
  first_isometry := by
    letI := glueMetricApprox id matching radius radiusPositive distortion
    exact Isometry.of_dist_eq (fun _ _ => rfl)
  second_isometry := by
    letI := glueMetricApprox id matching radius radiusPositive distortion
    exact Isometry.of_dist_eq (fun _ _ => rfl)

/-- A measured distortion bound, using an explicit common metric and the
actual same-point probability coupling. This supplies the additional interface
needed for the original unit/diameter metrics; GH convergence alone cannot do so. -/
theorem measuredGHPDist_le_approximate_matching {First Second : Type}
    [MetricSpace First] [MetricSpace Second]
    [CompactSpace First] [CompactSpace Second] [Nonempty First] [Nonempty Second]
    [MeasurableSpace First] [MeasurableSpace Second] [BorelSpace First] [BorelSpace Second]
    (firstLaw : ProbabilityMeasure First) (secondLaw : ProbabilityMeasure Second)
    (matching : First → Second) (matchingMeasurable : Measurable matching)
    (radius : ℝ) (radiusPositive : 0 < radius)
    (distortion : ∀ first last, |dist first last - dist (matching first) (matching last)| ≤ 2 * radius)
    (mesh : ℝ) (meshNonnegative : 0 ≤ mesh)
    (cover : ∀ point : Second, ∃ original : First, dist point (matching original) ≤ mesh) :
    measuredGHPDist firstLaw secondLaw ≤
      max (radius + mesh)
        (radius + levyProkhorovDist (firstLaw.toMeasure.map matching) secondLaw.toMeasure) := by
  let realization := approximateCommonEmbedding matching radius radiusPositive distortion
  letI : MetricSpace (First ⊕ Second) := glueMetricApprox id matching radius radiusPositive distortion
  letI : MeasurableSpace (First ⊕ Second) := borel _
  letI : BorelSpace (First ⊕ Second) := ⟨rfl⟩
  have leftIsometric : Isometry (Sum.inl : First → First ⊕ Second) := realization.first_isometry
  have rightIsometric : Isometry (Sum.inr : Second → First ⊕ Second) := realization.second_isometry
  have leftMeasurable := leftIsometric.continuous.measurable
  have rightMeasurable := rightIsometric.continuous.measurable
  have matched : ∀ point : First, dist (Sum.inl point : First ⊕ Second) (Sum.inr (matching point)) = radius := by
    intro point
    exact glueDist_glued_points id matching radius point
  have hausdorffBound : hausdorffDist
      (range (Sum.inl : First → First ⊕ Second)) (range (Sum.inr : Second → First ⊕ Second)) ≤ radius + mesh := by
    apply hausdorffDist_le_of_mem_dist (add_nonneg radiusPositive.le meshNonnegative)
    · rintro _ ⟨point, rfl⟩
      refine ⟨Sum.inr (matching point), mem_range_self _, ?_⟩
      rw [matched]
      exact le_add_of_nonneg_right meshNonnegative
    · rintro _ ⟨point, rfl⟩
      obtain ⟨original, close⟩ := cover point
      refine ⟨Sum.inl original, mem_range_self _, ?_⟩
      calc
        _ ≤ dist (Sum.inr point : First ⊕ Second) (Sum.inr (matching original)) +
            dist (Sum.inr (matching original) : First ⊕ Second) (Sum.inl original) := dist_triangle _ _ _
        _ = dist point (matching original) + radius := by
          rw [rightIsometric.dist_eq, dist_comm (Sum.inr (matching original)) (Sum.inl original), matched]
        _ ≤ mesh + radius := add_le_add close (le_refl radius)
        _ = radius + mesh := add_comm _ _
  letI : IsProbabilityMeasure (firstLaw.toMeasure.map matching) :=
    Measure.isProbabilityMeasure_map matchingMeasurable.aemeasurable
  letI : IsProbabilityMeasure (firstLaw.toMeasure.map (Sum.inl : First → First ⊕ Second)) :=
    Measure.isProbabilityMeasure_map leftMeasurable.aemeasurable
  letI : IsProbabilityMeasure (firstLaw.toMeasure.map ((Sum.inr : Second → First ⊕ Second) ∘ matching)) :=
    Measure.isProbabilityMeasure_map (rightMeasurable.comp matchingMeasurable).aemeasurable
  letI : IsProbabilityMeasure (secondLaw.toMeasure.map (Sum.inr : Second → First ⊕ Second)) :=
    Measure.isProbabilityMeasure_map rightMeasurable.aemeasurable
  have coupledBound := levyProkhorovDist_same_source_le firstLaw
    (Sum.inl : First → First ⊕ Second) ((Sum.inr : Second → First ⊕ Second) ∘ matching)
    leftMeasurable (rightMeasurable.comp matchingMeasurable) radius radiusPositive.le
    (fun point => (matched point).le)
  have imageBound := levyProkhorovDist_map_isometry_le (firstLaw.toMeasure.map matching)
    secondLaw.toMeasure (Sum.inr : Second → First ⊕ Second) rightIsometric
  rw [Measure.map_map rightMeasurable matchingMeasurable] at imageBound
  have measureBound : levyProkhorovDist
      (firstLaw.toMeasure.map (Sum.inl : First → First ⊕ Second))
      (secondLaw.toMeasure.map (Sum.inr : Second → First ⊕ Second)) ≤
      radius + levyProkhorovDist (firstLaw.toMeasure.map matching) secondLaw.toMeasure :=
    (levyProkhorovDist_triangle _
      (firstLaw.toMeasure.map ((Sum.inr : Second → First ⊕ Second) ∘ matching)) _).trans
      (add_le_add coupledBound imageBound)
  have comparison := measuredGHPDist_le_commonCost firstLaw secondLaw realization
  exact comparison.trans (max_le_max hausdorffBound measureBound)

def xiNativeVertexProbability {K : ℕ} (system : EIGSData K) (level : ℕ) :
    ProbabilityMeasure (XiVtx system level) := ⟨xiVertexCountingMeasure system level, inferInstance⟩

def xiNativeSpeedProbability {K : ℕ} (system : EIGSData K)
    (mass : XiMassParameters system) (level : ℕ) : ProbabilityMeasure (XiVtx system level) :=
  ⟨xiVertexSpeedMeasure system mass level, inferInstance⟩

section ActualWeightedSpaces
variable {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)

/-- The actual chosen Xi embeddings in the actual common compact completion. -/
def xiCommonMetricEmbedding (level : ℕ) :
    letI := xiLevelMetricSpace system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) level
    CommonMetricEmbedding (XiVtx system level)
      (XiMetricCompletion system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair) := by
  letI := xiLevelMetricSpace system connected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) level
  exact {
    Ambient := XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair
    metric := inferInstance
    first := xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair level
    second := id
    first_isometry := xiCompletionEmbedding_isometry system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair level
    second_isometry := isometry_id }

def xiWeightedGHPDistance (mass : XiMassParameters system) (level : ℕ)
    (finiteLaw : ProbabilityMeasure (XiVtx system level)) : ℝ :=
  letI := xiLevelMetricSpace system connected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) level
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  letI : Nonempty (XiVtx system level) :=
    ⟨by simpa only [Nat.zero_add] using xiLiftVertices system 0 level true⟩
  letI : Nonempty (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
    ⟨xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair 0 true⟩
  measuredGHPDist finiteLaw
    (xiLimitProbabilityMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)

theorem xiWeightedGHPDistance_nonnegative (mass : XiMassParameters system) (level : ℕ)
    (finiteLaw : ProbabilityMeasure (XiVtx system level)) :
    0 ≤ xiWeightedGHPDistance system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass level finiteLaw := by
  letI := xiLevelMetricSpace system connected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) level
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  letI : Nonempty (XiVtx system level) :=
    ⟨by simpa only [Nat.zero_add] using xiLiftVertices system 0 level true⟩
  letI : Nonempty (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
    ⟨xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair 0 true⟩
  exact measuredGHPDist_nonnegative _ _

theorem xiWeightedGHPDistance_le_common (mass : XiMassParameters system) (level : ℕ)
    (finiteLaw : ProbabilityMeasure (XiVtx system level)) :
    xiWeightedGHPDistance system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass level finiteLaw ≤
    max (hausdorffDist
      (range (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level)) univ)
      (levyProkhorovDist
        (finiteLaw.toMeasure.map (xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair level))
        (xiLimitProbabilityMeasure system connected lengths lengthsPositive rate
          rateGreaterThanOne eigenpair mass).toMeasure) := by
  letI := xiLevelMetricSpace system connected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) level
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  letI : Nonempty (XiVtx system level) :=
    ⟨by simpa only [Nat.zero_add] using xiLiftVertices system 0 level true⟩
  letI : Nonempty (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
    ⟨xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair 0 true⟩
  have comparison := measuredGHPDist_le_commonCost finiteLaw
    (xiLimitProbabilityMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)
    (xiCommonMetricEmbedding system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair level)
  change xiWeightedGHPDistance system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass level finiteLaw ≤
    max (hausdorffDist
      (range (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level)) (range id))
      (levyProkhorovDist
        (finiteLaw.toMeasure.map (xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair level))
        ((xiLimitProbabilityMeasure system connected lengths lengthsPositive rate
          rateGreaterThanOne eigenpair mass).toMeasure.map id)) at comparison
  simpa only [range_id, Measure.map_id] using comparison

theorem xiSpeedProbability_levyProkhorov_tendsto_zero (mass : XiMassParameters system) :
    Tendsto (fun level => levyProkhorovDist
      (xiSpeedProbabilityMeasure system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass level).toMeasure
      (xiLimitProbabilityMeasure system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass).toMeasure) atTop (𝓝 0) := by
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  exact levyProkhorovDist_tendsto_zero_of_weak _ _
    (xiSpeedProbabilityMeasure_tendsto system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)

/-- Genuine speed-measured GHP convergence in the actual compatible metric. -/
theorem xiWeightedSpeed_GHP_tendsto_zero (mass : XiMassParameters system) :
    Tendsto (fun level => xiWeightedGHPDistance system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass level (xiNativeSpeedProbability system mass level))
      atTop (𝓝 0) := by
  have upper : ∀ level,
      xiWeightedGHPDistance system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass level (xiNativeSpeedProbability system mass level) ≤
      max (hausdorffDist
        (range (xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair level)) univ)
        (levyProkhorovDist
          (xiSpeedProbabilityMeasure system connected lengths lengthsPositive rate
            rateGreaterThanOne eigenpair mass level).toMeasure
          (xiLimitProbabilityMeasure system connected lengths lengthsPositive rate
            rateGreaterThanOne eigenpair mass).toMeasure) := by
    intro level
    have bound := xiWeightedGHPDistance_le_common system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass level (xiNativeSpeedProbability system mass level)
    change xiWeightedGHPDistance system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass level (xiNativeSpeedProbability system mass level) ≤
      max (hausdorffDist
        (range (xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair level)) univ)
        (levyProkhorovDist ((xiVertexSpeedMeasure system mass level).map
          (xiCompletionEmbedding system connected lengths lengthsPositive rate
            (zero_lt_one.trans rateGreaterThanOne) eigenpair level))
          (xiLimitProbabilityMeasure system connected lengths lengthsPositive rate
            rateGreaterThanOne eigenpair mass).toMeasure) at bound
    simpa only [xiVertexSpeedMeasure_map system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass level] using bound
  have convergence :=
    (xiFiniteLevel_hausdorffDist_tendsto_zero system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair).max
    (xiSpeedProbability_levyProkhorov_tendsto_zero system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass)
  apply squeeze_zero
    (fun level => xiWeightedGHPDistance_nonnegative system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass level _) upper
  simpa only [max_self] using convergence

variable (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))

include plantingNonadjacent distancePositive

theorem xiVertexProbability_levyProkhorov_tendsto_zero (mass : XiMassParameters system) :
    Tendsto (fun level => levyProkhorovDist
      (xiVertexProbabilityMeasure system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair level).toMeasure
      (xiLimitProbabilityMeasure system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass).toMeasure) atTop (𝓝 0) := by
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  exact levyProkhorovDist_tendsto_zero_of_weak _ _
    (xiVertexProbabilityMeasure_tendsto system connected plantingNonadjacent distancePositive
      lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)

/-- Genuine uniform-vertex-measured GHP convergence in the actual compatible metric. -/
theorem xiWeightedVertex_GHP_tendsto_zero (mass : XiMassParameters system) :
    Tendsto (fun level => xiWeightedGHPDistance system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass level (xiNativeVertexProbability system level))
      atTop (𝓝 0) := by
  apply squeeze_zero
    (fun level => xiWeightedGHPDistance_nonnegative system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass level _)
  · exact fun level => xiWeightedGHPDistance_le_common system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass level (xiNativeVertexProbability system level)
  · simpa only [max_self] using
      (xiFiniteLevel_hausdorffDist_tendsto_zero system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair).max
      (xiVertexProbability_levyProkhorov_tendsto_zero system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair plantingNonadjacent distancePositive mass)

end ActualWeightedSpaces

section OriginalRuleConsumer
variable {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))

/-- All metric and mass parameters are chosen from the original rules. -/
def xiCanonicalVertexGHPDistanceOfRules (level : ℕ) : ℝ :=
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  let mass := xiMassParametersOfRules system connected distancePositive
  let rateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  xiWeightedGHPDistance system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass level
    (xiNativeVertexProbability system level)

def xiCanonicalSpeedGHPDistanceOfRules (level : ℕ) : ℝ :=
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  let mass := xiMassParametersOfRules system connected distancePositive
  let rateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  xiWeightedGHPDistance system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass level
    (xiNativeSpeedProbability system mass level)

theorem xiCanonicalVertex_GHP_tendsto_zero_of_rules :
    Tendsto (xiCanonicalVertexGHPDistanceOfRules system connected loopless unique
      plantingNonadjacent distancePositive) atTop (𝓝 0) := by
  exact xiWeightedVertex_GHP_tendsto_zero system connected _ _ _ _ _
    plantingNonadjacent distancePositive (xiMassParametersOfRules system connected distancePositive)

theorem xiCanonicalSpeed_GHP_tendsto_zero_of_rules :
    Tendsto (xiCanonicalSpeedGHPDistanceOfRules system connected loopless unique
      plantingNonadjacent distancePositive) atTop (𝓝 0) := by
  exact xiWeightedSpeed_GHP_tendsto_zero system connected _ _ _ _ _
    (xiMassParametersOfRules system connected distancePositive)

end OriginalRuleConsumer
end EIGS.MeasuredGHP

#print axioms EIGS.MeasuredGHP.measuredGHPDist_nonnegative
#print axioms EIGS.MeasuredGHP.measuredGHPDist_le_commonCost
#print axioms EIGS.MeasuredGHP.levyProkhorovDist_tendsto_zero_of_weak
#print axioms EIGS.MeasuredGHP.levyProkhorovEDist_map_isometry_le
#print axioms EIGS.MeasuredGHP.levyProkhorovDist_same_source_le
#print axioms EIGS.MeasuredGHP.measuredGHPDist_le_approximate_matching
#print axioms EIGS.MeasuredGHP.xiWeightedGHPDistance_le_common
#print axioms EIGS.MeasuredGHP.xiWeightedSpeed_GHP_tendsto_zero
#print axioms EIGS.MeasuredGHP.xiWeightedVertex_GHP_tendsto_zero
#print axioms EIGS.MeasuredGHP.xiCanonicalVertex_GHP_tendsto_zero_of_rules
#print axioms EIGS.MeasuredGHP.xiCanonicalSpeed_GHP_tendsto_zero_of_rules
