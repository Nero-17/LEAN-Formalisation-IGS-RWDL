import RequestProject.Section31.EIGSNativeExponentialJ1TightnessOfRules
import RequestProject.Section31.ExponentialJ1SpatialDistortionTightness
import RequestProject.Section31.EIGSOriginalCountableRealisation

/-! Actual original unit-edge graphs divided by their own diameters have
tight exponential-clock J1 path laws in one compact common ambient. The
finite graph embeddings are isometric, and their distance from the native
projection is proved by the actual diameter/distortion theorem. The native
clock is unchanged; Poisson count identification is a separate theorem. -/

namespace EIGS
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open IGS.Sec31.DiscreteMarkov IGS.Sec31.PoissonClock
open scoped Classical NNReal
set_option maxHeartbeats 7000000
variable {K : ℕ}

theorem exists_xiOriginalExponentialJ1Tightness_of_rules (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization) :
    let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
    letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system connected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected)
        distanceGreaterThanOne parameters.eigenpair
    ∃ Ambient : Type, ∃ metric : MetricSpace Ambient, letI := metric;
      ∃ ambientCompact : CompactSpace Ambient, letI := ambientCompact;
      letI : BoundedSpace Ambient := ⟨Metric.isBounded_of_compactSpace⟩;
      letI : MeasurableSpace Ambient := borel _;
      letI : BorelSpace Ambient := ⟨rfl⟩;
      ∃ target : parameters.LimitSpace → Ambient, Continuous target ∧
        (letI := MeasuredGHP.xiCompletionDiameterMetricSpace system connected parameters.lengths
          parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair;
          Isometry target) ∧
      ∃ sources : ∀ level, XiVtx system level → Ambient,
        (∀ level, letI := MeasuredGHP.xiOriginalGraphDiameterMetricSpace system connected level;
          Isometry (sources level)) ∧
        ∀ initial : ∀ level, ProbabilityMeasure (XiVtx system level),
          ∀ horizon : ℝ≥0, ∀ horizonPositive : 0 < horizon,
          let rates := xiNativeFiniteJumpRateNNReal system connected distancePositive normalization normalizationPositive;
          IsTightMeasureSet (Set.range (fun level =>
            (finiteGraphExponentialJ1Law (XiSimpleGraph system level)
              (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system connected level vertex))
              (initial level) (sources level) ((rates level : ℝ) * horizon)
              (mul_pos (xiNativeFiniteJumpRateNNReal_positive system connected distancePositive normalization normalizationPositive level)
                horizonPositive) : Measure (UnitCadlagJ1Path Ambient)))) := by
  classical
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  letI nativeCompact : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system connected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected)
      distanceGreaterThanOne parameters.eigenpair
  letI : MeasurableSpace parameters.LimitSpace := borel _
  letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  letI : BoundedSpace parameters.LimitSpace := ⟨Metric.isBounded_of_compactSpace⟩
  have common := by
    letI vertexMetric : ∀ level, MetricSpace (XiVtx system level) :=
      MeasuredGHP.xiOriginalGraphDiameterMetricSpace system connected
    letI completionMetric : MetricSpace parameters.LimitSpace := MeasuredGHP.xiCompletionDiameterMetricSpace system connected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected)
        distanceGreaterThanOne parameters.eigenpair
    letI vertexNonempty : ∀ level, Nonempty (XiVtx system level) := fun level =>
      ⟨by simpa only [Nat.zero_add] using xiLiftVertices system 0 level true⟩
    letI completionNonempty : Nonempty parameters.LimitSpace := ⟨parameters.vertexEmbedding 0 true⟩
    exact @CountableRealisation.exists_compact_common_realisation_of_projection_distortion
      (XiVtx system) vertexMetric (fun _ => inferInstance) vertexNonempty parameters.LimitSpace completionMetric
      nativeCompact completionNonempty parameters.vertexEmbedding
      (MeasuredGHP.xiOriginalDiameter_projection_distortion_zero system connected loopless unique plantingNonadjacent
        distancePositive parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected)
          distanceGreaterThanOne parameters.normalized parameters.eigenpair)
  obtain ⟨Ambient, metric, ambientComplete, ambientCompact, target, targetIsometry, sources, sourceIsometry,
    radii, radiiPositive, radiiZero, displacement, remaining⟩ := common
  letI := metric
  letI := ambientCompact
  letI : BoundedSpace Ambient := ⟨Metric.isBounded_of_compactSpace⟩
  letI : MeasurableSpace Ambient := borel _
  letI : BorelSpace Ambient := ⟨rfl⟩
  have targetContinuous : Continuous target := by
    letI := MeasuredGHP.xiCompletionDiameterMetricSpace system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair
    exact targetIsometry.continuous
  refine ⟨Ambient, metric, ambientCompact, target, targetContinuous, targetIsometry, sources, sourceIsometry, ?_⟩
  intro initial horizon horizonPositive
  let rates := xiNativeFiniteJumpRateNNReal system connected distancePositive normalization normalizationPositive
  have nativeTight := xiNativeExponentialJ1Laws_isTight_of_rules system connected loopless unique plantingNonadjacent
    distancePositive normalization normalizationPositive initial horizon horizonPositive
  exact finiteGraphExponentialJ1Laws_tight_of_spatial_distortion (fun level => XiVtx system level)
    (fun level => XiSimpleGraph system level)
    (fun level vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system connected level vertex))
    initial parameters.vertexEmbedding sources target targetContinuous
    (fun level => (rates level : ℝ) * horizon)
    (fun level => mul_pos (xiNativeFiniteJumpRateNNReal_positive system connected distancePositive normalization normalizationPositive level)
      horizonPositive)
    radii radiiZero (fun level vertex => (displacement level vertex).le) nativeTight

end
end EIGS

#print axioms EIGS.exists_xiOriginalExponentialJ1Tightness_of_rules
