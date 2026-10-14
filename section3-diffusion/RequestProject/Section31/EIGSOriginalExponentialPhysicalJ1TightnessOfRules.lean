import RequestProject.Section31.EIGSNativeExponentialJ1TightnessOfRules
import RequestProject.Section31.ExponentialJ1SpatialDistortionTightness
import RequestProject.Section31.EIGSOriginalCountableRealisation
import RequestProject.Section31.EIGSOriginalExponentialJ1TightnessOfRules
import RequestProject.Section31.FiniteGraphExponentialPhysicalJ1PathLaw

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
local instance originalPhysicalTimeBounded (horizon : ℝ≥0) : BoundedSpace (Set.Icc (0 : ℝ) (horizon : ℝ)) :=
  ⟨Metric.isBounded_of_compactSpace⟩
local instance originalPhysicalCadlagMeasurable {Ambient : Type*} [MetricSpace Ambient] [BoundedSpace Ambient]
    (horizon : ℝ≥0) : MeasurableSpace (CadlagJ1Path (Set.Icc (0 : ℝ) (horizon : ℝ)) Ambient) := borel _
local instance originalPhysicalCadlagBorel {Ambient : Type*} [MetricSpace Ambient] [BoundedSpace Ambient]
    (horizon : ℝ≥0) : BorelSpace (CadlagJ1Path (Set.Icc (0 : ℝ) (horizon : ℝ)) Ambient) := ⟨rfl⟩

theorem exists_xiOriginalExponentialPhysicalJ1Tightness_of_rules (system : EIGSData K)
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
            (finiteGraphExponentialPhysicalJ1Law (XiSimpleGraph system level)
              (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system connected level vertex))
              (initial level) (sources level) (rates level : ℝ)
              (xiNativeFiniteJumpRateNNReal_positive system connected distancePositive normalization normalizationPositive level)
              horizon horizonPositive : Measure (CadlagJ1Path (Set.Icc (0 : ℝ) (horizon : ℝ)) Ambient)))) := by
  classical
  obtain ⟨Ambient, metric, ambientCompact, target, targetContinuous, targetIsometry, sources, sourceIsometry, tight⟩ :=
    exists_xiOriginalExponentialJ1Tightness_of_rules system connected loopless unique plantingNonadjacent
      distancePositive normalization normalizationPositive
  letI := metric
  letI := ambientCompact
  letI : BoundedSpace Ambient := ⟨Metric.isBounded_of_compactSpace⟩
  letI : MeasurableSpace Ambient := borel _
  letI : BorelSpace Ambient := ⟨rfl⟩
  refine ⟨Ambient, metric, ambientCompact, target, targetContinuous, targetIsometry, sources, sourceIsometry, ?_⟩
  intro initial horizon horizonPositive
  let rates := xiNativeFiniteJumpRateNNReal system connected distancePositive normalization normalizationPositive
  have unitTight := tight initial horizon horizonPositive
  have result := unitToPhysicalCadlagJ1_tight horizon horizonPositive
    (fun level => finiteGraphExponentialJ1Law (XiSimpleGraph system level)
      (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system connected level vertex))
      (initial level) (sources level) ((rates level : ℝ) * horizon)
      (mul_pos (xiNativeFiniteJumpRateNNReal_positive system connected distancePositive normalization normalizationPositive level)
        (by exact_mod_cast horizonPositive))) unitTight
  simpa only [finiteGraphExponentialPhysicalJ1Law, ProbabilityMeasure.toMeasure_map] using result

end
end EIGS

#print axioms EIGS.exists_xiOriginalExponentialPhysicalJ1Tightness_of_rules
