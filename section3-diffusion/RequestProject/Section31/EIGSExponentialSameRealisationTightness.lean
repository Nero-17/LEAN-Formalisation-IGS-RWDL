import RequestProject.Section31.EIGSNativeExponentialJ1TightnessOfRules
import RequestProject.Section31.ExponentialJ1SpatialDistortionTightness
import RequestProject.Section31.FiniteGraphExponentialPhysicalJ1PathLaw

/-! Unit and physical Poisson path tightness in every supplied actual
vanishing-distortion realization. In particular the existing original
GHPS/Hunt ambient can be used without choosing a second ambient. -/
namespace EIGS
open MeasureTheory ProbabilityTheory Filter Topology
open IGS.Sec31.DiscreteMarkov IGS.Sec31.PoissonClock
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 6000000
variable {K : ℕ}
local instance (horizon : ℝ≥0) : BoundedSpace (Set.Icc (0 : ℝ) (horizon : ℝ)) :=
  ⟨Metric.isBounded_of_compactSpace⟩
local instance {Ambient : Type} [MetricSpace Ambient] [BoundedSpace Ambient]
    (horizon : ℝ≥0) : MeasurableSpace (CadlagJ1Path (Set.Icc (0 : ℝ) (horizon : ℝ)) Ambient) := borel _
local instance {Ambient : Type} [MetricSpace Ambient] [BoundedSpace Ambient]
    (horizon : ℝ≥0) : BorelSpace (CadlagJ1Path (Set.Icc (0 : ℝ) (horizon : ℝ)) Ambient) := ⟨rfl⟩

theorem xiExponentialJ1Laws_unit_and_physical_tight_in_same_realisation
    (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (Ambient : Type) [MetricSpace Ambient] [CompactSpace Ambient]
    [MeasurableSpace Ambient] [BorelSpace Ambient] :
    let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
    letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system connected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected)
      distanceGreaterThanOne parameters.eigenpair
    letI : BoundedSpace Ambient := ⟨Metric.isBounded_of_compactSpace⟩
    ∀ target : parameters.LimitSpace → Ambient, Continuous target →
    ∀ sources : ∀ level, XiVtx system level → Ambient,
    ∀ radii : ℕ → ℝ, Tendsto radii atTop (𝓝 0) →
      (∀ level vertex, dist (sources level vertex) (target (parameters.vertexEmbedding level vertex)) ≤ radii level) →
    ∀ initial : ∀ level, ProbabilityMeasure (XiVtx system level),
    ∀ horizon : ℝ≥0, ∀ horizonPositive : 0 < horizon,
    let rates := xiNativeFiniteJumpRateNNReal system connected distancePositive normalization normalizationPositive
    IsTightMeasureSet (Set.range (fun level =>
      (finiteGraphExponentialJ1Law (XiSimpleGraph system level)
        (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system connected level vertex))
        (initial level) (sources level) ((rates level : ℝ) * horizon)
        (mul_pos (xiNativeFiniteJumpRateNNReal_positive system connected distancePositive normalization normalizationPositive level)
          (by exact_mod_cast horizonPositive)) : Measure (UnitCadlagJ1Path Ambient)))) ∧
    IsTightMeasureSet (Set.range (fun level =>
      (finiteGraphExponentialPhysicalJ1Law (XiSimpleGraph system level)
        (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system connected level vertex))
        (initial level) (sources level) (rates level : ℝ)
        (xiNativeFiniteJumpRateNNReal_positive system connected distancePositive normalization normalizationPositive level)
        horizon horizonPositive : Measure (CadlagJ1Path (Set.Icc (0 : ℝ) (horizon : ℝ)) Ambient)))) := by
  intro parameters distanceGreaterThanOne
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system connected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected)
    distanceGreaterThanOne parameters.eigenpair
  letI : BoundedSpace parameters.LimitSpace := ⟨Metric.isBounded_of_compactSpace⟩
  letI : MeasurableSpace parameters.LimitSpace := borel _
  letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  letI : BoundedSpace Ambient := ⟨Metric.isBounded_of_compactSpace⟩
  intro target targetContinuous sources radii radiiZero displacement initial horizon horizonPositive
  let rates := xiNativeFiniteJumpRateNNReal system connected distancePositive normalization normalizationPositive
  let horizons := fun level => (rates level : ℝ) * horizon
  have horizonsPositive : ∀ level, 0 < horizons level := fun level =>
    mul_pos (xiNativeFiniteJumpRateNNReal_positive system connected distancePositive normalization normalizationPositive level)
      (by exact_mod_cast horizonPositive)
  have nativeTight := xiNativeExponentialJ1Laws_isTight_of_rules system connected loopless unique
    plantingNonadjacent distancePositive normalization normalizationPositive initial horizon horizonPositive
  have unitTight := finiteGraphExponentialJ1Laws_tight_of_spatial_distortion
    (fun level => XiVtx system level) (fun level => XiSimpleGraph system level)
    (fun level vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system connected level vertex)) initial
    parameters.vertexEmbedding sources target targetContinuous horizons horizonsPositive radii radiiZero displacement
    (by simpa only [horizons, rates] using nativeTight)
  dsimp only
  refine ⟨unitTight, ?_⟩
  have physicalTight := unitToPhysicalCadlagJ1_tight horizon horizonPositive
    (fun level => finiteGraphExponentialJ1Law (XiSimpleGraph system level)
      (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system connected level vertex))
      (initial level) (sources level) ((rates level : ℝ) * horizon)
      (mul_pos (xiNativeFiniteJumpRateNNReal_positive system connected distancePositive normalization normalizationPositive level)
        (by exact_mod_cast horizonPositive))) unitTight
  simpa only [finiteGraphExponentialPhysicalJ1Law, ProbabilityMeasure.toMeasure_map] using physicalTight

end
end EIGS

#print axioms EIGS.xiExponentialJ1Laws_unit_and_physical_tight_in_same_realisation
