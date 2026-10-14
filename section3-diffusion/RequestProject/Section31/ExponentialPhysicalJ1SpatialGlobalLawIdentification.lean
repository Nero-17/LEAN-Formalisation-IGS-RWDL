import RequestProject.Section31.ExponentialPhysicalJ1GlobalLawIdentification
import RequestProject.Section31.CadlagJ1SpatialTransport

/-! Physical-interval spatial images of the actual holding laws converge
to the spatial image of the same global continuous law's restriction.
The time and spatial maps commute pathwise and in probability law. -/

namespace IGS.Sec31.PoissonClock
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open IGS.Sec31.DiscreteMarkov EIGS
open scoped NNReal
set_option maxHeartbeats 4000000

variable {State Ambient : Type*} [MetricSpace State] [CompactSpace State]
variable [MetricSpace Ambient] [CompactSpace Ambient]
variable [MeasurableSpace State] [BorelSpace State] [MeasurableSpace Ambient] [BorelSpace Ambient]
local instance physicalSpatialSourceBounded : BoundedSpace State := ⟨Metric.isBounded_of_compactSpace⟩
local instance physicalSpatialTargetBounded : BoundedSpace Ambient := ⟨Metric.isBounded_of_compactSpace⟩
local instance physicalSpatialMapMeasurable {Time Space : Type*}
    [TopologicalSpace Time] [TopologicalSpace Space] : MeasurableSpace C(Time, Space) := borel _
local instance physicalSpatialMapBorel {Time Space : Type*}
    [TopologicalSpace Time] [TopologicalSpace Space] : BorelSpace C(Time, Space) := ⟨rfl⟩
local instance physicalSpatialTimeBounded (horizon : ℝ≥0) : BoundedSpace (Icc (0 : ℝ) (horizon : ℝ)) :=
  ⟨Metric.isBounded_of_compactSpace⟩
local instance physicalSpatialCadlagMeasurable {Space : Type*} [MetricSpace Space] [BoundedSpace Space]
    (horizon : ℝ≥0) : MeasurableSpace (CadlagJ1Path (Icc (0 : ℝ) (horizon : ℝ)) Space) := borel _
local instance physicalSpatialCadlagBorel {Space : Type*} [MetricSpace Space] [BoundedSpace Space]
    (horizon : ℝ≥0) : BorelSpace (CadlagJ1Path (Icc (0 : ℝ) (horizon : ℝ)) Space) := ⟨rfl⟩

theorem unitToPhysicalCadlagJ1_spatial_path (horizon : ℝ≥0) (positive : 0 < horizon)
    (spatial : State → Ambient) (continuousSpatial : Continuous spatial) (path : UnitCadlagJ1Path State) :
    unitToPhysicalCadlagJ1 horizon positive (cadlagJ1SpatialMap spatial continuousSpatial path) =
      cadlagJ1SpatialMap spatial continuousSpatial (unitToPhysicalCadlagJ1 horizon positive path) := by
  apply Subtype.ext
  rfl

theorem unitToPhysicalCadlagJ1_spatial_law (horizon : ℝ≥0) (positive : 0 < horizon)
    (spatial : State → Ambient) (continuousSpatial : Continuous spatial)
    (law : ProbabilityMeasure (UnitCadlagJ1Path State)) :
    ProbabilityMeasure.map
      (ProbabilityMeasure.map law (cadlagJ1SpatialMap_continuous spatial continuousSpatial).measurable.aemeasurable)
      (unitToPhysicalCadlagJ1_continuous horizon positive).measurable.aemeasurable =
      ProbabilityMeasure.map
        (ProbabilityMeasure.map law (unitToPhysicalCadlagJ1_continuous horizon positive).measurable.aemeasurable)
        (cadlagJ1SpatialMap_continuous spatial continuousSpatial).measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (unitToPhysicalCadlagJ1_continuous horizon positive).measurable
    (cadlagJ1SpatialMap_continuous spatial continuousSpatial).measurable,
    Measure.map_map (cadlagJ1SpatialMap_continuous spatial continuousSpatial).measurable
      (unitToPhysicalCadlagJ1_continuous horizon positive).measurable]
  congr 1

theorem unitToPhysicalCadlagJ1_spatial_global_law (horizon : ℝ≥0) (positive : 0 < horizon)
    (spatial : State → Ambient) (continuousSpatial : Continuous spatial)
    (globalLaw : ProbabilityMeasure C(ℝ≥0, State)) :
    ProbabilityMeasure.map
      (ProbabilityMeasure.map
        (ProbabilityMeasure.map globalLaw (continuousPathToUnitCadlagJ1_continuous horizon).measurable.aemeasurable)
        (cadlagJ1SpatialMap_continuous spatial continuousSpatial).measurable.aemeasurable)
      (unitToPhysicalCadlagJ1_continuous horizon positive).measurable.aemeasurable =
      ProbabilityMeasure.map
        (ProbabilityMeasure.map
          (ProbabilityMeasure.map globalLaw (continuousPathFiniteHorizonRestriction_continuous horizon).measurable.aemeasurable)
          compactContinuousMapToCadlagJ1_lipschitz.continuous.measurable.aemeasurable)
        (cadlagJ1SpatialMap_continuous spatial continuousSpatial).measurable.aemeasurable := by
  rw [unitToPhysicalCadlagJ1_spatial_law, unitToPhysicalCadlagJ1_global_law]

theorem finiteGraphExponentialPhysicalJ1Laws_tendsto_spatial_global_restriction
    (Vertex : ℕ → Type) [∀ level, Fintype (Vertex level)] [∀ level, DecidableEq (Vertex level)]
    [∀ level, MeasurableSpace (Vertex level)] [∀ level, MeasurableSingletonClass (Vertex level)]
    (graphs : ∀ level, SimpleGraph (Vertex level)) [∀ level, DecidableRel (graphs level).Adj]
    (degreePositive : ∀ level vertex, 0 < (graphs level).degree vertex)
    (initial : ∀ level, ProbabilityMeasure (Vertex level)) (sources : ∀ level, Vertex level → Ambient)
    (rates : ℕ → ℝ) (ratesPositive : ∀ level, 0 < rates level)
    (horizon : ℝ≥0) (positive : 0 < horizon) (globalLaw : ProbabilityMeasure C(ℝ≥0, State))
    (spatial : State → Ambient) (continuousSpatial : Continuous spatial)
    (unitConverges : Tendsto (fun level => finiteGraphExponentialJ1Law (graphs level) (degreePositive level)
      (initial level) (sources level) (rates level * horizon)
      (mul_pos (ratesPositive level) (show (0 : ℝ) < horizon from positive))) atTop
      (𝓝 (ProbabilityMeasure.map
        (ProbabilityMeasure.map globalLaw (continuousPathToUnitCadlagJ1_continuous horizon).measurable.aemeasurable)
        (cadlagJ1SpatialMap_continuous spatial continuousSpatial).measurable.aemeasurable))) :
    Tendsto (fun level => finiteGraphExponentialPhysicalJ1Law (graphs level) (degreePositive level)
      (initial level) (sources level) (rates level) (ratesPositive level) horizon positive) atTop
      (𝓝 (ProbabilityMeasure.map
        (ProbabilityMeasure.map
          (ProbabilityMeasure.map globalLaw (continuousPathFiniteHorizonRestriction_continuous horizon).measurable.aemeasurable)
          compactContinuousMapToCadlagJ1_lipschitz.continuous.measurable.aemeasurable)
        (cadlagJ1SpatialMap_continuous spatial continuousSpatial).measurable.aemeasurable)) := by
  have result := unitToPhysicalCadlagJ1_weak_convergence horizon positive _ _ unitConverges
  rw [unitToPhysicalCadlagJ1_spatial_global_law] at result
  exact result

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.unitToPhysicalCadlagJ1_spatial_global_law
#print axioms IGS.Sec31.PoissonClock.finiteGraphExponentialPhysicalJ1Laws_tendsto_spatial_global_restriction
