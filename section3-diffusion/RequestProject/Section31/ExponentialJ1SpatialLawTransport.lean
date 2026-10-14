import RequestProject.Section31.FiniteGraphExponentialJ1PathLaw
import RequestProject.Section31.CadlagJ1SpatialTransport
import Mathlib.MeasureTheory.Measure.Tight

namespace IGS.Sec31.PoissonClock
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open IGS.Sec31.DiscreteMarkov EIGS
open scoped Topology
set_option maxHeartbeats 5000000

variable {State OtherState : Type*} [MetricSpace State] [CompactSpace State]
variable [MetricSpace OtherState] [CompactSpace OtherState]
variable [MeasurableSpace State] [BorelSpace State] [MeasurableSpace OtherState] [BorelSpace OtherState]
local instance exponentialSpatialSourceBounded : BoundedSpace State := ⟨Metric.isBounded_of_compactSpace⟩
local instance exponentialSpatialTargetBounded : BoundedSpace OtherState := ⟨Metric.isBounded_of_compactSpace⟩

theorem exponentialHoldingJ1Sample_spatial_map {Vertex : Type*}
    (embedding : Vertex → State) (spatial : State → OtherState) (spatialContinuous : Continuous spatial)
    (horizon : ℝ) (horizonPositive : 0 < horizon) (sample : (ℕ → Vertex) × (ℕ → ℝ)) :
    cadlagJ1SpatialMap spatial spatialContinuous (exponentialHoldingJ1Sample embedding horizon horizonPositive sample) =
      exponentialHoldingJ1Sample (spatial ∘ embedding) horizon horizonPositive sample := by
  classical
  apply Subtype.ext
  by_cases regular : exponentialClockRegular sample.2
  · simp only [exponentialHoldingJ1Sample, dif_pos regular, cadlagJ1SpatialMap, j1FunctionSpatialMap,
      unitHoldingCadlagPath, Function.comp_def, holdingTimePath]
  · simp only [exponentialHoldingJ1Sample, dif_neg regular, cadlagJ1SpatialMap, j1FunctionSpatialMap,
      Function.comp_def]

theorem finiteGraphExponentialJ1Law_spatial_map
    {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
    [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex]
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (initial : ProbabilityMeasure Vertex)
    (embedding : Vertex → State) (spatial : State → OtherState) (spatialContinuous : Continuous spatial)
    (horizon : ℝ) (horizonPositive : 0 < horizon) :
    ProbabilityMeasure.map (finiteGraphExponentialJ1Law graph degreePositive initial embedding horizon horizonPositive)
      (cadlagJ1SpatialMap_continuous spatial spatialContinuous).measurable.aemeasurable =
        finiteGraphExponentialJ1Law graph degreePositive initial (spatial ∘ embedding) horizon horizonPositive := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map, finiteGraphExponentialJ1Law]
  rw [Measure.map_map_of_aemeasurable
    (cadlagJ1SpatialMap_continuous spatial spatialContinuous).measurable.aemeasurable
    (exponentialHoldingJ1Sample_aemeasurable graph degreePositive initial embedding horizon horizonPositive)]
  congr 1
  exact funext (exponentialHoldingJ1Sample_spatial_map embedding spatial spatialContinuous horizon horizonPositive)

theorem finiteGraphExponentialJ1Laws_spatial_tight
    (Vertex : ℕ → Type) [∀ level, Fintype (Vertex level)] [∀ level, DecidableEq (Vertex level)]
    [∀ level, MeasurableSpace (Vertex level)] [∀ level, MeasurableSingletonClass (Vertex level)]
    (graphs : ∀ level, SimpleGraph (Vertex level)) [∀ level, DecidableRel (graphs level).Adj]
    (degreePositive : ∀ level vertex, 0 < (graphs level).degree vertex)
    (initial : ∀ level, ProbabilityMeasure (Vertex level)) (embedding : ∀ level, Vertex level → State)
    (spatial : State → OtherState) (spatialContinuous : Continuous spatial)
    (horizons : ℕ → ℝ) (horizonsPositive : ∀ level, 0 < horizons level)
    (tight : IsTightMeasureSet (Set.range (fun level =>
      (finiteGraphExponentialJ1Law (graphs level) (degreePositive level) (initial level) (embedding level)
        (horizons level) (horizonsPositive level) : Measure (UnitCadlagJ1Path State))))) :
    IsTightMeasureSet (Set.range (fun level =>
      (finiteGraphExponentialJ1Law (graphs level) (degreePositive level) (initial level) (spatial ∘ embedding level)
        (horizons level) (horizonsPositive level) : Measure (UnitCadlagJ1Path OtherState)))) := by
  have mapped := tight.map (cadlagJ1SpatialMap_continuous spatial spatialContinuous)
  have equality : Measure.map (cadlagJ1SpatialMap spatial spatialContinuous) ''
      (Set.range (fun level =>
        (finiteGraphExponentialJ1Law (graphs level) (degreePositive level) (initial level) (embedding level)
          (horizons level) (horizonsPositive level) : Measure (UnitCadlagJ1Path State)))) =
        Set.range (fun level =>
          (finiteGraphExponentialJ1Law (graphs level) (degreePositive level) (initial level) (spatial ∘ embedding level)
            (horizons level) (horizonsPositive level) : Measure (UnitCadlagJ1Path OtherState))) := by
    rw [← Set.range_comp']
    congr 1
    funext level
    exact congrArg (fun law : ProbabilityMeasure (UnitCadlagJ1Path OtherState) => (law : Measure _))
      (finiteGraphExponentialJ1Law_spatial_map _ _ _ _ _ spatialContinuous _ _)
  rw [equality] at mapped
  exact mapped

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.exponentialHoldingJ1Sample_spatial_map
#print axioms IGS.Sec31.PoissonClock.finiteGraphExponentialJ1Law_spatial_map
#print axioms IGS.Sec31.PoissonClock.finiteGraphExponentialJ1Laws_spatial_tight
