import RequestProject.Section31.CadlagJ1CarrierInstances
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Continuous spatial transport on the genuine cadlag carrier equipped
with the explicit time-change J1 pseudometric. Uniform continuity of the
spatial map controls the spatial part of every clock-change cost; the clock
part is preserved. Thus a spatial homeomorphism, or the identity between a
metric and a positive rescaling, can transport actual weak path laws without
identifying their distances. This does not prove J1 completeness/Polishness.

The general spatial-transport question was suggested by
IGSIII34/Diffusion/SkorokhodCarrierTransportCompletion.lean at commit
cb0183af15f571bb0b1b5d3b8de367a419716f1b. This is an independent proof for
the existing RWDL finite-interval distance and cadlag subtype. -/

namespace IGS.Sec31.DiscreteMarkov
noncomputable section
open Set Filter Topology MeasureTheory
open scoped UniformConvergence

variable {Time State OtherState : Type*} [LinearOrder Time] [MetricSpace Time] [BoundedSpace Time]
  [MetricSpace State] [CompactSpace State] [MetricSpace OtherState] [CompactSpace OtherState]

local instance spatialJ1SourceBoundedSpace : BoundedSpace State := ⟨Metric.isBounded_of_compactSpace⟩
local instance spatialJ1TargetBoundedSpace : BoundedSpace OtherState := ⟨Metric.isBounded_of_compactSpace⟩

theorem IsCadlagPath.map_continuous {path : Time → State} (cadlag : IsCadlagPath path)
    (spatial : State → OtherState) (spatialContinuous : Continuous spatial) :
    IsCadlagPath (spatial ∘ path) := by
  constructor
  · intro time
    exact spatialContinuous.continuousAt.comp_continuousWithinAt (cadlag.1 time)
  · intro time
    obtain ⟨limit, convergence⟩ := cadlag.2 time
    exact ⟨spatial limit, spatialContinuous.continuousAt.tendsto.comp convergence⟩

def j1FunctionSpatialMap (spatial : State → OtherState) (path : J1Function Time State) :
    J1Function Time OtherState := ⟨spatial ∘ path.toFun⟩

theorem j1FunctionSpatialMap_continuous (spatial : State → OtherState)
    (spatialContinuous : Continuous spatial) :
    Continuous (j1FunctionSpatialMap (Time := Time) spatial) := by
  have spatialUniform := CompactSpace.uniformContinuous_of_continuous spatialContinuous
  apply continuous_iff_continuousAt.mpr
  intro path
  apply Metric.continuousAt_iff.mpr
  intro epsilon positive
  obtain ⟨duration, durationPositive, spatialClose⟩ :=
    Metric.uniformContinuous_iff.mp spatialUniform (epsilon / 2) (half_pos positive)
  refine ⟨min (epsilon / 2) duration, lt_min (half_pos positive) durationPositive, ?_⟩
  intro other near
  change skorokhodJ1Distance other.toFun path.toFun < min (epsilon / 2) duration at near
  obtain ⟨change, costSmall⟩ := exists_lt_of_ciInf_lt near
  have mappedCost : skorokhodJ1Cost (spatial ∘ other.toFun) (spatial ∘ path.toFun) change ≤ epsilon / 2 := by
    apply max_le
    · exact (le_max_left _ _).trans (costSmall.le.trans (min_le_left _ _))
    · apply (UniformFun.dist_le (half_pos positive).le).mpr
      intro time
      have stateClose : dist (other.toFun time) (path.toFun (change time)) < duration :=
        ((skorokhodJ1Cost_path_le other.toFun path.toFun change time).trans_lt costSmall).trans_le
          (min_le_right _ _)
      exact (spatialClose stateClose).le
  exact ((skorokhodJ1Distance_le_cost (spatial ∘ other.toFun) (spatial ∘ path.toFun) change).trans mappedCost).trans_lt
    (half_lt_self positive)

def cadlagJ1SpatialMap (spatial : State → OtherState) (spatialContinuous : Continuous spatial)
    (path : CadlagJ1Path Time State) : CadlagJ1Path Time OtherState :=
  ⟨j1FunctionSpatialMap spatial path.val, path.property.map_continuous spatial spatialContinuous⟩

theorem cadlagJ1SpatialMap_continuous (spatial : State → OtherState)
    (spatialContinuous : Continuous spatial) :
    Continuous (cadlagJ1SpatialMap (Time := Time) spatial spatialContinuous) :=
  ((j1FunctionSpatialMap_continuous spatial spatialContinuous).comp continuous_subtype_val).subtype_mk _

theorem cadlagJ1SpatialMap_apply (spatial : State → OtherState) (spatialContinuous : Continuous spatial)
    (path : CadlagJ1Path Time State) (time : Time) :
    (cadlagJ1SpatialMap spatial spatialContinuous path).val.toFun time = spatial (path.val.toFun time) := rfl

/-- Same-clock pointwise displacement controls the actual J1 distance.
No additional clock identification is hidden in this lemma. -/
theorem cadlagJ1_dist_le_of_pointwise (first second : CadlagJ1Path Time State)
    (radius : ℝ) (radiusNonnegative : 0 ≤ radius)
    (close : ∀ time, dist (first.val.toFun time) (second.val.toFun time) ≤ radius) :
    dist first second ≤ radius :=
  (skorokhodJ1Distance_le_uniform first.val.toFun second.val.toFun).trans
    ((UniformFun.dist_le radiusNonnegative).mpr close)

local instance spatialJ1SourcePathMeasurableSpace : MeasurableSpace (CadlagJ1Path Time State) := borel _
local instance spatialJ1SourcePathBorelSpace : BorelSpace (CadlagJ1Path Time State) := ⟨rfl⟩
local instance spatialJ1TargetPathMeasurableSpace : MeasurableSpace (CadlagJ1Path Time OtherState) := borel _
local instance spatialJ1TargetPathBorelSpace : BorelSpace (CadlagJ1Path Time OtherState) := ⟨rfl⟩

def cadlagJ1SpatialLaw (spatial : State → OtherState) (spatialContinuous : Continuous spatial)
    (law : ProbabilityMeasure (CadlagJ1Path Time State)) : ProbabilityMeasure (CadlagJ1Path Time OtherState) :=
  law.map (cadlagJ1SpatialMap_continuous spatial spatialContinuous).measurable.aemeasurable

theorem cadlagJ1SpatialLaw_weak_convergence (spatial : State → OtherState)
    (spatialContinuous : Continuous spatial)
    (laws : ℕ → ProbabilityMeasure (CadlagJ1Path Time State))
    (law : ProbabilityMeasure (CadlagJ1Path Time State))
    (convergence : Tendsto laws atTop (𝓝 law)) :
    Tendsto (fun n => cadlagJ1SpatialLaw spatial spatialContinuous (laws n)) atTop
      (𝓝 (cadlagJ1SpatialLaw spatial spatialContinuous law)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous laws law convergence
    (cadlagJ1SpatialMap_continuous spatial spatialContinuous)

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.j1FunctionSpatialMap_continuous
#print axioms IGS.Sec31.DiscreteMarkov.cadlagJ1SpatialLaw_weak_convergence
