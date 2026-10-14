import RequestProject.Section31.CadlagJ1CarrierInstances
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tight

/-! Increasing order homeomorphisms of compact time intervals induce
homeomorphisms of the genuine J1 path carriers. Clock changes are conjugated
by the time order isomorphism; the J1 distance is never replaced by sup distance. -/

namespace IGS.Sec31.DiscreteMarkov
noncomputable section
open Set Filter Topology MeasureTheory
open scoped UniformConvergence
set_option maxHeartbeats 4000000

variable {Time OtherTime State : Type*}
variable [LinearOrder Time] [MetricSpace Time] [OrderTopology Time] [CompactSpace Time]
variable [LinearOrder OtherTime] [MetricSpace OtherTime] [OrderTopology OtherTime] [CompactSpace OtherTime]
variable [MetricSpace State] [BoundedSpace State]
local instance timeTransportSourceBounded : BoundedSpace Time := ⟨Metric.isBounded_of_compactSpace⟩
local instance timeTransportTargetBounded : BoundedSpace OtherTime := ⟨Metric.isBounded_of_compactSpace⟩

def j1FunctionTimeOrderIsoMap (timeMap : OtherTime ≃o Time) (path : J1Function Time State) :
    J1Function OtherTime State := ⟨path.toFun ∘ timeMap⟩

theorem j1FunctionTimeOrderIsoMap_continuous (timeMap : OtherTime ≃o Time) :
    Continuous (j1FunctionTimeOrderIsoMap (State := State) timeMap) := by
  have inverseUniform := CompactSpace.uniformContinuous_of_continuous timeMap.symm.toHomeomorph.continuous
  apply continuous_iff_continuousAt.mpr
  intro path
  apply Metric.continuousAt_iff.mpr
  intro epsilon positive
  obtain ⟨duration, durationPositive, inverseClose⟩ :=
    Metric.uniformContinuous_iff.mp inverseUniform (epsilon / 2) (half_pos positive)
  refine ⟨min (epsilon / 2) duration, lt_min (half_pos positive) durationPositive, ?_⟩
  intro other near
  change skorokhodJ1Distance other.toFun path.toFun < min (epsilon / 2) duration at near
  obtain ⟨change, costSmall⟩ := exists_lt_of_ciInf_lt near
  let conjugated := timeMap.trans (change.trans timeMap.symm)
  have mappedCost : skorokhodJ1Cost (other.toFun ∘ timeMap) (path.toFun ∘ timeMap) conjugated ≤ epsilon / 2 := by
    apply max_le
    · apply (UniformFun.dist_le (half_pos positive).le).mpr
      intro time
      have clockSmall : dist (change (timeMap time)) (timeMap time) < duration :=
        ((skorokhodJ1Cost_clock_le other.toFun path.toFun change (timeMap time)).trans_lt costSmall).trans_le
          (min_le_right _ _)
      simpa only [conjugated, OrderIso.trans_apply, OrderIso.symm_apply_apply, UniformFun.toFun_ofFun,
        id_eq] using (inverseClose clockSmall).le
    · apply (UniformFun.dist_le (half_pos positive).le).mpr
      intro time
      have stateSmall := (skorokhodJ1Cost_path_le other.toFun path.toFun change (timeMap time)).trans
        (costSmall.le.trans (min_le_left _ _))
      simpa only [conjugated, OrderIso.trans_apply, OrderIso.apply_symm_apply, UniformFun.toFun_ofFun,
        Function.comp_def] using stateSmall
  exact ((skorokhodJ1Distance_le_cost (other.toFun ∘ timeMap) (path.toFun ∘ timeMap) conjugated).trans mappedCost).trans_lt
    (half_lt_self positive)

def cadlagJ1TimeOrderIsoMap (timeMap : OtherTime ≃o Time) (path : CadlagJ1Path Time State) :
    CadlagJ1Path OtherTime State :=
  ⟨j1FunctionTimeOrderIsoMap timeMap path.val,
    path.property.comp_continuous_strictMono timeMap timeMap.toHomeomorph.continuous timeMap.strictMono⟩

theorem cadlagJ1TimeOrderIsoMap_continuous (timeMap : OtherTime ≃o Time) :
    Continuous (cadlagJ1TimeOrderIsoMap (State := State) timeMap) :=
  ((j1FunctionTimeOrderIsoMap_continuous timeMap).comp continuous_subtype_val).subtype_mk _

def cadlagJ1TimeOrderIsoHomeomorph (timeMap : OtherTime ≃o Time) :
    CadlagJ1Path Time State ≃ₜ CadlagJ1Path OtherTime State where
  toFun := cadlagJ1TimeOrderIsoMap timeMap
  invFun := cadlagJ1TimeOrderIsoMap timeMap.symm
  left_inv path := by
    rcases path with ⟨⟨function⟩, regular⟩
    apply Subtype.ext
    simp only [cadlagJ1TimeOrderIsoMap, j1FunctionTimeOrderIsoMap, Function.comp_def,
      OrderIso.apply_symm_apply]
  right_inv path := by
    rcases path with ⟨⟨function⟩, regular⟩
    apply Subtype.ext
    simp only [cadlagJ1TimeOrderIsoMap, j1FunctionTimeOrderIsoMap, Function.comp_def,
      OrderIso.symm_apply_apply]
  continuous_toFun := cadlagJ1TimeOrderIsoMap_continuous timeMap
  continuous_invFun := cadlagJ1TimeOrderIsoMap_continuous timeMap.symm

local instance timeTransportSourcePathMeasurable : MeasurableSpace (CadlagJ1Path Time State) := borel _
local instance timeTransportSourcePathBorel : BorelSpace (CadlagJ1Path Time State) := ⟨rfl⟩
local instance timeTransportTargetPathMeasurable : MeasurableSpace (CadlagJ1Path OtherTime State) := borel _
local instance timeTransportTargetPathBorel : BorelSpace (CadlagJ1Path OtherTime State) := ⟨rfl⟩

theorem cadlagJ1TimeOrderIsoMap_weak_convergence (timeMap : OtherTime ≃o Time)
    (laws : ℕ → ProbabilityMeasure (CadlagJ1Path Time State)) (limit : ProbabilityMeasure (CadlagJ1Path Time State))
    (converges : Tendsto laws atTop (𝓝 limit)) :
    Tendsto (fun index => ProbabilityMeasure.map (laws index)
      (cadlagJ1TimeOrderIsoMap_continuous timeMap).measurable.aemeasurable) atTop
      (𝓝 (ProbabilityMeasure.map limit (cadlagJ1TimeOrderIsoMap_continuous timeMap).measurable.aemeasurable)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous laws limit converges
    (cadlagJ1TimeOrderIsoMap_continuous timeMap)

theorem cadlagJ1TimeOrderIsoMap_tight (timeMap : OtherTime ≃o Time)
    (laws : ℕ → ProbabilityMeasure (CadlagJ1Path Time State))
    (tight : IsTightMeasureSet (Set.range (fun index => (laws index : Measure _)))) :
    IsTightMeasureSet (Set.range (fun index =>
      (laws index : Measure _).map (cadlagJ1TimeOrderIsoMap timeMap))) := by
  simpa only [← Set.range_comp', Function.comp_def] using tight.map
    (cadlagJ1TimeOrderIsoMap_continuous timeMap)

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.cadlagJ1TimeOrderIsoHomeomorph
#print axioms IGS.Sec31.DiscreteMarkov.cadlagJ1TimeOrderIsoMap_weak_convergence
#print axioms IGS.Sec31.DiscreteMarkov.cadlagJ1TimeOrderIsoMap_tight
