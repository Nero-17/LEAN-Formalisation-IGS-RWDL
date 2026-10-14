import RequestProject.Section31.ExponentialJ1SpatialLawTransport
import RequestProject.Section31.ProbabilityConstructedCouplingWeakLimit

/-! Exact same-clock spatial transport of holding-law weak convergence
under vanishing actual vertex distortion. No tightness/Polish or target
weak-limit hypothesis is used. -/

namespace IGS.Sec31.PoissonClock
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open IGS.Sec31.DiscreteMarkov EIGS
open scoped Topology
set_option maxHeartbeats 5000000

variable {State Ambient : Type} [MetricSpace State] [CompactSpace State]
variable [MetricSpace Ambient] [CompactSpace Ambient]
variable [MeasurableSpace State] [BorelSpace State] [MeasurableSpace Ambient] [BorelSpace Ambient]
local instance exponentialWeakSourceBounded : BoundedSpace State := ⟨Metric.isBounded_of_compactSpace⟩
local instance exponentialWeakTargetBounded : BoundedSpace Ambient := ⟨Metric.isBounded_of_compactSpace⟩

theorem finiteGraphExponentialJ1Laws_tendsto_of_spatial_distortion
    (Vertex : ℕ → Type) [∀ level, Fintype (Vertex level)] [∀ level, DecidableEq (Vertex level)]
    [∀ level, MeasurableSpace (Vertex level)] [∀ level, MeasurableSingletonClass (Vertex level)]
    (graphs : ∀ level, SimpleGraph (Vertex level)) [∀ level, DecidableRel (graphs level).Adj]
    (degreePositive : ∀ level vertex, 0 < (graphs level).degree vertex)
    (initial : ∀ level, ProbabilityMeasure (Vertex level))
    (projection : ∀ level, Vertex level → State) (sources : ∀ level, Vertex level → Ambient)
    (spatial : State → Ambient) (spatialContinuous : Continuous spatial)
    (horizons : ℕ → ℝ) (horizonsPositive : ∀ level, 0 < horizons level)
    (radii : ℕ → ℝ) (radiiZero : Tendsto radii atTop (𝓝 0))
    (displacement : ∀ level vertex, dist (sources level vertex) (spatial (projection level vertex)) ≤ radii level)
    (limit : ProbabilityMeasure (UnitCadlagJ1Path State))
    (nativeConverges : Tendsto (fun level =>
      finiteGraphExponentialJ1Law (graphs level) (degreePositive level) (initial level) (projection level)
        (horizons level) (horizonsPositive level)) atTop (𝓝 limit)) :
    Tendsto (fun level => finiteGraphExponentialJ1Law (graphs level) (degreePositive level) (initial level)
      (sources level) (horizons level) (horizonsPositive level)) atTop
      (𝓝 (ProbabilityMeasure.map limit (cadlagJ1SpatialMap_continuous spatial spatialContinuous).measurable.aemeasurable)) := by
  classical
  let joint := fun level => finiteGraphExponentialSampleLaw (graphs level) (degreePositive level) (initial level)
  let samples := fun level => (⟨joint level, inferInstance⟩ : ProbabilityMeasure ((ℕ → Vertex level) × (ℕ → ℝ)))
  let source := fun level => exponentialHoldingJ1Sample (spatial ∘ projection level) (horizons level) (horizonsPositive level)
  let target := fun level => exponentialHoldingJ1Sample (sources level) (horizons level) (horizonsPositive level)
  have sourceConverges : Tendsto
      (fun level => ProbabilityMeasure.map (samples level)
        (exponentialHoldingJ1Sample_aemeasurable (graphs level) (degreePositive level) (initial level)
          (spatial ∘ projection level) (horizons level) (horizonsPositive level))) atTop
      (𝓝 (ProbabilityMeasure.map limit (cadlagJ1SpatialMap_continuous spatial spatialContinuous).measurable.aemeasurable)) := by
    have mapped := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ nativeConverges
      (cadlagJ1SpatialMap_continuous spatial spatialContinuous)
    simpa only [finiteGraphExponentialJ1Law_spatial_map] using mapped
  apply IGS.Sec31.probability_maps_same_limit_of_constructed_coupling samples source target
    (fun level => exponentialHoldingJ1Sample_aemeasurable _ _ _ _ _ _)
    (fun level => exponentialHoldingJ1Sample_aemeasurable _ _ _ _ _ _) _ _ sourceConverges
  intro radius error radiusPositive errorPositive
  filter_upwards [radiiZero.eventually (gt_mem_nhds radiusPositive)] with level small
  refine ⟨∅, MeasurableSet.empty, by simp only [measureReal_empty]; exact errorPositive.le, ?_⟩
  filter_upwards [finiteGraphExponentialSampleLaw_clock_regular (graphs level) (degreePositive level) (initial level)]
    with sample regular
  intro outside
  change skorokhodJ1Distance (target level sample).val.toFun (source level sample).val.toFun ≤ radius
  apply (skorokhodJ1Distance_le_uniform _ _).trans
  apply (UniformFun.dist_le radiusPositive.le).mpr
  intro time
  have bound := (displacement level (holdingTimePath sample.1 sample.2 (horizons level * time.val))).trans small.le
  simpa only [source, target, exponentialHoldingJ1Sample, dif_pos regular, unitHoldingCadlagPath,
    Function.comp_def, holdingTimePath] using bound

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.finiteGraphExponentialJ1Laws_tendsto_of_spatial_distortion
