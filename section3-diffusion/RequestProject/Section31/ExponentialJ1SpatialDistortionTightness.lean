import RequestProject.Section31.ExponentialJ1SpatialLawTransport
import RequestProject.Section31.FiniteGraphExponentialJ1LawTightness
import RequestProject.Section31.TightnessFromConstructedCouplings

namespace IGS.Sec31.PoissonClock
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open IGS.Sec31.DiscreteMarkov EIGS
open scoped Topology
set_option maxHeartbeats 5000000

variable {State Ambient : Type} [MetricSpace State] [CompactSpace State]
variable [MetricSpace Ambient] [CompactSpace Ambient]
variable [MeasurableSpace State] [BorelSpace State] [MeasurableSpace Ambient] [BorelSpace Ambient]
local instance exponentialDistortionSourceBounded : BoundedSpace State := ⟨Metric.isBounded_of_compactSpace⟩
local instance exponentialDistortionTargetBounded : BoundedSpace Ambient := ⟨Metric.isBounded_of_compactSpace⟩

theorem finiteGraphExponentialJ1Laws_tight_of_spatial_distortion
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
    (nativeTight : IsTightMeasureSet (Set.range (fun level =>
      (finiteGraphExponentialJ1Law (graphs level) (degreePositive level) (initial level) (projection level)
        (horizons level) (horizonsPositive level) : Measure (UnitCadlagJ1Path State))))) :
    IsTightMeasureSet (Set.range (fun level =>
      (finiteGraphExponentialJ1Law (graphs level) (degreePositive level) (initial level) (sources level)
        (horizons level) (horizonsPositive level) : Measure (UnitCadlagJ1Path Ambient)))) := by
  classical
  let joint := fun level => finiteGraphExponentialSampleLaw (graphs level) (degreePositive level) (initial level)
  let source := fun level => exponentialHoldingJ1Sample (spatial ∘ projection level) (horizons level) (horizonsPositive level)
  let target := fun level => exponentialHoldingJ1Sample (sources level) (horizons level) (horizonsPositive level)
  let sourceLaws := fun level => finiteGraphExponentialJ1Law (graphs level) (degreePositive level) (initial level)
    (spatial ∘ projection level) (horizons level) (horizonsPositive level)
  let targetLaws := fun level => finiteGraphExponentialJ1Law (graphs level) (degreePositive level) (initial level)
    (sources level) (horizons level) (horizonsPositive level)
  have sourceTight := finiteGraphExponentialJ1Laws_spatial_tight Vertex graphs degreePositive initial projection
    spatial spatialContinuous horizons horizonsPositive nativeTight
  apply isTight_of_constructed_couplings (fun level => (ℕ → Vertex level) × (ℕ → ℝ)) joint source target
    (fun level => exponentialHoldingJ1Sample_aemeasurable _ _ _ _ _ _)
    (fun level => exponentialHoldingJ1Sample_aemeasurable _ _ _ _ _ _)
    sourceLaws targetLaws (fun _ => rfl) (fun _ => rfl) sourceTight
    (fun level => finiteGraphExponentialJ1Law_isTight _ _ _ _ _ _)
  intro radius error radiusPositive errorPositive
  filter_upwards [radiiZero.eventually (gt_mem_nhds radiusPositive)] with level small
  refine ⟨∅, by simp only [measureReal_empty]; exact errorPositive.le, ?_⟩
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

#print axioms IGS.Sec31.PoissonClock.finiteGraphExponentialJ1Laws_tight_of_spatial_distortion
