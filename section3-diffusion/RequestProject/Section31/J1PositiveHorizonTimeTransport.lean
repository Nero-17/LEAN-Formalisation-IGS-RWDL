import RequestProject.Section31.CadlagJ1TimeOrderIsoTransport
import RequestProject.Section31.FiniteSupportUnitJ1Transport

/-! Explicit affine identification of unit-time J1 paths with paths on
the literal physical interval [0,H]. Both laws and tightness are transported
by the genuine J1 homeomorphism, rather than by a uniform-metric argument. -/

namespace IGS.Sec31.DiscreteMarkov
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
set_option maxHeartbeats 4000000

def positiveHorizonTimeOrderIso (horizon : ℝ≥0) (positive : 0 < horizon) :
    UnitJ1Time ≃o Icc (0 : ℝ) (horizon : ℝ) where
  toFun := unitIntervalScale horizon
  invFun time := ⟨time.val / horizon, div_nonneg time.property.1 horizon.property,
    (div_le_one (show (0 : ℝ) < horizon from positive)).mpr time.property.2⟩
  left_inv time := by
    apply Subtype.ext
    change ((horizon : ℝ) * time.val) / horizon = time.val
    field_simp [ne_of_gt (show (0 : ℝ) < horizon from positive)]
  right_inv time := by
    apply Subtype.ext
    change (horizon : ℝ) * (time.val / horizon) = time.val
    field_simp [ne_of_gt (show (0 : ℝ) < horizon from positive)]
  map_rel_iff' := by
    intro first second
    change (horizon : ℝ) * first.val ≤ (horizon : ℝ) * second.val ↔ first.val ≤ second.val
    exact mul_le_mul_left (show (0 : ℝ) < horizon from positive)

variable {State : Type*} [MetricSpace State] [BoundedSpace State]
local instance physicalTimeBounded (horizon : ℝ≥0) : BoundedSpace (Icc (0 : ℝ) (horizon : ℝ)) :=
  ⟨Metric.isBounded_of_compactSpace⟩
local instance physicalPathMeasurable (horizon : ℝ≥0) :
    MeasurableSpace (CadlagJ1Path (Icc (0 : ℝ) (horizon : ℝ)) State) := borel _
local instance physicalPathBorel (horizon : ℝ≥0) :
    BorelSpace (CadlagJ1Path (Icc (0 : ℝ) (horizon : ℝ)) State) := ⟨rfl⟩

def unitToPhysicalCadlagJ1 (horizon : ℝ≥0) (positive : 0 < horizon) :
    UnitCadlagJ1Path State → CadlagJ1Path (Icc (0 : ℝ) (horizon : ℝ)) State :=
  cadlagJ1TimeOrderIsoMap (positiveHorizonTimeOrderIso horizon positive).symm

theorem unitToPhysicalCadlagJ1_continuous (horizon : ℝ≥0) (positive : 0 < horizon) :
    Continuous (unitToPhysicalCadlagJ1 (State := State) horizon positive) :=
  cadlagJ1TimeOrderIsoMap_continuous (positiveHorizonTimeOrderIso horizon positive).symm

theorem unitToPhysicalCadlagJ1_apply (horizon : ℝ≥0) (positive : 0 < horizon)
    (path : UnitCadlagJ1Path State) (time : Icc (0 : ℝ) (horizon : ℝ)) :
    (unitToPhysicalCadlagJ1 horizon positive path).val.toFun time =
      path.val.toFun ⟨time.val / horizon, div_nonneg time.property.1 horizon.property,
        (div_le_one (show (0 : ℝ) < horizon from positive)).mpr time.property.2⟩ := rfl

theorem unitToPhysicalCadlagJ1_weak_convergence (horizon : ℝ≥0) (positive : 0 < horizon)
    (laws : ℕ → ProbabilityMeasure (UnitCadlagJ1Path State)) (limit : ProbabilityMeasure (UnitCadlagJ1Path State))
    (converges : Tendsto laws atTop (𝓝 limit)) :
    Tendsto (fun index => ProbabilityMeasure.map (laws index)
      (unitToPhysicalCadlagJ1_continuous horizon positive).measurable.aemeasurable) atTop
      (𝓝 (ProbabilityMeasure.map limit (unitToPhysicalCadlagJ1_continuous horizon positive).measurable.aemeasurable)) :=
  cadlagJ1TimeOrderIsoMap_weak_convergence (positiveHorizonTimeOrderIso horizon positive).symm laws limit converges

theorem unitToPhysicalCadlagJ1_tight (horizon : ℝ≥0) (positive : 0 < horizon)
    (laws : ℕ → ProbabilityMeasure (UnitCadlagJ1Path State))
    (tight : IsTightMeasureSet (Set.range (fun index => (laws index : Measure _)))) :
    IsTightMeasureSet (Set.range (fun index =>
      (laws index : Measure _).map (unitToPhysicalCadlagJ1 horizon positive))) :=
  cadlagJ1TimeOrderIsoMap_tight (positiveHorizonTimeOrderIso horizon positive).symm laws tight

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.positiveHorizonTimeOrderIso
#print axioms IGS.Sec31.DiscreteMarkov.unitToPhysicalCadlagJ1_continuous
#print axioms IGS.Sec31.DiscreteMarkov.unitToPhysicalCadlagJ1_weak_convergence
#print axioms IGS.Sec31.DiscreteMarkov.unitToPhysicalCadlagJ1_tight
