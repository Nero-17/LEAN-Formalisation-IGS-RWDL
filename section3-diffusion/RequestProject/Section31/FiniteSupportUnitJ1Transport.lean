import RequestProject.Section31.FiniteSupportCadlagJ1Transport
import RequestProject.Section31.J1UnitGridReconstruction
import Mathlib.MeasureTheory.Measure.Tight

namespace IGS.Sec31.DiscreteMarkov
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal UniformConvergence

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable {History : ℕ → Type*} [∀ level, Finite (History level)]

local instance unitTransportStateBounded : BoundedSpace State := ⟨Metric.isBounded_of_compactSpace⟩
local instance unitTransportIntervalBounded (horizon : ℝ≥0) :
    BoundedSpace (Icc (0 : ℝ) (horizon : ℝ)) := ⟨Metric.isBounded_of_compactSpace⟩

def unitIntervalScale (horizon : ℝ≥0) (time : UnitJ1Time) : Icc (0 : ℝ) (horizon : ℝ) :=
  ⟨(horizon : ℝ) * time.val, mul_nonneg horizon.property time.property.1,
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left time.property.2 horizon.property⟩

theorem unitIntervalScale_continuous (horizon : ℝ≥0) : Continuous (unitIntervalScale horizon) :=
  (continuous_const.mul continuous_subtype_val).subtype_mk _

def finiteSupportPathToUnitCadlagJ1 (horizon : ℝ≥0) (horizonPositive : 0 < horizon)
    (paths : (level : ℕ) → History level → Icc (0 : ℝ) (horizon : ℝ) → State)
    (supportsCadlag : ∀ level history, IsCadlagPath (paths level history))
    (path : FiniteSupportPathSpace paths) : UnitCadlagJ1Path State :=
  ⟨⟨fun time => UniformFun.toFun path.val (unitIntervalScale horizon time)⟩,
    (finiteSupportPathSpace_isCadlag paths supportsCadlag path).comp_continuous_strictMono
      (unitIntervalScale horizon) (unitIntervalScale_continuous horizon)
        (fun first second ordered => by
          change (horizon : ℝ) * first.val < (horizon : ℝ) * second.val
          exact mul_lt_mul_of_pos_left ordered (show (0 : ℝ) < horizon from horizonPositive))⟩

theorem finiteSupportPathToUnitCadlagJ1_lipschitz (horizon : ℝ≥0) (horizonPositive : 0 < horizon)
    (paths : (level : ℕ) → History level → Icc (0 : ℝ) (horizon : ℝ) → State)
    (supportsCadlag : ∀ level history, IsCadlagPath (paths level history)) :
    LipschitzWith 1 (finiteSupportPathToUnitCadlagJ1 horizon horizonPositive paths supportsCadlag) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  change skorokhodJ1Distance
    (fun time => UniformFun.toFun first.val (unitIntervalScale horizon time))
    (fun time => UniformFun.toFun second.val (unitIntervalScale horizon time)) ≤
      (1 : ℝ≥0) * dist first second
  simp only [NNReal.coe_one, one_mul]
  apply (skorokhodJ1Distance_le_uniform _ _).trans
  apply (UniformFun.dist_le dist_nonneg).mpr
  intro time
  exact uniformFunction_dist_eval_le (UniformFun.toFun first.val) (UniformFun.toFun second.val)
    (unitIntervalScale horizon time)

theorem finiteSupportPathToUnitCadlagJ1_measurable (horizon : ℝ≥0) (horizonPositive : 0 < horizon)
    (paths : (level : ℕ) → History level → Icc (0 : ℝ) (horizon : ℝ) → State)
    (supportsCadlag : ∀ level history, IsCadlagPath (paths level history)) :
    Measurable (finiteSupportPathToUnitCadlagJ1 horizon horizonPositive paths supportsCadlag) :=
  (finiteSupportPathToUnitCadlagJ1_lipschitz horizon horizonPositive paths supportsCadlag).continuous.measurable

theorem finiteSupportPathToUnitCadlagJ1_tight (horizon : ℝ≥0) (horizonPositive : 0 < horizon)
    (paths : (level : ℕ) → History level → Icc (0 : ℝ) (horizon : ℝ) → State)
    (supportsCadlag : ∀ level history, IsCadlagPath (paths level history))
    (laws : ℕ → ProbabilityMeasure (FiniteSupportPathSpace paths))
    (tight : IsTightMeasureSet (Set.range (fun level => (laws level : Measure (FiniteSupportPathSpace paths))))) :
    IsTightMeasureSet (Set.range (fun level => (laws level : Measure (FiniteSupportPathSpace paths)).map
      (finiteSupportPathToUnitCadlagJ1 horizon horizonPositive paths supportsCadlag))) := by
  simpa only [← Set.range_comp', Function.comp_def] using tight.map
    (finiteSupportPathToUnitCadlagJ1_lipschitz horizon horizonPositive paths supportsCadlag).continuous

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPathToUnitCadlagJ1_lipschitz
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPathToUnitCadlagJ1_measurable
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPathToUnitCadlagJ1_tight
