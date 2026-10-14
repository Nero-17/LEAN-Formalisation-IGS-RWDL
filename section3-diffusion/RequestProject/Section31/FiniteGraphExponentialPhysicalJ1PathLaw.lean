import RequestProject.Section31.FiniteGraphExponentialJ1PathLaw
import RequestProject.Section31.J1PositiveHorizonTimeTransport

/-! Literal physical-interval J1 laws of the actual finite-graph walk with
independent exponential holdings. The sampler at physical time t is exactly
the embedded walk at the actual renewal index for rate*t. -/

namespace IGS.Sec31.PoissonClock
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open IGS.Sec31.DiscreteMarkov EIGS
open scoped NNReal
set_option maxHeartbeats 4000000

variable {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
variable [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex]
variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
local instance physicalHoldingStateBounded : BoundedSpace State := ⟨Metric.isBounded_of_compactSpace⟩
local instance physicalHoldingTimeBounded (horizon : ℝ≥0) : BoundedSpace (Icc (0 : ℝ) (horizon : ℝ)) :=
  ⟨Metric.isBounded_of_compactSpace⟩
local instance physicalHoldingPathMeasurable (horizon : ℝ≥0) :
    MeasurableSpace (CadlagJ1Path (Icc (0 : ℝ) (horizon : ℝ)) State) := borel _
local instance physicalHoldingPathBorel (horizon : ℝ≥0) :
    BorelSpace (CadlagJ1Path (Icc (0 : ℝ) (horizon : ℝ)) State) := ⟨rfl⟩

def exponentialHoldingPhysicalJ1Sample (embedding : Vertex → State)
    (rate : ℝ) (ratePositive : 0 < rate) (horizon : ℝ≥0) (horizonPositive : 0 < horizon)
    (sample : (ℕ → Vertex) × (ℕ → ℝ)) : CadlagJ1Path (Icc (0 : ℝ) (horizon : ℝ)) State :=
  unitToPhysicalCadlagJ1 horizon horizonPositive
    (exponentialHoldingJ1Sample embedding (rate * horizon)
      (mul_pos ratePositive (show (0 : ℝ) < horizon from horizonPositive)) sample)

theorem exponentialHoldingPhysicalJ1Sample_apply (embedding : Vertex → State)
    (rate : ℝ) (ratePositive : 0 < rate) (horizon : ℝ≥0) (horizonPositive : 0 < horizon)
    (sample : (ℕ → Vertex) × (ℕ → ℝ)) (regular : exponentialClockRegular sample.2)
    (time : Icc (0 : ℝ) (horizon : ℝ)) :
    (exponentialHoldingPhysicalJ1Sample embedding rate ratePositive horizon horizonPositive sample).val.toFun time =
      embedding (holdingTimePath sample.1 sample.2 (rate * time.val)) := by
  unfold exponentialHoldingPhysicalJ1Sample
  rw [unitToPhysicalCadlagJ1_apply]
  have clockEquality : (rate * horizon) * (time.val / horizon) = rate * time.val := by
    field_simp [ne_of_gt (show (0 : ℝ) < horizon from horizonPositive)] <;> ring
  simp only [exponentialHoldingJ1Sample, dif_pos regular, unitHoldingCadlagPath, clockEquality, holdingTimePath]

def finiteGraphExponentialPhysicalJ1Law
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (initial : ProbabilityMeasure Vertex)
    (embedding : Vertex → State) (rate : ℝ) (ratePositive : 0 < rate)
    (horizon : ℝ≥0) (horizonPositive : 0 < horizon) :
    ProbabilityMeasure (CadlagJ1Path (Icc (0 : ℝ) (horizon : ℝ)) State) :=
  ProbabilityMeasure.map
    (finiteGraphExponentialJ1Law graph degreePositive initial embedding (rate * horizon)
      (mul_pos ratePositive (show (0 : ℝ) < horizon from horizonPositive)))
    (unitToPhysicalCadlagJ1_continuous horizon horizonPositive).measurable.aemeasurable

theorem finiteGraphExponentialPhysicalJ1Law_eq_product_map
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (initial : ProbabilityMeasure Vertex)
    (embedding : Vertex → State) (rate : ℝ) (ratePositive : 0 < rate)
    (horizon : ℝ≥0) (horizonPositive : 0 < horizon) :
    (finiteGraphExponentialPhysicalJ1Law graph degreePositive initial embedding rate ratePositive
      horizon horizonPositive : Measure _) =
      (finiteGraphExponentialSampleLaw graph degreePositive initial).map
        (exponentialHoldingPhysicalJ1Sample embedding rate ratePositive horizon horizonPositive) := by
  simp only [finiteGraphExponentialPhysicalJ1Law, finiteGraphExponentialJ1Law, ProbabilityMeasure.toMeasure_map]
  rw [AEMeasurable.map_map_of_aemeasurable
    (unitToPhysicalCadlagJ1_continuous horizon horizonPositive).measurable.aemeasurable
    (exponentialHoldingJ1Sample_aemeasurable graph degreePositive initial embedding (rate * horizon)
      (mul_pos ratePositive (show (0 : ℝ) < horizon from horizonPositive)))]
  rfl

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.exponentialHoldingPhysicalJ1Sample_apply
#print axioms IGS.Sec31.PoissonClock.finiteGraphExponentialPhysicalJ1Law_eq_product_map
