import RequestProject.Section31.FiniteGraphExponentialHoldingProcess
import RequestProject.Section31.ExponentialHoldingFiniteJumpRepresentation
import RequestProject.Section31.J1FiniteJumpGridApproximation

/-! A genuine finite-horizon J1 Borel probability law for the actual finite
graph walk with independent exponential holdings. Measurability follows
from fixed-grid J1 approximation and the actual finite-jump representation;
no uniform-Borel path pushforward or Polish-space theorem is assumed. -/

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory Filter Set Topology
open IGS.Sec31.DiscreteMarkov
open EIGS
open scoped NNReal
noncomputable section
set_option maxHeartbeats 5000000

def unitHoldingCadlagPath {State : Type*} [MetricSpace State]
    (trajectory : ℕ → State) (holdingTimes : ℕ → ℝ)
    (positive : ∀ index, 0 < holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
    (horizon : ℝ) (horizonPositive : 0 < horizon) : UnitCadlagJ1Path State := by
  let clock : UnitJ1Time → ℝ≥0 := fun time => ⟨horizon * time.val, mul_nonneg horizonPositive.le time.property.1⟩
  have clockContinuous : Continuous clock := (continuous_const.mul continuous_subtype_val).subtype_mk _
  have clockStrict : StrictMono clock := fun _ _ ordered => mul_lt_mul_of_pos_left ordered horizonPositive
  refine ⟨⟨fun time => holdingTimePath trajectory holdingTimes (horizon * time.val)⟩, ?_⟩
  exact (holdingTimePathNNReal_isCadlag trajectory holdingTimes positive nonexplosion).comp_continuous_strictMono
    clock clockContinuous clockStrict

def exponentialClockRegular (holdingTimes : ℕ → ℝ) : Prop :=
  (∀ index, 0 < holdingTimes index) ∧ Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop

def exponentialHoldingJ1Sample {Vertex State : Type*} [MetricSpace State]
    (embedding : Vertex → State) (horizon : ℝ) (horizonPositive : 0 < horizon)
    (sample : (ℕ → Vertex) × (ℕ → ℝ)) : UnitCadlagJ1Path State := by
  classical
  exact if regular : exponentialClockRegular sample.2 then
    unitHoldingCadlagPath (fun index => embedding (sample.1 index)) sample.2 regular.1 regular.2 horizon horizonPositive
  else ⟨⟨fun _ => embedding (sample.1 0)⟩,
    IGS.Sec31.DiscreteMarkov.Continuous.isCadlagPath continuous_const⟩

variable {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
variable [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex]
variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

theorem finiteGraphExponentialSampleLaw_clock_regular
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (initial : ProbabilityMeasure Vertex) :
    ∀ᵐ sample ∂finiteGraphExponentialSampleLaw graph degreePositive initial, exponentialClockRegular sample.2 := by
  have positive := (Measure.quasiMeasurePreserving_snd
    (μ := pathLaw (finiteGraphTransitionKernel graph degreePositive) (initial : Measure Vertex))
    (ν := exponentialHoldingTimeLaw)).ae exponentialHoldingTimeLaw_positive
  have nonexplosion := (Measure.quasiMeasurePreserving_snd
    (μ := pathLaw (finiteGraphTransitionKernel graph degreePositive) (initial : Measure Vertex))
    (ν := exponentialHoldingTimeLaw)).ae exponentialHoldingTimeLaw_nonexplosion
  exact positive.and nonexplosion

theorem exponentialHoldingJ1Sample_aemeasurable
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (initial : ProbabilityMeasure Vertex)
    (embedding : Vertex → State) (horizon : ℝ) (horizonPositive : 0 < horizon) :
    AEMeasurable (exponentialHoldingJ1Sample embedding horizon horizonPositive)
      (finiteGraphExponentialSampleLaw graph degreePositive initial) := by
  have regular := finiteGraphExponentialSampleLaw_clock_regular graph degreePositive initial
  apply unitCadlagJ1Sample_aemeasurable_of_finite_jumps
    (finiteGraphExponentialSampleLaw graph degreePositive initial)
    (exponentialHoldingJ1Sample embedding horizon horizonPositive)
  · intro time
    have equality : ∀ᵐ sample ∂finiteGraphExponentialSampleLaw graph degreePositive initial,
        (exponentialHoldingJ1Sample embedding horizon horizonPositive sample).val.toFun time =
          embedding (holdingTimePath sample.1 sample.2 (horizon * time.val)) := by
      filter_upwards [regular] with sample clock
      simp only [exponentialHoldingJ1Sample, dif_pos clock, unitHoldingCadlagPath, holdingTimePath]
    have measurableEvaluation : Measurable (fun sample : (ℕ → Vertex) × (ℕ → ℝ) =>
        embedding (holdingTimePath sample.1 sample.2 (horizon * time.val))) :=
      (measurable_of_countable embedding).comp (holdingTimePath_measurable (horizon * time.val))
    exact measurableEvaluation.aemeasurable.congr equality.symm
  · filter_upwards [regular] with sample clock
    obtain ⟨count, knots, increasing, interior, states, endpoint, representation⟩ :=
      holdingTimePath_finite_endpoint_jump_representation (fun index => embedding (sample.1 index))
        sample.2 clock.1 clock.2 horizon horizonPositive
    refine ⟨count, knots, increasing, interior, states, endpoint, ?_⟩
    simpa only [exponentialHoldingJ1Sample, dif_pos clock, unitHoldingCadlagPath, holdingTimePath] using representation

def finiteGraphExponentialJ1Law
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (initial : ProbabilityMeasure Vertex)
    (embedding : Vertex → State) (horizon : ℝ) (horizonPositive : 0 < horizon) :
    ProbabilityMeasure (UnitCadlagJ1Path State) :=
  (⟨finiteGraphExponentialSampleLaw graph degreePositive initial, inferInstance⟩ :
    ProbabilityMeasure ((ℕ → Vertex) × (ℕ → ℝ))).map
      (exponentialHoldingJ1Sample_aemeasurable graph degreePositive initial embedding horizon horizonPositive)

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.unitHoldingCadlagPath
#print axioms IGS.Sec31.PoissonClock.finiteGraphExponentialSampleLaw_clock_regular
#print axioms IGS.Sec31.PoissonClock.exponentialHoldingJ1Sample_aemeasurable
#print axioms IGS.Sec31.PoissonClock.finiteGraphExponentialJ1Law
