import RequestProject.Section31.ExponentialPoissonProcessCertificate
import RequestProject.Section31.PoissonCountingProcessTimeScaling
import RequestProject.Section31.FiniteGraphExponentialPhysicalJ1PathLaw
import Mathlib.Probability.Independence.InfinitePi

/-! The Poisson count and the discrete walk are certified on the very same
product sample space used by the accepted holding J1 laws. No independent
process or coupling is selected to identify the physical path. -/

namespace IGS.Sec31.PoissonClock
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open IGS.Sec31.DiscreteMarkov
open scoped NNReal
set_option maxHeartbeats 3500000

variable {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
variable [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex]

def finiteGraphPoissonCount (time : ℝ≥0) (sample : (ℕ → Vertex) × (ℕ → ℝ)) : ℕ :=
  holdingJumpIndex sample.2 (time : ℝ)

theorem finiteGraphPoissonCount_process_laws
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (initial : ProbabilityMeasure Vertex) :
    PoissonCountingProcessLaws (finiteGraphExponentialSampleLaw graph degreePositive initial)
      finiteGraphPoissonCount 1 := by
  have clockLaw : HasLaw (Prod.snd : (ℕ → Vertex) × (ℕ → ℝ) → (ℕ → ℝ))
      exponentialHoldingTimeLaw (finiteGraphExponentialSampleLaw graph degreePositive initial) :=
    ⟨measurable_snd.aemeasurable,
      finiteGraphExponentialSampleLaw_clock_marginal graph degreePositive initial⟩
  have clockPreserving := Measure.quasiMeasurePreserving_snd
    (μ := pathLaw (EIGS.finiteGraphTransitionKernel graph degreePositive) initial.toMeasure)
    (ν := exponentialHoldingTimeLaw)
  refine ⟨fun time => (holdingJumpIndex_measurable (time : ℝ)).comp measurable_snd,
    clockPreserving.ae exponentialHoldingJumpIndex_initial,
    clockPreserving.ae exponentialHoldingJumpIndex_regular, ?_, ?_⟩
  · intro first last ordered
    simpa only [finiteGraphPoissonCount] using
      (exponentialHoldingJumpIndex_poisson_process.increments first last ordered).fun_comp clockLaw
  · intro times ordered
    change iIndepFun (fun index sample => holdingCountIncrement times index sample.2)
      (finiteGraphExponentialSampleLaw graph degreePositive initial)
    have measurableIncrement (index : ℕ) : Measurable
        (fun sample : (ℕ → Vertex) × (ℕ → ℝ) => holdingCountIncrement times index sample.2) :=
      (holdingCountIncrement_measurable times index).comp measurable_snd
    apply (iIndepFun_iff_map_fun_eq_infinitePi_map measurableIncrement).mpr
    have clockJoint := (iIndepFun_iff_map_fun_eq_infinitePi_map
      (holdingCountIncrement_measurable times)).mp
        (exponential_poisson_increments_iIndepFun times ordered)
    change (finiteGraphExponentialSampleLaw graph degreePositive initial).map
      ((fun holdingTimes => fun index => holdingCountIncrement times index holdingTimes) ∘ Prod.snd) = _
    rw [← Measure.map_map (measurable_pi_iff.mpr (holdingCountIncrement_measurable times)) measurable_snd,
      finiteGraphExponentialSampleLaw_clock_marginal, clockJoint]
    congr 1
    funext index
    have marginal := Measure.map_map
      (μ := finiteGraphExponentialSampleLaw graph degreePositive initial)
      (holdingCountIncrement_measurable times index)
      (show Measurable (Prod.snd : (ℕ → Vertex) × (ℕ → ℝ) → (ℕ → ℝ)) from measurable_snd)
    rw [finiteGraphExponentialSampleLaw_clock_marginal] at marginal
    exact marginal

theorem finiteGraphPoissonCount_independent_walk
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (initial : ProbabilityMeasure Vertex) :
    IndepFun (Prod.fst : (ℕ → Vertex) × (ℕ → ℝ) → (ℕ → Vertex))
      (fun sample => fun time : ℝ≥0 => finiteGraphPoissonCount time sample)
      (finiteGraphExponentialSampleLaw graph degreePositive initial) := by
  have measurableCounts : Measurable
      (fun holdingTimes : ℕ → ℝ => fun time : ℝ≥0 => holdingJumpIndex holdingTimes (time : ℝ)) :=
    measurable_pi_iff.mpr (fun time => holdingJumpIndex_measurable (time : ℝ))
  exact (finiteGraphExponentialSampleLaw_independent graph degreePositive initial).comp
    measurable_id measurableCounts

theorem finiteGraphPoissonCount_increment_vector_law
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (initial : ProbabilityMeasure Vertex)
    (times : ℕ → ℝ≥0) (ordered : Monotone times) (count : ℕ) :
    (finiteGraphExponentialSampleLaw graph degreePositive initial).map
      (fun sample => fun index : Fin count =>
        finiteGraphPoissonCount (times (index.val + 1)) sample -
          finiteGraphPoissonCount (times index.val) sample) =
      Measure.pi (fun index : Fin count => poissonMeasure (times (index.val + 1) - times index.val)) := by
  change (finiteGraphExponentialSampleLaw graph degreePositive initial).map
    ((fun holdingTimes => fun index : Fin count => holdingCountIncrement times index.val holdingTimes) ∘ Prod.snd) = _
  rw [← Measure.map_map (measurable_pi_iff.mpr
    (fun index : Fin count => holdingCountIncrement_measurable times index.val)) measurable_snd,
    finiteGraphExponentialSampleLaw_clock_marginal,
    exponential_poisson_increment_vector_law times ordered count]

theorem finiteGraphPoissonCount_scaled_process_laws
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (initial : ProbabilityMeasure Vertex)
    (speed : ℝ≥0) (speedPositive : 0 < speed) :
    PoissonCountingProcessLaws (finiteGraphExponentialSampleLaw graph degreePositive initial)
      (fun time sample => finiteGraphPoissonCount (speed * time) sample) speed := by
  simpa only [one_mul] using
    (finiteGraphPoissonCount_process_laws graph degreePositive initial).timeScale speed speedPositive

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
local instance poissonIdentificationStateBounded : BoundedSpace State := ⟨Metric.isBounded_of_compactSpace⟩
local instance poissonIdentificationTimeBounded (horizon : ℝ≥0) :
    BoundedSpace (Icc (0 : ℝ) (horizon : ℝ)) := ⟨Metric.isBounded_of_compactSpace⟩

theorem exponentialHoldingPhysicalJ1Sample_is_poissonized_walk
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (initial : ProbabilityMeasure Vertex)
    (embedding : Vertex → State) (rate : ℝ≥0) (ratePositive : 0 < rate)
    (horizon : ℝ≥0) (horizonPositive : 0 < horizon) :
    ∀ᵐ sample ∂finiteGraphExponentialSampleLaw graph degreePositive initial,
      ∀ time : Icc (0 : ℝ) (horizon : ℝ),
        (exponentialHoldingPhysicalJ1Sample embedding (rate : ℝ)
          (show (0 : ℝ) < rate from ratePositive) horizon horizonPositive sample).val.toFun time =
        embedding (sample.1 (finiteGraphPoissonCount
          (rate * ⟨time.val, time.property.1⟩) sample)) := by
  filter_upwards [finiteGraphExponentialSampleLaw_clock_regular graph degreePositive initial]
    with sample regular
  intro time
  exact exponentialHoldingPhysicalJ1Sample_apply embedding rate ratePositive horizon horizonPositive
    sample regular time

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.finiteGraphPoissonCount_process_laws
#print axioms IGS.Sec31.PoissonClock.finiteGraphPoissonCount_independent_walk
#print axioms IGS.Sec31.PoissonClock.finiteGraphPoissonCount_increment_vector_law
#print axioms IGS.Sec31.PoissonClock.finiteGraphPoissonCount_scaled_process_laws
#print axioms IGS.Sec31.PoissonClock.exponentialHoldingPhysicalJ1Sample_is_poissonized_walk
