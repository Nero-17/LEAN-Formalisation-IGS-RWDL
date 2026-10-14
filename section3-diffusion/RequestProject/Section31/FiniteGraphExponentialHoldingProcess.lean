import RequestProject.Section31.ExponentialHoldingTimePaths
import RequestProject.Section31.UniformCadlagClosed
import RequestProject.Section31.EIGSAnchoredWindowDisplacementTail

/-! The actual finite graph IFT trajectory and independent exponential
holding times on one explicit product probability space. Coordinate-function
laws and samplewise cadlag regularity are proved here. A law on the genuine
J1 Borel carrier and Poisson counting-law identification are separate duties;
this file does not substitute the uniform Borel carrier for that duty. -/

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory Filter Set Topology
open IGS.Sec31.DiscreteMarkov
open scoped NNReal
noncomputable section
set_option maxHeartbeats 4000000

theorem holdingTimePathNNReal_isCadlag
    {State : Type*} [MetricSpace State] (trajectory : ℕ → State)
    (holdingTimes : ℕ → ℝ) (positive : ∀ index, 0 < holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop) :
    IsCadlagPath (fun time : ℝ≥0 => holdingTimePath trajectory holdingTimes (time : ℝ)) := by
  constructor
  · intro time
    obtain ⟨intervalLength, intervalPositive, constant⟩ :=
      holdingTimePath_locally_constant_right trajectory holdingTimes positive nonexplosion time time.property
    have rightReal : ContinuousWithinAt (holdingTimePath trajectory holdingTimes) (Ici (time : ℝ)) time := by
      apply tendsto_const_nhds.congr'
      filter_upwards [Ico_mem_nhdsGE (lt_add_of_pos_right (time : ℝ) intervalPositive)] with nextTime bounds
      exact (constant nextTime bounds.1 bounds.2).symm
    exact rightReal.comp continuous_subtype_val.continuousWithinAt (fun _ membership => membership)
  · intro time
    by_cases zero : time = 0
    · subst time
      refine ⟨trajectory 0, ?_⟩
      simp only [Iio_bot, nhdsWithin_empty, tendsto_bot]
    · have timePositive : 0 < (time : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr zero)
      obtain ⟨intervalLength, intervalPositive, leftValue, constant⟩ :=
        holdingTimePath_locally_constant_left trajectory holdingTimes positive nonexplosion time timePositive
      have leftReal : Tendsto (holdingTimePath trajectory holdingTimes)
          (𝓝[Iio (time : ℝ)] (time : ℝ)) (𝓝 leftValue) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [Ioo_mem_nhdsLT (sub_lt_self (time : ℝ) intervalPositive)] with previousTime bounds
        exact (constant previousTime bounds.1 bounds.2).symm
      refine ⟨leftValue, leftReal.comp ?_⟩
      exact continuous_subtype_val.continuousWithinAt.tendsto_nhdsWithin (fun _ membership => membership)

variable {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
variable [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex]

def finiteGraphExponentialSampleLaw (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (initial : ProbabilityMeasure Vertex) :
    Measure ((ℕ → Vertex) × (ℕ → ℝ)) :=
  (pathLaw (finiteGraphTransitionKernel graph degreePositive) (initial : Measure Vertex)).prod exponentialHoldingTimeLaw

instance finiteGraphExponentialSampleLaw_probability (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (initial : ProbabilityMeasure Vertex) :
    IsProbabilityMeasure (finiteGraphExponentialSampleLaw graph degreePositive initial) := by
  unfold finiteGraphExponentialSampleLaw
  infer_instance

theorem finiteGraphExponentialSampleLaw_independent (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (initial : ProbabilityMeasure Vertex) :
    IndepFun (Prod.fst : (ℕ → Vertex) × (ℕ → ℝ) → (ℕ → Vertex)) Prod.snd
      (finiteGraphExponentialSampleLaw graph degreePositive initial) :=
  indepFun_prod (X := id) (Y := id) measurable_id measurable_id

theorem finiteGraphExponentialSampleLaw_discrete_marginal (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (initial : ProbabilityMeasure Vertex) :
    (finiteGraphExponentialSampleLaw graph degreePositive initial).map Prod.fst =
      pathLaw (finiteGraphTransitionKernel graph degreePositive) (initial : Measure Vertex) :=
  measurePreserving_fst.map_eq

theorem finiteGraphExponentialSampleLaw_clock_marginal (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (initial : ProbabilityMeasure Vertex) :
    (finiteGraphExponentialSampleLaw graph degreePositive initial).map Prod.snd = exponentialHoldingTimeLaw :=
  measurePreserving_snd.map_eq

def finiteGraphExponentialEmbeddedPath {State : Type*} (embedding : Vertex → State) (rate : ℝ≥0)
    (sample : (ℕ → Vertex) × (ℕ → ℝ)) (time : ℝ≥0) : State :=
  embedding (holdingTimePath sample.1 sample.2 ((rate : ℝ) * (time : ℝ)))

theorem finiteGraphExponentialEmbeddedPath_measurable
    {State : Type*} [MeasurableSpace State] (embedding : Vertex → State)
    (embeddingMeasurable : Measurable embedding) (rate : ℝ≥0) :
    Measurable (finiteGraphExponentialEmbeddedPath embedding rate) := by
  apply measurable_pi_lambda
  intro time
  exact embeddingMeasurable.comp (holdingTimePath_measurable ((rate : ℝ) * (time : ℝ)))

theorem finiteGraphExponentialEmbeddedPath_ae_cadlag
    {State : Type*} [MetricSpace State] (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (initial : ProbabilityMeasure Vertex)
    (embedding : Vertex → State) (rate : ℝ≥0) (ratePositive : 0 < rate) :
    ∀ᵐ sample ∂finiteGraphExponentialSampleLaw graph degreePositive initial,
      IsCadlagPath (finiteGraphExponentialEmbeddedPath embedding rate sample) := by
  have positive := (quasiMeasurePreserving_snd
    (μ := pathLaw (finiteGraphTransitionKernel graph degreePositive) (initial : Measure Vertex))
    (ν := exponentialHoldingTimeLaw)).ae exponentialHoldingTimeLaw_positive
  have nonexplosion := (quasiMeasurePreserving_snd
    (μ := pathLaw (finiteGraphTransitionKernel graph degreePositive) (initial : Measure Vertex))
    (ν := exponentialHoldingTimeLaw)).ae exponentialHoldingTimeLaw_nonexplosion
  filter_upwards [positive, nonexplosion] with sample clockPositive clockDiverges
  have cadlag := holdingTimePathNNReal_isCadlag (fun index => embedding (sample.1 index))
    sample.2 clockPositive clockDiverges
  exact cadlag.comp_continuous_strictMono (fun time : ℝ≥0 => rate * time)
    (continuous_const.mul continuous_id) (fun _ _ ordered => mul_lt_mul_of_pos_left ordered ratePositive)

def finiteGraphExponentialFunctionLaw {State : Type*} [MeasurableSpace State]
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (initial : ProbabilityMeasure Vertex)
    (embedding : Vertex → State) (rate : ℝ≥0) : Measure (ℝ≥0 → State) :=
  (finiteGraphExponentialSampleLaw graph degreePositive initial).map
    (finiteGraphExponentialEmbeddedPath embedding rate)

theorem finiteGraphExponentialFunctionLaw_probability {State : Type*} [MeasurableSpace State]
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (initial : ProbabilityMeasure Vertex)
    (embedding : Vertex → State) (embeddingMeasurable : Measurable embedding) (rate : ℝ≥0) :
    IsProbabilityMeasure (finiteGraphExponentialFunctionLaw graph degreePositive initial embedding rate) :=
  isProbabilityMeasure_map (finiteGraphExponentialEmbeddedPath_measurable embedding embeddingMeasurable rate).aemeasurable

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.holdingTimePathNNReal_isCadlag
#print axioms IGS.Sec31.PoissonClock.finiteGraphExponentialSampleLaw_independent
#print axioms IGS.Sec31.PoissonClock.finiteGraphExponentialSampleLaw_discrete_marginal
#print axioms IGS.Sec31.PoissonClock.finiteGraphExponentialSampleLaw_clock_marginal
#print axioms IGS.Sec31.PoissonClock.finiteGraphExponentialEmbeddedPath_measurable
#print axioms IGS.Sec31.PoissonClock.finiteGraphExponentialEmbeddedPath_ae_cadlag
#print axioms IGS.Sec31.PoissonClock.finiteGraphExponentialFunctionLaw_probability
