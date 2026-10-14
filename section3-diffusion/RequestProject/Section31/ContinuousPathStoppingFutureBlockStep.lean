import RequestProject.Section31.ContinuousPathBoundedBorelStoppingMarkov
import RequestProject.Section31.NNRealStoppingTimeShift
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! One backward step for a future observation block at a finite stopping
time. The one-time stopping conditional expectation is derived from the
deterministic continuous-test Markov identity and its representing kernel.
The preceding bounded factor is measurable at the stopping time; it may be
the product of all earlier observations in a block. No future-block Markov
identity is an input.

The separate delayed-stopping sigma-field inclusion is the filtration step
needed to iterate this identity at tau+s. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal
noncomputable section

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable [ambient : MeasurableSpace C(ℝ≥0, State)] [OpensMeasurableSpace C(ℝ≥0, State)]

theorem continuousPath_finite_stoppingTime_delayed_measurableSpace_mono
    (filtration : Filtration ℝ≥0 ambient)
    (stoppingTime : C(ℝ≥0, State) → ℝ≥0)
    (stopping : IsStoppingTime filtration (fun path => (stoppingTime path : WithTop ℝ≥0)))
    (delay : ℝ≥0) :
    stopping.measurableSpace ≤
      (StoppingApproximation.isStoppingTime_finite_add_nnreal_delay
        filtration stoppingTime stopping delay).measurableSpace := by
  apply stopping.measurableSpace_mono
  intro path
  change (stoppingTime path : WithTop ℝ≥0) ≤ ((stoppingTime path + delay : ℝ≥0) : WithTop ℝ≥0)
  exact_mod_cast (le_add_of_nonneg_right (zero_le delay) : stoppingTime path ≤ stoppingTime path + delay)

theorem continuousPath_finite_stoppingTime_state_measurable
    (filtration : Filtration ℝ≥0 ambient)
    (naturalBelow : ∀ time, canonicalContinuousPathFiltration (State := State) time ≤ filtration time)
    (stoppingTime : C(ℝ≥0, State) → ℝ≥0)
    (stopping : IsStoppingTime filtration (fun path => (stoppingTime path : WithTop ℝ≥0))) :
    Measurable[stopping.measurableSpace] (fun path : C(ℝ≥0, State) => path (stoppingTime path)) := by
  have adapted : StronglyAdapted filtration canonicalContinuousPathProcess :=
    fun time => (canonicalContinuousPathProcess_stronglyAdapted time).mono (naturalBelow time)
  have progressive : ProgMeasurable filtration canonicalContinuousPathProcess :=
    adapted.progMeasurable_of_continuous canonicalContinuousPathProcess_continuous
  simpa [stoppedValue, canonicalContinuousPathProcess] using measurable_stoppedValue progressive stopping

theorem continuousPath_finite_stoppingTime_weighted_boundedBorel_setIntegral_markov
    (measure : Measure C(ℝ≥0, State)) [IsFiniteMeasure measure]
    (filtration : Filtration ℝ≥0 ambient)
    (naturalBelow : ∀ time, canonicalContinuousPathFiltration (State := State) time ≤ filtration time)
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (deterministicMarkov : ∀ (time delay : ℝ≥0) (terminal : C(State, ℝ)) (event : Set C(ℝ≥0, State)),
      MeasurableSet[filtration time] event →
      (∫ path in event, terminal (path (time + delay)) ∂measure) =
        ∫ path in event, semigroup delay terminal (path time) ∂measure)
    (kernel : ℝ≥0 → Kernel State State) (kernelMarkov : ∀ delay, IsMarkovKernel (kernel delay))
    (kernelContinuous : ∀ delay point (function : C(State, ℝ)),
      (∫ location, function location ∂kernel delay point) = semigroup delay function point)
    (stoppingTime : C(ℝ≥0, State) → ℝ≥0)
    (stopping : IsStoppingTime filtration (fun path => (stoppingTime path : WithTop ℝ≥0)))
    (prior : C(ℝ≥0, State) → ℝ) (priorMeasurable : Measurable[stopping.measurableSpace] prior)
    (priorBound : ℝ) (priorBoundNonnegative : 0 ≤ priorBound)
    (priorBounded : ∀ path, ‖prior path‖ ≤ priorBound)
    (delay : ℝ≥0) (terminal : State → ℝ) (terminalMeasurable : Measurable terminal)
    (terminalBound : ℝ) (terminalBoundNonnegative : 0 ≤ terminalBound)
    (terminalBounded : ∀ point, ‖terminal point‖ ≤ terminalBound)
    (event : Set C(ℝ≥0, State)) (eventMeasurable : MeasurableSet[stopping.measurableSpace] event) :
    (∫ path in event, prior path * terminal (path (stoppingTime path + delay)) ∂measure) =
      ∫ path in event, prior path *
        (∫ location, terminal location ∂kernel delay (path (stoppingTime path))) ∂measure := by
  have stoppingTimeMeasurable : Measurable stoppingTime := by
    simpa using stopping.measurable'.untopA
  have futureStateMeasurable : Measurable (fun path : C(ℝ≥0, State) => path (stoppingTime path + delay)) :=
    continuous_eval.measurable.comp (measurable_id.prodMk (stoppingTimeMeasurable.add_const delay))
  have terminalPathMeasurable : Measurable (fun path : C(ℝ≥0, State) =>
      terminal (path (stoppingTime path + delay))) := terminalMeasurable.comp futureStateMeasurable
  have futureIntegrable : Integrable (fun path : C(ℝ≥0, State) =>
      terminal (path (stoppingTime path + delay))) measure :=
    Integrable.of_bound terminalPathMeasurable.aestronglyMeasurable terminalBound
      (Eventually.of_forall fun path => terminalBounded _)
  have productIntegrable : Integrable (fun path : C(ℝ≥0, State) =>
      prior path * terminal (path (stoppingTime path + delay))) measure := by
    apply Integrable.of_bound
      ((priorMeasurable.mono stopping.measurableSpace_le le_rfl).mul terminalPathMeasurable).aestronglyMeasurable
      (priorBound * terminalBound)
    exact Eventually.of_forall fun path => by
      rw [norm_mul]
      exact mul_le_mul (priorBounded path) (terminalBounded _) (norm_nonneg _) priorBoundNonnegative
  have oneTimeIdentity := continuousPath_finite_stoppingTime_boundedBorel_condExp_markov
    measure filtration naturalBelow semigroup deterministicMarkov kernel kernelMarkov kernelContinuous
    stoppingTime stopping delay terminal terminalMeasurable terminalBound terminalBounded
  have pullOutIdentity := condExp_stronglyMeasurable_mul_of_bound stopping.measurableSpace_le
    priorMeasurable.stronglyMeasurable futureIntegrable priorBound (Eventually.of_forall priorBounded)
  have weightedIdentity :
      condExp stopping.measurableSpace measure
        (fun path => prior path * terminal (path (stoppingTime path + delay))) =ᵐ[measure]
      (fun path => prior path * (∫ location, terminal location ∂kernel delay (path (stoppingTime path)))) :=
    pullOutIdentity.trans (oneTimeIdentity.mono fun path equality => congrArg (fun value => prior path * value) equality)
  calc
    _ = ∫ path in event, condExp stopping.measurableSpace measure
        (fun path => prior path * terminal (path (stoppingTime path + delay))) path ∂measure :=
      (setIntegral_condExp stopping.measurableSpace_le productIntegrable eventMeasurable).symm
    _ = _ := integral_congr_ae (ae_restrict_of_ae weightedIdentity)

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_finite_stoppingTime_delayed_measurableSpace_mono
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_finite_stoppingTime_state_measurable
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_finite_stoppingTime_weighted_boundedBorel_setIntegral_markov
