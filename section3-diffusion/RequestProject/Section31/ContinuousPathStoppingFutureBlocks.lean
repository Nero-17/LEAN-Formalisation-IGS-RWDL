import RequestProject.Section31.ContinuousPathStoppingFutureBlockStep
import RequestProject.Section31.ContinuousKernelBackwardObservations

/-! Finite future observation blocks at every finite stopping time. An
observation records its test at the current time and the nonnegative gap to
the next observation. A leading constant-one observation permits the first
nonconstant test to occur at any nonnegative delay. The backward recursion
is the existing continuous-semigroup recursion used by the global family's
finite-dimensional laws; it is not a new choice of process law. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal
noncomputable section

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable [ambient : MeasurableSpace C(ℝ≥0, State)] [OpensMeasurableSpace C(ℝ≥0, State)]

def continuousPathFutureObservationProduct :
    List (ℝ≥0 × C(State, ℝ)) → C(State, ℝ) → C(ℝ≥0, State) → ℝ≥0 → ℝ
  | [], terminal, path, time => terminal (path time)
  | observation :: remaining, terminal, path, time => observation.2 (path time) *
      continuousPathFutureObservationProduct remaining terminal path (time + observation.1)

theorem continuousPath_finite_stoppingTime_futureBlock_setIntegral_markov
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
    (observations : List (ℝ≥0 × C(State, ℝ))) (terminal : C(State, ℝ)) :
    ∀ (stoppingTime : C(ℝ≥0, State) → ℝ≥0)
      (stopping : IsStoppingTime filtration (fun path => (stoppingTime path : WithTop ℝ≥0)))
      (prior : C(ℝ≥0, State) → ℝ) (priorMeasurable : Measurable[stopping.measurableSpace] prior)
      (priorBound : ℝ) (priorBoundNonnegative : 0 ≤ priorBound)
      (priorBounded : ∀ path, ‖prior path‖ ≤ priorBound)
      (event : Set C(ℝ≥0, State)) (eventMeasurable : MeasurableSet[stopping.measurableSpace] event),
      (∫ path in event, prior path *
        continuousPathFutureObservationProduct observations terminal path (stoppingTime path) ∂measure) =
        ∫ path in event, prior path *
          (BanachBackwardObservations.backwardProduct semigroup
            (fun function => ContinuousLinearMap.mul ℝ C(State, ℝ) function)
            observations terminal) (path (stoppingTime path)) ∂measure := by
  induction observations with
  | nil =>
      intro stoppingTime stopping prior priorMeasurable priorBound priorBoundNonnegative priorBounded event eventMeasurable
      rfl
  | cons observation remaining induction =>
      intro stoppingTime stopping prior priorMeasurable priorBound priorBoundNonnegative priorBounded event eventMeasurable
      let shiftedStopping := StoppingApproximation.isStoppingTime_finite_add_nnreal_delay
        filtration stoppingTime stopping observation.1
      have stoppingSigmaInclusion : stopping.measurableSpace ≤ shiftedStopping.measurableSpace :=
        continuousPath_finite_stoppingTime_delayed_measurableSpace_mono
          filtration stoppingTime stopping observation.1
      have stoppedStateMeasurable := continuousPath_finite_stoppingTime_state_measurable
        filtration naturalBelow stoppingTime stopping
      have priorNextMeasurable : Measurable[stopping.measurableSpace]
          (fun path : C(ℝ≥0, State) => prior path * observation.2 (path (stoppingTime path))) :=
        priorMeasurable.mul (observation.2.continuous.measurable.comp stoppedStateMeasurable)
      have priorNextBounded (path : C(ℝ≥0, State)) :
          ‖prior path * observation.2 (path (stoppingTime path))‖ ≤ priorBound * ‖observation.2‖ := by
        rw [norm_mul]
        exact mul_le_mul (priorBounded path) (observation.2.norm_coe_le_norm _)
          (norm_nonneg _) priorBoundNonnegative
      let remainingBackward : C(State, ℝ) :=
        BanachBackwardObservations.backwardProduct semigroup
          (fun function => ContinuousLinearMap.mul ℝ C(State, ℝ) function) remaining terminal
      have remainingIdentity := induction (fun path => stoppingTime path + observation.1) shiftedStopping
        (fun path => prior path * observation.2 (path (stoppingTime path)))
        (priorNextMeasurable.mono stoppingSigmaInclusion le_rfl)
        (priorBound * ‖observation.2‖) (mul_nonneg priorBoundNonnegative (norm_nonneg _)) priorNextBounded
        event (stoppingSigmaInclusion event eventMeasurable)
      have oneStepIdentity := continuousPath_finite_stoppingTime_weighted_boundedBorel_setIntegral_markov
        measure filtration naturalBelow semigroup deterministicMarkov kernel kernelMarkov kernelContinuous
        stoppingTime stopping (fun path => prior path * observation.2 (path (stoppingTime path)))
        priorNextMeasurable (priorBound * ‖observation.2‖)
        (mul_nonneg priorBoundNonnegative (norm_nonneg _)) priorNextBounded
        observation.1 remainingBackward remainingBackward.continuous.measurable
        ‖remainingBackward‖ (norm_nonneg _) (fun point => remainingBackward.norm_coe_le_norm point)
        event eventMeasurable
      calc
        _ = ∫ path in event, (prior path * observation.2 (path (stoppingTime path))) *
            continuousPathFutureObservationProduct remaining terminal path
              (stoppingTime path + observation.1) ∂measure := by
          apply integral_congr_ae
          exact Eventually.of_forall fun path => by
            simp only [continuousPathFutureObservationProduct]
            exact (mul_assoc _ _ _).symm
        _ = ∫ path in event, (prior path * observation.2 (path (stoppingTime path))) *
            remainingBackward (path (stoppingTime path + observation.1)) ∂measure := remainingIdentity
        _ = ∫ path in event, (prior path * observation.2 (path (stoppingTime path))) *
            (∫ location, remainingBackward location ∂kernel observation.1 (path (stoppingTime path))) ∂measure :=
          oneStepIdentity
        _ = _ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun path => by
            dsimp only
            rw [kernelContinuous]
            change (prior path * observation.2 (path (stoppingTime path))) *
                semigroup observation.1 remainingBackward (path (stoppingTime path)) =
              prior path * (observation.2 (path (stoppingTime path)) *
                semigroup observation.1 remainingBackward (path (stoppingTime path)))
            exact mul_assoc _ _ _

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_finite_stoppingTime_futureBlock_setIntegral_markov
