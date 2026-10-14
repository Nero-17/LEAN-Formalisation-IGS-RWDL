import RequestProject.Section31.ExponentialPoissonPastIndependence
import RequestProject.Section31.SequentialIncrementIndependence

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
set_option maxHeartbeats 2500000

def holdingCountIncrement (times : ℕ → ℝ≥0) (index : ℕ) (holdingTimes : ℕ → ℝ) : ℕ :=
  holdingJumpIndex holdingTimes (times (index + 1) : ℝ) -
    holdingJumpIndex holdingTimes (times index : ℝ)

theorem holdingCountIncrement_measurable (times : ℕ → ℝ≥0) (index : ℕ) :
    Measurable (holdingCountIncrement times index) := by
  exact (holdingJumpIndex_measurable (times (index + 1) : ℝ)).sub
    (holdingJumpIndex_measurable (times index : ℝ))

theorem exponential_poisson_increments_sequential_independent
    (times : ℕ → ℝ≥0) (ordered : Monotone times) (count : ℕ) :
    IndepFun (fun holdingTimes => fun index : Fin count =>
        holdingCountIncrement times index.val holdingTimes)
      (holdingCountIncrement times count) exponentialHoldingTimeLaw := by
  have pastBefore : ∀ index : Fin (count + 1), times index.val ≤ times count := by
    intro index
    exact ordered (by omega)
  have independent := exponential_poisson_future_increment_independent
    (times count) (times (count + 1) - times count)
    (fun index : Fin (count + 1) => times index.val) pastBefore
  have pastMapMeasurable : Measurable (fun values : Fin (count + 1) → ℕ =>
      fun index : Fin count => values index.succ - values index.castSucc) := by
    apply measurable_pi_lambda
    intro index
    exact (measurable_pi_apply index.succ).sub (measurable_pi_apply index.castSucc)
  have endpoint : times count + (times (count + 1) - times count) = times (count + 1) :=
    add_tsub_cancel_of_le (ordered (Nat.le_succ count))
  simpa only [Function.comp_def, holdingCountIncrement, Fin.val_succ, Fin.val_castSucc,
    endpoint] using independent.comp pastMapMeasurable measurable_id

theorem exponential_poisson_increments_iIndepFun
    (times : ℕ → ℝ≥0) (ordered : Monotone times) :
    iIndepFun (holdingCountIncrement times) exponentialHoldingTimeLaw := by
  exact iIndepFun_of_sequential_prefix_independence exponentialHoldingTimeLaw
    (holdingCountIncrement times) (exponential_poisson_increments_sequential_independent times ordered)

theorem exponential_poisson_ordered_increment_hasLaw
    (times : ℕ → ℝ≥0) (ordered : Monotone times) (index : ℕ) :
    HasLaw (holdingCountIncrement times index)
      (poissonMeasure (times (index + 1) - times index)) exponentialHoldingTimeLaw := by
  have endpoint : times index + (times (index + 1) - times index) = times (index + 1) :=
    add_tsub_cancel_of_le (ordered (Nat.le_succ index))
  simpa only [holdingCountIncrement, endpoint] using
    exponential_poisson_increment_hasLaw (times index) (times (index + 1) - times index)

theorem exponential_poisson_increment_vector_law
    (times : ℕ → ℝ≥0) (ordered : Monotone times) (count : ℕ) :
    exponentialHoldingTimeLaw.map
      (fun holdingTimes => fun index : Fin count => holdingCountIncrement times index.val holdingTimes) =
      Measure.pi (fun index : Fin count =>
        poissonMeasure (times (index.val + 1) - times index.val)) := by
  have independent := (exponential_poisson_increments_iIndepFun times ordered).precomp
    (g := fun index : Fin count => index.val) Fin.val_injective
  have joint := (iIndepFun_iff_map_fun_eq_pi_map
    (fun index : Fin count => (holdingCountIncrement_measurable times index.val).aemeasurable)).mp
      independent
  calc
    _ = Measure.pi (fun index : Fin count => exponentialHoldingTimeLaw.map
        (holdingCountIncrement times index.val)) := joint
    _ = _ := by
      congr 1
      funext index
      exact (exponential_poisson_ordered_increment_hasLaw times ordered index.val).map_eq

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.exponential_poisson_increments_sequential_independent
#print axioms IGS.Sec31.PoissonClock.exponential_poisson_increments_iIndepFun
#print axioms IGS.Sec31.PoissonClock.exponential_poisson_ordered_increment_hasLaw
#print axioms IGS.Sec31.PoissonClock.exponential_poisson_increment_vector_law
