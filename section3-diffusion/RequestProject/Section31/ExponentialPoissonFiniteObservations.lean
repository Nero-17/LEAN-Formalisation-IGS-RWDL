import RequestProject.Section31.ExponentialPoissonProcessCertificate

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
set_option maxHeartbeats 2200000

def extendObservationTimes {count : ℕ} (times : Fin (count + 1) → ℝ≥0)
    (index : ℕ) : ℝ≥0 :=
  times ⟨min index count, Nat.lt_succ_of_le (Nat.min_le_right index count)⟩

theorem extendObservationTimes_monotone {count : ℕ}
    (times : Fin (count + 1) → ℝ≥0) (ordered : Monotone times) :
    Monotone (extendObservationTimes times) := by
  intro first last before
  apply ordered
  change min first count ≤ min last count
  exact min_le_min before le_rfl

theorem extendObservationTimes_eq {count : ℕ} (times : Fin (count + 1) → ℝ≥0)
    (index : Fin (count + 1)) : extendObservationTimes times index.val = times index := by
  unfold extendObservationTimes
  congr 1
  apply Fin.ext
  exact Nat.min_eq_left (Nat.le_of_lt_succ index.isLt)

theorem exponential_poisson_finite_increment_joint_law {count : ℕ}
    (times : Fin (count + 1) → ℝ≥0) (ordered : Monotone times) :
    exponentialHoldingTimeLaw.map (fun holdingTimes => fun index : Fin count =>
      holdingJumpIndex holdingTimes (times index.succ : ℝ) -
        holdingJumpIndex holdingTimes (times index.castSucc : ℝ)) =
      Measure.pi (fun index : Fin count => poissonMeasure
        (times index.succ - times index.castSucc)) := by
  have joint := exponential_poisson_increment_vector_law (extendObservationTimes times)
    (extendObservationTimes_monotone times ordered) count
  have leftTime : ∀ index : Fin count,
      extendObservationTimes times index.val = times index.castSucc := by
    intro index
    exact extendObservationTimes_eq times index.castSucc
  have rightTime : ∀ index : Fin count,
      extendObservationTimes times (index.val + 1) = times index.succ := by
    intro index
    exact extendObservationTimes_eq times index.succ
  simpa only [holdingCountIncrement, leftTime, rightTime] using joint

theorem holdingCountIncrement_prefix_sum (times : ℕ → ℝ≥0) (ordered : Monotone times)
    (initial : times 0 = 0) :
    ∀ᵐ holdingTimes ∂exponentialHoldingTimeLaw, ∀ count,
      (∑ index ∈ Finset.range count, holdingCountIncrement times index holdingTimes) =
        holdingJumpIndex holdingTimes (times count : ℝ) := by
  filter_upwards [exponentialHoldingJumpIndex_initial, exponentialHoldingJumpIndex_regular]
    with holdingTimes zero regular
  intro count
  have monotoneCounts : Monotone (fun index => holdingJumpIndex holdingTimes (times index : ℝ)) :=
    regular.1.comp ordered
  have telescope := Finset.sum_range_tsub monotoneCounts count
  simpa only [holdingCountIncrement, initial, NNReal.coe_zero, zero, Nat.sub_zero] using telescope

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.extendObservationTimes_monotone
#print axioms IGS.Sec31.PoissonClock.extendObservationTimes_eq
#print axioms IGS.Sec31.PoissonClock.exponential_poisson_finite_increment_joint_law
#print axioms IGS.Sec31.PoissonClock.holdingCountIncrement_prefix_sum
