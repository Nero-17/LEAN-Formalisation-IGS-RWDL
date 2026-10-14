import RequestProject.Section31.IndependentExponentialHoldingTimes
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace IGS.Sec31.PoissonClock
noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators Topology

def cumulativeHoldingTime (holdingTimes : ℕ → ℝ) (count : ℕ) : ℝ :=
  ∑ index ∈ Finset.range count, holdingTimes index

theorem cumulativeHoldingTime_measurable (count : ℕ) :
    Measurable (fun holdingTimes => cumulativeHoldingTime holdingTimes count) := by
  unfold cumulativeHoldingTime
  fun_prop

theorem cumulativeHoldingTime_monotone (holdingTimes : ℕ → ℝ)
    (nonnegative : ∀ index, 0 ≤ holdingTimes index) : Monotone (cumulativeHoldingTime holdingTimes) := by
  intro first last bound
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono bound)
    (fun index _ _ => nonnegative index)

/-- The index of the state occupied at a real time. The default value on
explosive holding-time samples is used only to make this a total measurable map. -/
def holdingJumpIndex (holdingTimes : ℕ → ℝ) (time : ℝ) : ℕ := by
  classical
  exact if reached : ∃ count, time < cumulativeHoldingTime holdingTimes (count + 1)
    then Nat.find reached else 0

theorem holdingJumpIndex_measurable (time : ℝ) : Measurable (fun holdingTimes => holdingJumpIndex holdingTimes time) := by
  classical
  let reached : Set (ℕ → ℝ) := {holdingTimes | ∃ count, time < cumulativeHoldingTime holdingTimes (count + 1)}
  have reachedMeasurable : MeasurableSet reached := by
    change MeasurableSet {holdingTimes | ∃ count, time < cumulativeHoldingTime holdingTimes (count + 1)}
    simp only [Set.setOf_exists]
    exact MeasurableSet.iUnion fun count => measurableSet_lt measurable_const (cumulativeHoldingTime_measurable (count + 1))
  have firstReached : Measurable (fun holdingTimes : reached => Nat.find holdingTimes.property) := by
    apply measurable_find (fun holdingTimes : reached => holdingTimes.property)
    intro count
    exact (measurableSet_lt measurable_const (cumulativeHoldingTime_measurable (count + 1))).preimage measurable_subtype_coe
  exact firstReached.dite measurable_const reachedMeasurable

theorem holdingJumpIndex_eq_of_interval (holdingTimes : ℕ → ℝ)
    (nonnegative : ∀ index, 0 ≤ holdingTimes index) (time : ℝ) (count : ℕ)
    (lower : cumulativeHoldingTime holdingTimes count ≤ time)
    (upper : time < cumulativeHoldingTime holdingTimes (count + 1)) :
    holdingJumpIndex holdingTimes time = count := by
  have reached : ∃ index, time < cumulativeHoldingTime holdingTimes (index + 1) := ⟨count, upper⟩
  rw [holdingJumpIndex, dif_pos reached, Nat.find_eq_iff]
  refine ⟨upper, fun index indexSmall => ?_⟩
  exact not_lt_of_ge ((cumulativeHoldingTime_monotone holdingTimes nonnegative (Nat.succ_le_of_lt indexSmall)).trans lower)

theorem holdingJumpIndex_interval (holdingTimes : ℕ → ℝ)
    (nonnegative : ∀ index, 0 ≤ holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
    (time : ℝ) (timeNonnegative : 0 ≤ time) :
    cumulativeHoldingTime holdingTimes (holdingJumpIndex holdingTimes time) ≤ time ∧
      time < cumulativeHoldingTime holdingTimes (holdingJumpIndex holdingTimes time + 1) := by
  obtain ⟨count, countLarge⟩ := (nonexplosion.eventually_gt_atTop time).exists
  have reached : ∃ index, time < cumulativeHoldingTime holdingTimes (index + 1) :=
    ⟨count, countLarge.trans_le (cumulativeHoldingTime_monotone holdingTimes nonnegative (Nat.le_succ count))⟩
  rw [holdingJumpIndex, dif_pos reached]
  refine ⟨?_, Nat.find_spec reached⟩
  generalize indexEquality : Nat.find reached = index
  cases index with
  | zero => simpa [cumulativeHoldingTime] using timeNonnegative
  | succ previous =>
    exact le_of_not_gt (Nat.find_min reached (by rw [indexEquality]; exact Nat.lt_succ_self previous))

def holdingTimePath {Vertex : Type*} (trajectory : ℕ → Vertex) (holdingTimes : ℕ → ℝ) (time : ℝ) : Vertex :=
  trajectory (holdingJumpIndex holdingTimes time)

theorem holdingTimePath_measurable {Vertex : Type*} [MeasurableSpace Vertex] (time : ℝ) :
    Measurable (fun sample : (ℕ → Vertex) × (ℕ → ℝ) => holdingTimePath sample.1 sample.2 time) := by
  have evaluation : Measurable (fun sample : (ℕ → Vertex) × ℕ => sample.1 sample.2) :=
    measurable_from_prod_countable_left fun index => measurable_pi_apply index
  exact evaluation.comp (measurable_fst.prodMk ((holdingJumpIndex_measurable time).comp measurable_snd))

theorem holdingTimePath_initial {Vertex : Type*} (trajectory : ℕ → Vertex) (holdingTimes : ℕ → ℝ)
    (positive : ∀ index, 0 < holdingTimes index) : holdingTimePath trajectory holdingTimes 0 = trajectory 0 := by
  unfold holdingTimePath
  rw [holdingJumpIndex_eq_of_interval holdingTimes (fun index => (positive index).le) 0 0]
  · simp [cumulativeHoldingTime]
  · simpa [cumulativeHoldingTime] using positive 0

/-- Each nonexplosive sample is constant on a nonempty right interval at
every nonnegative time, including its jump times. -/
theorem holdingTimePath_locally_constant_right {Vertex : Type*} (trajectory : ℕ → Vertex)
    (holdingTimes : ℕ → ℝ) (positive : ∀ index, 0 < holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
    (time : ℝ) (timeNonnegative : 0 ≤ time) :
    ∃ intervalLength : ℝ, 0 < intervalLength ∧ ∀ nextTime : ℝ,
      time ≤ nextTime → nextTime < time + intervalLength →
        holdingTimePath trajectory holdingTimes nextTime = holdingTimePath trajectory holdingTimes time := by
  have interval := holdingJumpIndex_interval holdingTimes (fun index => (positive index).le)
    nonexplosion time timeNonnegative
  refine ⟨cumulativeHoldingTime holdingTimes (holdingJumpIndex holdingTimes time + 1) - time,
    sub_pos.mpr interval.2, fun nextTime lower upper => ?_⟩
  unfold holdingTimePath
  congr 1
  apply holdingJumpIndex_eq_of_interval holdingTimes (fun index => (positive index).le)
  · exact interval.1.trans lower
  · linarith

/-- At every strictly positive time a nonexplosive sample is also constant
on a nonempty left interval. Its value may differ from the value at a jump. -/
theorem holdingTimePath_locally_constant_left {Vertex : Type*} (trajectory : ℕ → Vertex)
    (holdingTimes : ℕ → ℝ) (positive : ∀ index, 0 < holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
    (time : ℝ) (timePositive : 0 < time) :
    ∃ intervalLength : ℝ, 0 < intervalLength ∧ ∃ leftValue : Vertex, ∀ previousTime : ℝ,
      time - intervalLength < previousTime → previousTime < time →
        holdingTimePath trajectory holdingTimes previousTime = leftValue := by
  obtain ⟨count, countLarge⟩ := (nonexplosion.eventually_gt_atTop time).exists
  have reached : ∃ index, time ≤ cumulativeHoldingTime holdingTimes (index + 1) :=
    ⟨count, countLarge.le.trans (cumulativeHoldingTime_monotone holdingTimes
      (fun index => (positive index).le) (Nat.le_succ count))⟩
  have lower : cumulativeHoldingTime holdingTimes (Nat.find reached) < time := by
    generalize indexEquality : Nat.find reached = index
    cases index with
    | zero => simpa [cumulativeHoldingTime] using timePositive
    | succ previous =>
      exact lt_of_not_ge (Nat.find_min reached (by rw [indexEquality]; exact Nat.lt_succ_self previous))
  refine ⟨time - cumulativeHoldingTime holdingTimes (Nat.find reached), sub_pos.mpr lower,
    trajectory (Nat.find reached), fun previousTime lowerTime upperTime => ?_⟩
  unfold holdingTimePath
  congr 1
  apply holdingJumpIndex_eq_of_interval holdingTimes (fun index => (positive index).le)
  · linarith
  · exact upperTime.trans_le (Nat.find_spec reached)

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.holdingJumpIndex_measurable
#print axioms IGS.Sec31.PoissonClock.holdingTimePath_measurable
#print axioms IGS.Sec31.PoissonClock.holdingTimePath_locally_constant_right
#print axioms IGS.Sec31.PoissonClock.holdingTimePath_locally_constant_left

