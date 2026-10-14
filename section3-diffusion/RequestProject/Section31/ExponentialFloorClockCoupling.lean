import RequestProject.Section31.FiniteGraphExponentialClockCoupling
import RequestProject.Section31.ExponentialClockGridInterpolation
import RequestProject.Section31.EIGSFullHorizonModulusBound

namespace IGS.Sec31.PoissonClock
noncomputable section
open MeasureTheory Filter Set
open IGS.Sec31.DiscreteMarkov

def floorClockBadModulus {Vertex State : Type*} [MetricSpace State]
    (embedding : Vertex → State) (rate horizon window tolerance : ℝ) : Set (ℕ → Vertex) :=
  {path | ∃ first ∈ Icc (0 : ℝ) horizon, ∃ second ∈ Icc (0 : ℝ) horizon,
    |second - first| ≤ window ∧ tolerance <
      dist (embedding (path ⌊first * rate⌋₊)) (embedding (path ⌊second * rate⌋₊))}

theorem floorClockBadModulus_measurable {Vertex State : Type} [Fintype Vertex]
    [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [MetricSpace State]
    (embedding : Vertex → State) (rate horizon window tolerance : ℝ) (rateNonnegative : 0 ≤ rate) :
    MeasurableSet (floorClockBadModulus embedding rate horizon window tolerance) := by
  have result := finite_floor_clock_modulus_event_measurable embedding rate horizon window
    (tolerance / 2) rateNonnegative
  convert result using 1 <;> simp only [floorClockBadModulus, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]

theorem floorChain_good_clock_coupling
    {Vertex State : Type*} [MetricSpace State] (embedding : Vertex → State)
    (trajectory : ℕ → Vertex) (holdingTimes : ℕ → ℝ)
    (acceleration : ℝ) (accelerationPositive : 0 < acceleration)
    (horizon : ℕ) (duration error tolerance : ℝ)
    (errorSmall : error ≤ duration) (errorAtMostOne : error ≤ 1)
    (good : trajectory ∉ floorClockBadModulus embedding acceleration (horizon + 1 : ℕ) duration tolerance)
    (clockError : ∀ time : ℝ, 0 ≤ time → time ≤ horizon →
      |(holdingJumpIndex holdingTimes (acceleration * time) : ℝ) / acceleration - time| ≤ error)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (timeBound : time ≤ horizon) :
    dist (embedding (holdingTimePath trajectory holdingTimes (acceleration * time)))
      (embedding (trajectory ⌊acceleration * time⌋₊)) ≤ tolerance := by
  let inverseTime : ℝ := (holdingJumpIndex holdingTimes (acceleration * time) : ℝ) / acceleration
  have inverseNonnegative : 0 ≤ inverseTime := div_nonneg (Nat.cast_nonneg _) accelerationPositive.le
  have close : |inverseTime - time| ≤ error := clockError time timeNonnegative timeBound
  have inverseBound : inverseTime ≤ (horizon + 1 : ℕ) := by
    rw [Nat.cast_add, Nat.cast_one]
    have upper := (abs_le.mp close).2
    linarith
  have timeBound' : time ≤ (horizon + 1 : ℕ) := by
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have identity : trajectory ⌊inverseTime * acceleration⌋₊ =
      holdingTimePath trajectory holdingTimes (acceleration * time) := by
    dsimp only [inverseTime]
    rw [div_mul_cancel₀ _ accelerationPositive.ne', Nat.floor_natCast]
    rfl
  by_contra failure
  apply good
  refine ⟨inverseTime, ⟨inverseNonnegative, inverseBound⟩, time,
    ⟨timeNonnegative, timeBound'⟩, ?_, ?_⟩
  · simpa only [abs_sub_comm] using close.trans errorSmall
  · rw [identity, mul_comm time acceleration]
    exact lt_of_not_ge failure

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.floorClockBadModulus_measurable
#print axioms IGS.Sec31.PoissonClock.floorChain_good_clock_coupling
