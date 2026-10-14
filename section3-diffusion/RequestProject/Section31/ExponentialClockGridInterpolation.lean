import RequestProject.Section31.ExponentialClockFiniteGrid

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace IGS.Sec31.PoissonClock
noncomputable section
open Filter Set
open scoped _root_.Topology

/-- Monotonicity of the genuine jump count turns a finite Borel clock
grid event into an error bound at every real time in the interval. -/
theorem holdingJumpClock_uniform_of_finite_grid
    (holdingTimes : ℕ → ℝ) (positive : ∀ index, 0 < holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
    (acceleration : ℝ) (accelerationPositive : 0 < acceleration)
    (horizon grid : ℕ) (tolerance : ℝ)
    (good : holdingTimes ∉ clockFiniteGridBad acceleration horizon grid tolerance)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (timeBound : time ≤ horizon) :
    |(holdingJumpIndex holdingTimes (acceleration * time) : ℝ) / acceleration - time| ≤
      tolerance + 1 / (grid + 1 : ℝ) := by
  let lower : ℕ := ⌊(grid + 1 : ℝ) * time⌋₊
  let upper : ℕ := lower + 1
  let lowerTime := clockFiniteGridTime grid lower
  let upperTime := clockFiniteGridTime grid upper
  have denominatorPositive : (0 : ℝ) < grid + 1 := by positivity
  have lowerIndex : lower ≤ horizon * (grid + 1) := by
    have realBound : (lower : ℝ) ≤ (horizon * (grid + 1) : ℕ) := by
      calc
        _ ≤ (grid + 1 : ℝ) * time := Nat.floor_le (mul_nonneg denominatorPositive.le timeNonnegative)
        _ ≤ (grid + 1 : ℝ) * horizon := mul_le_mul_of_nonneg_left timeBound denominatorPositive.le
        _ = _ := by simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]; ring
    exact_mod_cast realBound
  have upperIndex : upper ≤ (horizon + 1) * (grid + 1) := by
    calc
      _ ≤ horizon * (grid + 1) + 1 := Nat.add_le_add_right lowerIndex 1
      _ ≤ horizon * (grid + 1) + (grid + 1) := Nat.add_le_add_left (by omega) _
      _ = _ := by ring
  let lowerFin : Fin ((horizon + 1) * (grid + 1) + 1) := ⟨lower, lt_of_le_of_lt (by omega) (Nat.lt_succ_self _)⟩
  let upperFin : Fin ((horizon + 1) * (grid + 1) + 1) := ⟨upper, Nat.lt_succ_of_le upperIndex⟩
  have lowerNonnegative : 0 ≤ lowerTime := div_nonneg (Nat.cast_nonneg _) denominatorPositive.le
  have lowerBefore : lowerTime ≤ time := by
    apply (div_le_iff₀ denominatorPositive).mpr
    simpa only [lower, mul_comm] using (Nat.floor_le (mul_nonneg denominatorPositive.le timeNonnegative) : (lower : ℝ) ≤ (grid + 1 : ℝ) * time)
  have upperAfter : time < upperTime := by
    apply (lt_div_iff₀ denominatorPositive).mpr
    simpa only [upper, lower, Nat.cast_add, Nat.cast_one, mul_comm] using Nat.lt_floor_add_one ((grid + 1 : ℝ) * time)
  have gap : upperTime - lowerTime = 1 / (grid + 1 : ℝ) := by
    dsimp only [upperTime, lowerTime, clockFiniteGridTime, upper]
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have lowerError : |(holdingJumpIndex holdingTimes (acceleration * lowerTime) : ℝ) / acceleration - lowerTime| < tolerance := by
    apply lt_of_not_ge
    intro failure
    exact good ⟨lowerFin, failure⟩
  have upperError : |(holdingJumpIndex holdingTimes (acceleration * upperTime) : ℝ) / acceleration - upperTime| < tolerance := by
    apply lt_of_not_ge
    intro failure
    exact good ⟨upperFin, failure⟩
  have lowerClock := holdingJumpIndex_monotone holdingTimes positive nonexplosion
    (acceleration * lowerTime) (acceleration * time) (mul_nonneg accelerationPositive.le lowerNonnegative)
    (mul_le_mul_of_nonneg_left lowerBefore accelerationPositive.le)
  have upperClock := holdingJumpIndex_monotone holdingTimes positive nonexplosion
    (acceleration * time) (acceleration * upperTime) (mul_nonneg accelerationPositive.le timeNonnegative)
    (mul_le_mul_of_nonneg_left upperAfter.le accelerationPositive.le)
  have lowerDiv : (holdingJumpIndex holdingTimes (acceleration * lowerTime) : ℝ) / acceleration ≤
      (holdingJumpIndex holdingTimes (acceleration * time) : ℝ) / acceleration :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr lowerClock) accelerationPositive.le
  have upperDiv : (holdingJumpIndex holdingTimes (acceleration * time) : ℝ) / acceleration ≤
      (holdingJumpIndex holdingTimes (acceleration * upperTime) : ℝ) / acceleration :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr upperClock) accelerationPositive.le
  rw [abs_le]
  constructor
  · have bound := (abs_lt.mp lowerError).1
    linarith
  · have bound := (abs_lt.mp upperError).2
    linarith

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.holdingJumpClock_uniform_of_finite_grid

