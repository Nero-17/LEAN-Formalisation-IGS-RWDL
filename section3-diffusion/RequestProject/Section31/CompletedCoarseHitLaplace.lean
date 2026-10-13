import RequestProject.Section31.CoarseHittingShift
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Actual finite-horizon completed coarse-hit Laplace weights. A cap value is
noncompletion and has weight zero. The multiplicative decomposition follows
from the deterministic capped next-hit identity on the same path. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped BigOperators ProbabilityTheory Classical
noncomputable section
set_option maxHeartbeats 4000000

variable {X : Type} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X]

def completedCoarseHitLaplace (coarse : Finset X) (arrival cap : ℕ)
    (scale : ℝ) (path : ℕ → X) : ℝ :=
  if ((boundedCoarseArrival coarse arrival cap).time path).val < cap then
    Real.exp (-(((boundedCoarseArrival coarse arrival cap).time path).val : ℝ) / scale)
  else 0

theorem BoundedHistoryStop.time_eq_of_prefix_eq {cap : ℕ}
    (stop : BoundedHistoryStop (X := X) cap) (first second : ℕ → X)
    (agree : ∀ index ≤ cap, first index = second index) :
    stop.time first = stop.time second := by
  have prefixEquality : frestrictLe (stop.time first).val first =
      frestrictLe (stop.time first).val second := by
    funext index
    exact agree index.val ((Finset.mem_Iic.mp index.property).trans
      (Nat.le_of_lt_succ (stop.time first).isLt))
  have belongs := (stop.level_iff (stop.time first) first).mp rfl
  rw [prefixEquality] at belongs
  exact ((stop.level_iff (stop.time first) second).mpr belongs).symm

def completedCoarseHitPastWeight {cap : ℕ} (scale : ℝ) (index : Fin (cap + 1))
    (_history : Finset.Iic index.val → X) : ℝ :=
  if index.val < cap then Real.exp (-(index.val : ℝ) / scale) else 0

def completedCoarseHitFutureWeight (coarse : Finset X) (cap : ℕ) (scale : ℝ)
    (index : Fin (cap + 1)) (block : Finset.Iic cap → X) : ℝ :=
  completedCoarseHitLaplace coarse 1 (cap - index.val) scale (completedHistory block)

theorem completedCoarseHitLaplace_eq_past_weight (coarse : Finset X) (arrival cap : ℕ)
    (scale : ℝ) (path : ℕ → X) :
    completedCoarseHitLaplace coarse arrival cap scale path =
      completedCoarseHitPastWeight scale ((boundedCoarseArrival coarse arrival cap).time path)
        (frestrictLe ((boundedCoarseArrival coarse arrival cap).time path).val path) := rfl

/-- The local completed-duration payoff is an actual finite future-block
function. Arbitrarily completing the finite block beyond its end cannot alter
the local stop, because its remaining cap is at most the block length. -/
theorem completedCoarseHitFutureWeight_eq_shift (coarse : Finset X) (cap : ℕ) (scale : ℝ)
    (index : Fin (cap + 1)) (path : ℕ → X) :
    completedCoarseHitFutureWeight coarse cap scale index (futurePrefix index.val cap path) =
      completedCoarseHitLaplace coarse 1 (cap - index.val) scale (shiftPath index.val path) := by
  have hitEquality := (boundedCoarseArrival coarse 1 (cap - index.val)).time_eq_of_prefix_eq
    (completedHistory (futurePrefix index.val cap path)) (shiftPath index.val path) (by
      intro entry bounded
      have beforeEnd : entry ≤ cap := bounded.trans (Nat.sub_le _ _)
      simp only [completedHistory, dif_pos beforeEnd, futurePrefix, shiftPath])
  unfold completedCoarseHitFutureWeight completedCoarseHitLaplace
  rw [hitEquality]

theorem completedCoarseHitLaplace_nonnegative (coarse : Finset X) (arrival cap : ℕ)
    (scale : ℝ) (path : ℕ → X) :
    0 ≤ completedCoarseHitLaplace coarse arrival cap scale path := by
  unfold completedCoarseHitLaplace
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem completedCoarseHitLaplace_le_one (coarse : Finset X) (arrival cap : ℕ)
    (scale : ℝ) (scalePositive : 0 < scale) (path : ℕ → X) :
    completedCoarseHitLaplace coarse arrival cap scale path ≤ 1 := by
  unfold completedCoarseHitLaplace
  split_ifs
  · apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) scalePositive.le
  · exact zero_le_one

theorem completedCoarseHitLaplace_eq_zero_at_cap (coarse : Finset X) (arrival cap : ℕ)
    (scale : ℝ) (path : ℕ → X)
    (capped : ((boundedCoarseArrival coarse arrival cap).time path).val = cap) :
    completedCoarseHitLaplace coarse arrival cap scale path = 0 := by
  simp only [completedCoarseHitLaplace, capped, lt_self_iff_false, if_false]

/-- This equality includes the case where either the current hit or the next
hit is not completed. It does not require a stopping-time Markov hypothesis. -/
theorem completedCoarseHitLaplace_succ_product (coarse : Finset X) (arrival cap : ℕ)
    (scale : ℝ) (path : ℕ → X) :
    completedCoarseHitLaplace coarse (arrival + 1) cap scale path =
      completedCoarseHitLaplace coarse arrival cap scale path *
        completedCoarseHitLaplace coarse 1
          (cap - ((boundedCoarseArrival coarse arrival cap).time path).val) scale
          (shiftPath ((boundedCoarseArrival coarse arrival cap).time path).val path) := by
  let start := ((boundedCoarseArrival coarse arrival cap).time path).val
  let next := ((boundedCoarseArrival coarse (arrival + 1) cap).time path).val
  let localNext := ((boundedCoarseArrival coarse 1 (cap - start)).time (shiftPath start path)).val
  have startBound : start ≤ cap :=
    Nat.le_of_lt_succ ((boundedCoarseArrival coarse arrival cap).time path).isLt
  have nextBound : next ≤ cap :=
    Nat.le_of_lt_succ ((boundedCoarseArrival coarse (arrival + 1) cap).time path).isLt
  have localBound : localNext ≤ cap - start :=
    Nat.le_of_lt_succ ((boundedCoarseArrival coarse 1 (cap - start)).time (shiftPath start path)).isLt
  have ordered : start ≤ next := by
    have ordered := boundedCoarseArrival_monotone coarse cap path (Nat.le_succ arrival)
    dsimp only at ordered
    simp only [Nat.succ_eq_add_one] at ordered
    exact ordered
  change (if next < cap then Real.exp (-(next : ℝ) / scale) else 0) =
    (if start < cap then Real.exp (-(start : ℝ) / scale) else 0) *
      (if localNext < cap - start then Real.exp (-(localNext : ℝ) / scale) else 0)
  by_cases startBeforeCap : start < cap
  · have decomposition : next = start + localNext :=
      boundedCoarseArrival_next_shift coarse arrival cap path startBeforeCap
    by_cases nextBeforeCap : next < cap
    · have localBeforeCap : localNext < cap - start := by omega
      rw [if_pos nextBeforeCap, if_pos startBeforeCap, if_pos localBeforeCap, ← Real.exp_add]
      congr 1
      rw [decomposition, Nat.cast_add]
      ring
    · have localCapped : ¬localNext < cap - start := by omega
      rw [if_neg nextBeforeCap, if_pos startBeforeCap, if_neg localCapped, mul_zero]
  · have nextCapped : ¬next < cap := by omega
    rw [if_neg nextCapped, if_neg startBeforeCap, zero_mul]

/-- The same exact product in the stopped-history/future-block format consumed
by the proved bounded stopping Markov integral identity. -/
theorem completedCoarseHitLaplace_succ_block_product (coarse : Finset X) (arrival cap : ℕ)
    (scale : ℝ) (path : ℕ → X) :
    completedCoarseHitLaplace coarse (arrival + 1) cap scale path =
      completedCoarseHitPastWeight scale ((boundedCoarseArrival coarse arrival cap).time path)
        (frestrictLe ((boundedCoarseArrival coarse arrival cap).time path).val path) *
      completedCoarseHitFutureWeight coarse cap scale ((boundedCoarseArrival coarse arrival cap).time path)
        (futurePrefix ((boundedCoarseArrival coarse arrival cap).time path).val cap path) := by
  rw [completedCoarseHitFutureWeight_eq_shift, ← completedCoarseHitLaplace_eq_past_weight,
    completedCoarseHitLaplace_succ_product]

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.completedCoarseHitLaplace_nonnegative
#print axioms IGS.Sec31.DiscreteMarkov.completedCoarseHitLaplace_le_one
#print axioms IGS.Sec31.DiscreteMarkov.completedCoarseHitLaplace_eq_zero_at_cap
#print axioms IGS.Sec31.DiscreteMarkov.completedCoarseHitLaplace_succ_product
#print axioms IGS.Sec31.DiscreteMarkov.completedCoarseHitFutureWeight_eq_shift
#print axioms IGS.Sec31.DiscreteMarkov.completedCoarseHitLaplace_succ_block_product
