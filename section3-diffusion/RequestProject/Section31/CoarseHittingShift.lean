import RequestProject.Section31.BoundedCoarseHittingStops

/-! Deterministic regeneration identities for the actual coarse-hit scanner.
The local scanner starts at the actual stopped coarse point. Capped next-hit
times decompose exactly, including the noncompletion sentinel. No probabilistic
Markov or regeneration identity is an assumption. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped BigOperators ProbabilityTheory Classical
noncomputable section
set_option maxHeartbeats 4000000

variable {X : Type} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X]

def shiftPath (start : ℕ) (path : ℕ → X) : ℕ → X :=
  fun index => path (start + index)

/-- The global and shifted scanners have the same last coarse point. Their
counts differ by the actual count already accumulated before the shift. -/
theorem coarseArrivalState_shift (coarse : Finset X) (path : ℕ → X) (start offset : ℕ)
    (startsCoarse : path start ∈ coarse)
    (currentState : (coarseArrivalState coarse path start).1 = some (path start)) :
    (coarseArrivalState coarse path (start + offset)).1 =
        (coarseArrivalState coarse (shiftPath start path) offset).1 ∧
      (coarseArrivalState coarse path (start + offset)).2 + 1 =
        (coarseArrivalState coarse path start).2 +
          (coarseArrivalState coarse (shiftPath start path) offset).2 := by
  induction offset with
  | zero =>
    simpa only [Nat.add_zero, coarseArrivalState, shiftPath, if_pos startsCoarse] using
      (show (coarseArrivalState coarse path start).1 = some (path start) ∧
        (coarseArrivalState coarse path start).2 + 1 = (coarseArrivalState coarse path start).2 + 1
        from ⟨currentState, rfl⟩)
  | succ offset inductionHypothesis =>
    have lastEqual := inductionHypothesis.1
    have countEqual := inductionHypothesis.2
    by_cases arrives : path (start + offset + 1) ∈ coarse ∧
        (coarseArrivalState coarse (shiftPath start path) offset).1 ≠
          some (path (start + offset + 1))
    · have globalArrives : path (start + offset + 1) ∈ coarse ∧
          (coarseArrivalState coarse path (start + offset)).1 ≠ some (path (start + offset + 1)) := by
        rw [lastEqual]
        exact arrives
      have localArrives : (shiftPath start path) (offset + 1) ∈ coarse ∧
          (coarseArrivalState coarse (shiftPath start path) offset).1 ≠
            some ((shiftPath start path) (offset + 1)) := by
        simpa only [shiftPath, Nat.add_assoc] using arrives
      have globalNext : coarseArrivalState coarse path (start + (offset + 1)) =
          (some (path (start + offset + 1)), (coarseArrivalState coarse path (start + offset)).2 + 1) := by
        rw [← Nat.add_assoc, coarseArrivalState, coarseArrivalUpdate, if_pos globalArrives]
      have localNext : coarseArrivalState coarse (shiftPath start path) (offset + 1) =
          (some ((shiftPath start path) (offset + 1)),
            (coarseArrivalState coarse (shiftPath start path) offset).2 + 1) := by
        rw [coarseArrivalState, coarseArrivalUpdate, if_pos localArrives]
      simp only [globalNext, localNext]
      constructor
      · simp only [shiftPath, Nat.add_assoc]
      · dsimp only
        omega
    · have globalDoesNotArrive : ¬(path (start + offset + 1) ∈ coarse ∧
          (coarseArrivalState coarse path (start + offset)).1 ≠ some (path (start + offset + 1))) := by
        rw [lastEqual]
        exact arrives
      have localDoesNotArrive : ¬((shiftPath start path) (offset + 1) ∈ coarse ∧
          (coarseArrivalState coarse (shiftPath start path) offset).1 ≠
            some ((shiftPath start path) (offset + 1))) := by
        simpa only [shiftPath, Nat.add_assoc] using arrives
      have globalNext : coarseArrivalState coarse path (start + (offset + 1)) =
          coarseArrivalState coarse path (start + offset) := by
        rw [← Nat.add_assoc, coarseArrivalState, coarseArrivalUpdate, if_neg globalDoesNotArrive]
      have localNext : coarseArrivalState coarse (shiftPath start path) (offset + 1) =
          coarseArrivalState coarse (shiftPath start path) offset := by
        rw [coarseArrivalState, coarseArrivalUpdate, if_neg localDoesNotArrive]
      simpa only [globalNext, localNext] using inductionHypothesis

/-- At an actual completed coarse arrival, the shifted count starts at one.
The next global arrival threshold is exactly the second local coarse arrival. -/
theorem coarseArrival_next_threshold_shift (coarse : Finset X) (arrival cap : ℕ)
    (path : ℕ → X)
    (beforeCap : ((boundedCoarseArrival coarse arrival cap).time path).val < cap)
    (offset : ℕ) :
    arrival + 2 ≤ (coarseArrivalState coarse path
      (((boundedCoarseArrival coarse arrival cap).time path).val + offset)).2 ↔
      2 ≤ (coarseArrivalState coarse
        (shiftPath ((boundedCoarseArrival coarse arrival cap).time path).val path) offset).2 := by
  have stopped := boundedCoarseArrival_is_coarse coarse arrival cap path beforeCap
  have shift := (coarseArrivalState_shift coarse path
    ((boundedCoarseArrival coarse arrival cap).time path).val offset stopped.1 stopped.2).2
  have initialCount := boundedCoarseArrival_count_eq coarse arrival cap path beforeCap
  omega

/-- The exact next-hit decomposition on the same actual path. The local cap is
the remaining observation horizon. If no new distinct coarse point is reached,
both sides equal the original cap. -/
theorem boundedCoarseArrival_next_shift (coarse : Finset X) (arrival cap : ℕ)
    (path : ℕ → X)
    (beforeCap : ((boundedCoarseArrival coarse arrival cap).time path).val < cap) :
    ((boundedCoarseArrival coarse (arrival + 1) cap).time path).val =
      ((boundedCoarseArrival coarse arrival cap).time path).val +
        ((boundedCoarseArrival coarse 1
          (cap - ((boundedCoarseArrival coarse arrival cap).time path).val)).time
          (shiftPath ((boundedCoarseArrival coarse arrival cap).time path).val path)).val := by
  let start := ((boundedCoarseArrival coarse arrival cap).time path).val
  let next := ((boundedCoarseArrival coarse (arrival + 1) cap).time path).val
  let localNext := ((boundedCoarseArrival coarse 1 (cap - start)).time (shiftPath start path)).val
  have startBound : start < cap := beforeCap
  have globalBound : next ≤ cap :=
    Nat.le_of_lt_succ ((boundedCoarseArrival coarse (arrival + 1) cap).time path).isLt
  have localBound : localNext ≤ cap - start :=
    Nat.le_of_lt_succ ((boundedCoarseArrival coarse 1 (cap - start)).time (shiftPath start path)).isLt
  have ordered : start ≤ next := by
    have ordered := boundedCoarseArrival_monotone coarse cap path (Nat.le_succ arrival)
    dsimp only at ordered
    simp only [Nat.succ_eq_add_one] at ordered
    exact ordered
  change next = start + localNext
  apply Nat.le_antisymm
  · by_cases localBeforeCap : localNext < cap - start
    · have localCount := boundedCoarseArrival_occurs coarse 1 (cap - start)
        (shiftPath start path) localBeforeCap
      have threshold : arrival + 2 ≤ (coarseArrivalState coarse path (start + localNext)).2 :=
        (coarseArrival_next_threshold_shift coarse arrival cap path beforeCap localNext).mpr localCount
      exact boundedCoarseArrival_le_of_count coarse (arrival + 1) cap (start + localNext) path threshold
    · have capped : start + localNext = cap := by omega
      rw [capped]
      exact globalBound
  · by_cases nextBeforeCap : next < cap
    · have globalCount := boundedCoarseArrival_occurs coarse (arrival + 1) cap path nextBeforeCap
      have globalThreshold : arrival + 2 ≤
          (coarseArrivalState coarse path (start + (next - start))).2 := by
        simpa only [Nat.add_sub_of_le ordered] using globalCount
      have localThreshold : 2 ≤ (coarseArrivalState coarse (shiftPath start path) (next - start)).2 :=
        (coarseArrival_next_threshold_shift coarse arrival cap path beforeCap (next - start)).mp globalThreshold
      have localLe := boundedCoarseArrival_le_of_count coarse 1 (cap - start) (next - start)
        (shiftPath start path) localThreshold
      change localNext ≤ next - start at localLe
      omega
    · omega

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.coarseArrivalState_shift
#print axioms IGS.Sec31.DiscreteMarkov.coarseArrival_next_threshold_shift
#print axioms IGS.Sec31.DiscreteMarkov.boundedCoarseArrival_next_shift
