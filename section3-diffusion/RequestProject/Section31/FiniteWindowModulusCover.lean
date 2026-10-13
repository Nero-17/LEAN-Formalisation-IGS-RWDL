import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

/-! A full-horizon modulus event is covered by finitely many anchored
two-window displacement events. The finite grid factor is retained;
small probability on one window alone does not prove tightness. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

theorem ordered_times_in_grid_window (horizon window first second : ℝ)
    (windowPositive : 0 < window) (firstNonnegative : 0 ≤ first)
    (ordered : first ≤ second) (withinHorizon : second ≤ horizon)
    (close : second - first ≤ window) :
    ∃ index : ℕ, index ≤ ⌊horizon / window⌋₊ ∧
      (index : ℝ) * window ≤ first ∧ second ≤ ((index : ℝ) + 2) * window := by
  refine ⟨⌊first / window⌋₊, Nat.floor_mono
    (div_le_div_of_nonneg_right (ordered.trans withinHorizon) windowPositive.le), ?_, ?_⟩
  · exact (le_div_iff₀ windowPositive).mp
      (Nat.floor_le (div_nonneg firstNonnegative windowPositive.le))
  · have next := (div_lt_iff₀ windowPositive).mp (Nat.lt_floor_add_one (first / window))
    nlinarith

theorem large_modulus_has_grid_displacement {Space : Type*} [PseudoMetricSpace Space]
    (path : ℝ → Space) (horizon window radius : ℝ) (windowPositive : 0 < window)
    (large : ∃ first ∈ Set.Icc (0 : ℝ) horizon, ∃ second ∈ Set.Icc (0 : ℝ) horizon,
      |second - first| ≤ window ∧ 2 * radius < dist (path first) (path second)) :
    ∃ index : ℕ, index ≤ ⌊horizon / window⌋₊ ∧
      ∃ time ∈ Set.Icc (0 : ℝ) horizon,
        (index : ℝ) * window ≤ time ∧ time ≤ ((index : ℝ) + 2) * window ∧
          radius < dist (path time) (path ((index : ℝ) * window)) := by
  obtain ⟨first, firstBounds, second, secondBounds, close, far⟩ := large
  have ordered_case (first second : ℝ) (firstBounds : first ∈ Set.Icc (0 : ℝ) horizon)
      (secondBounds : second ∈ Set.Icc (0 : ℝ) horizon) (ordered : first ≤ second)
      (close : second - first ≤ window) (far : 2 * radius < dist (path first) (path second)) :
      ∃ index : ℕ, index ≤ ⌊horizon / window⌋₊ ∧
        ∃ time ∈ Set.Icc (0 : ℝ) horizon,
          (index : ℝ) * window ≤ time ∧ time ≤ ((index : ℝ) + 2) * window ∧
            radius < dist (path time) (path ((index : ℝ) * window)) := by
    obtain ⟨index, indexBound, lower, upper⟩ := ordered_times_in_grid_window
      horizon window first second windowPositive firstBounds.1 ordered secondBounds.2 close
    refine ⟨index, indexBound, ?_⟩
    by_cases firstFar : radius < dist (path first) (path ((index : ℝ) * window))
    · exact ⟨first, firstBounds, lower, ordered.trans upper, firstFar⟩
    · refine ⟨second, secondBounds, lower.trans ordered, upper, ?_⟩
      have triangle := dist_triangle (path first) (path ((index : ℝ) * window)) (path second)
      rw [dist_comm (path ((index : ℝ) * window)) (path second)] at triangle
      have firstNear := le_of_not_gt firstFar
      linarith
  rcases le_total first second with ordered | ordered
  · exact ordered_case first second firstBounds secondBounds ordered (abs_le.mp close).2 far
  · apply ordered_case second first secondBounds firstBounds ordered
    · have lower := (abs_le.mp close).1
      linarith
    · simpa only [dist_comm] using far

theorem modulus_probability_le_grid_sum {Sample Space : Type*} [MeasurableSpace Sample]
    [PseudoMetricSpace Space] (law : Measure Sample) (process : Sample → ℝ → Space)
    (horizon window radius : ℝ) (windowPositive : 0 < window) :
    law {sample | ∃ first ∈ Set.Icc (0 : ℝ) horizon, ∃ second ∈ Set.Icc (0 : ℝ) horizon,
      |second - first| ≤ window ∧ 2 * radius < dist (process sample first) (process sample second)} ≤
    ∑ index ∈ Finset.range (⌊horizon / window⌋₊ + 1),
      law {sample | ∃ time ∈ Set.Icc (0 : ℝ) horizon,
        (index : ℝ) * window ≤ time ∧ time ≤ ((index : ℝ) + 2) * window ∧
          radius < dist (process sample time) (process sample ((index : ℝ) * window))} := by
  apply (measure_mono (show
    {sample | ∃ first ∈ Set.Icc (0 : ℝ) horizon, ∃ second ∈ Set.Icc (0 : ℝ) horizon,
      |second - first| ≤ window ∧ 2 * radius < dist (process sample first) (process sample second)} ⊆
    ⋃ index ∈ Finset.range (⌊horizon / window⌋₊ + 1),
      {sample | ∃ time ∈ Set.Icc (0 : ℝ) horizon,
        (index : ℝ) * window ≤ time ∧ time ≤ ((index : ℝ) + 2) * window ∧
          radius < dist (process sample time) (process sample ((index : ℝ) * window))} from ?_)).trans
      (measure_biUnion_finset_le _ _)
  intro sample large
  obtain ⟨index, bound, witness⟩ := large_modulus_has_grid_displacement
    (process sample) horizon window radius windowPositive large
  exact Set.mem_iUnion.mpr ⟨index, Set.mem_iUnion.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le bound), witness⟩⟩

theorem modulus_probability_le_grid_bound {Sample Space : Type*} [MeasurableSpace Sample]
    [PseudoMetricSpace Space] (law : Measure Sample) (process : Sample → ℝ → Space)
    (horizon window radius : ℝ) (windowPositive : 0 < window) (bound : ℝ≥0∞)
    (windowBounds : ∀ index : ℕ, index ≤ ⌊horizon / window⌋₊ →
      law {sample | ∃ time ∈ Set.Icc (0 : ℝ) horizon,
        (index : ℝ) * window ≤ time ∧ time ≤ ((index : ℝ) + 2) * window ∧
          radius < dist (process sample time) (process sample ((index : ℝ) * window))} ≤ bound) :
    law {sample | ∃ first ∈ Set.Icc (0 : ℝ) horizon, ∃ second ∈ Set.Icc (0 : ℝ) horizon,
      |second - first| ≤ window ∧ 2 * radius < dist (process sample first) (process sample second)} ≤
      (⌊horizon / window⌋₊ + 1 : ℝ≥0∞) * bound := by
  refine (modulus_probability_le_grid_sum law process horizon window radius windowPositive).trans ?_
  calc
    _ ≤ ∑ _index ∈ Finset.range (⌊horizon / window⌋₊ + 1), bound := by
      apply Finset.sum_le_sum
      intro index membership
      exact windowBounds index (Nat.le_of_lt_succ (Finset.mem_range.mp membership))
    _ = _ := by simp [nsmul_eq_mul]

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.ordered_times_in_grid_window
#print axioms IGS.Sec31.DiscreteMarkov.large_modulus_has_grid_displacement
#print axioms IGS.Sec31.DiscreteMarkov.modulus_probability_le_grid_sum
#print axioms IGS.Sec31.DiscreteMarkov.modulus_probability_le_grid_bound
