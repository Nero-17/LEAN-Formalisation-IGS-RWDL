import RequestProject.Section31.FiniteWindowModulusCover

/-! The full real-time modulus of a literal floor-clock path is controlled by
finite integer windows. Absolute floors are retained, including their rounding
error. This lemma does not assume continuity of the step paths. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory
open scoped ENNReal
noncomputable section

theorem floor_clock_window_displacement {Space : Type*} [PseudoMetricSpace Space]
    (path : ℕ → Space) (rate window radius time : ℝ) (index : ℕ)
    (rateNonnegative : 0 ≤ rate)
    (afterAnchor : (index : ℝ) * window ≤ time)
    (beforeEnd : time ≤ ((index : ℝ) + 2) * window)
    (far : radius < dist (path ⌊time * rate⌋₊)
      (path ⌊(index : ℝ) * window * rate⌋₊)) :
    ∃ offset : ℕ,
      offset ≤ ⌊((index : ℝ) + 2) * window * rate⌋₊ -
        ⌊(index : ℝ) * window * rate⌋₊ ∧
      radius < dist (path (⌊(index : ℝ) * window * rate⌋₊ + offset))
        (path ⌊(index : ℝ) * window * rate⌋₊) := by
  have lower : ⌊(index : ℝ) * window * rate⌋₊ ≤ ⌊time * rate⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_right afterAnchor rateNonnegative)
  have upper : ⌊time * rate⌋₊ ≤ ⌊((index : ℝ) + 2) * window * rate⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_right beforeEnd rateNonnegative)
  refine ⟨⌊time * rate⌋₊ - ⌊(index : ℝ) * window * rate⌋₊,
    Nat.sub_le_sub_right upper _, ?_⟩
  simpa only [Nat.add_sub_of_le lower] using far

theorem floor_clock_modulus_probability_le_grid_bound
    {Sample Space : Type*} [MeasurableSpace Sample] [PseudoMetricSpace Space]
    (law : Measure Sample) (process : Sample → ℕ → Space)
    (rate horizon window radius : ℝ) (rateNonnegative : 0 ≤ rate)
    (windowPositive : 0 < window) (bound : ℝ≥0∞)
    (integerWindowBounds : ∀ index : ℕ, index ≤ ⌊horizon / window⌋₊ →
      law {sample | ∃ offset : ℕ,
        offset ≤ ⌊((index : ℝ) + 2) * window * rate⌋₊ -
          ⌊(index : ℝ) * window * rate⌋₊ ∧
        radius < dist
          (process sample (⌊(index : ℝ) * window * rate⌋₊ + offset))
          (process sample ⌊(index : ℝ) * window * rate⌋₊)} ≤ bound) :
    law {sample | ∃ first ∈ Set.Icc (0 : ℝ) horizon,
      ∃ second ∈ Set.Icc (0 : ℝ) horizon, |second - first| ≤ window ∧
        2 * radius < dist (process sample ⌊first * rate⌋₊)
          (process sample ⌊second * rate⌋₊)} ≤
      (⌊horizon / window⌋₊ + 1 : ℝ≥0∞) * bound := by
  apply modulus_probability_le_grid_bound law
    (fun sample time => process sample ⌊time * rate⌋₊)
    horizon window radius windowPositive bound
  intro index indexBound
  refine (measure_mono ?_).trans (integerWindowBounds index indexBound)
  intro sample witness
  obtain ⟨time, _, afterAnchor, beforeEnd, far⟩ := witness
  exact floor_clock_window_displacement (process sample) rate window radius time index
    rateNonnegative afterAnchor beforeEnd far

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.floor_clock_window_displacement
#print axioms IGS.Sec31.DiscreteMarkov.floor_clock_modulus_probability_le_grid_bound
