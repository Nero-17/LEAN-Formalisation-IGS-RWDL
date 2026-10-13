import RequestProject.Section31.VaryingHilbert
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp

/-! The actual varying-space weak convergence definition forces bounded
norms. A norm-null test supported on an unbounded subsequence gives the
contradiction; boundedness is not added to the definition or assumed. -/

namespace IGS.Sec31.VaryingHilbertCore

open Filter Topology
open scoped BigOperators

variable {Core Hilbert : Type*} [AddCommGroup Core] [Module ℝ Core]
  [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
  {LevelHilbert : ℕ → Type*}
  [∀ level, NormedAddCommGroup (LevelHilbert level)]
  [∀ level, InnerProductSpace ℝ (LevelHilbert level)]

theorem strong_zero_of_norm_tendsto_zero
    (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    {sequence : ∀ level, LevelHilbert level}
    (normZero : Tendsto (fun level => ‖sequence level‖) atTop (nhds 0)) :
    core.Strong sequence 0 := by
  intro tolerance tolerancePositive
  refine ⟨0, by simpa using tolerancePositive, ?_⟩
  simpa only [map_zero, sub_zero] using
    (tendsto_order.1 normZero).2 tolerance tolerancePositive

theorem weak_norm_bounded (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    {sequence : ∀ level, LevelHilbert level} {limit : Hilbert}
    (weak : core.Weak sequence limit) :
    ∃ bound : ℝ, ∀ level, ‖sequence level‖ ≤ bound := by
  classical
  by_contra noBound
  push_neg at noBound
  have largeFrequently : ∀ index : ℕ,
      ∃ᶠ level in atTop, (index : ℝ) + 1 < ‖sequence level‖ := by
    intro index
    rw [frequently_atTop']
    intro threshold
    obtain ⟨level, levelLarge⟩ := noBound
      ((index : ℝ) + 1 + ∑ previous ∈ Finset.range (threshold + 1), ‖sequence previous‖)
    have prefixNonnegative : 0 ≤ ∑ previous ∈ Finset.range (threshold + 1), ‖sequence previous‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    refine ⟨level, ?_, by linarith⟩
    by_contra notLater
    have inPrefix : level ∈ Finset.range (threshold + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (le_of_not_gt notLater))
    have prefixBound := Finset.single_le_sum
      (fun previous (_ : previous ∈ Finset.range (threshold + 1)) => norm_nonneg (sequence previous)) inPrefix
    have indexNonnegative : (0 : ℝ) ≤ index := Nat.cast_nonneg index
    linarith
  obtain ⟨selection, selectionStrict, normLarge⟩ := extraction_forall_of_frequently largeFrequently
  let tests : ∀ level, LevelHilbert level := fun level =>
    if level ∈ Set.range selection then (‖sequence level‖ ^ 2)⁻¹ • sequence level else 0
  have selectedNormPositive : ∀ index, 0 < ‖sequence (selection index)‖ := by
    intro index
    exact (by positivity : (0 : ℝ) < (index : ℝ) + 1).trans (normLarge index)
  have selectedTestNorm : ∀ index,
      ‖tests (selection index)‖ = 1 / ‖sequence (selection index)‖ := by
    intro index
    rw [show tests (selection index) =
        (‖sequence (selection index)‖ ^ 2)⁻¹ • sequence (selection index) by
      simp [tests]]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    field_simp [(selectedNormPositive index).ne']
  have testsNormZero : Tendsto (fun level => ‖tests level‖) atTop (nhds 0) := by
    apply Metric.tendsto_atTop.mpr
    intro tolerance tolerancePositive
    obtain ⟨threshold, small⟩ := eventually_atTop.mp
      ((tendsto_order.1 (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).2
        tolerance tolerancePositive)
    refine ⟨selection threshold, ?_⟩
    intro level levelAfter
    by_cases selected : level ∈ Set.range selection
    · obtain ⟨index, rfl⟩ := selected
      have indexAfter : threshold ≤ index := selectionStrict.le_iff_le.mp levelAfter
      have reciprocalBound : 1 / ‖sequence (selection index)‖ ≤ 1 / ((index : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (normLarge index).le
      rw [dist_zero_right, norm_norm, selectedTestNorm]
      exact reciprocalBound.trans_lt (small index indexAfter)
    · have testZero : tests level = 0 := if_neg selected
      rw [testZero]
      simpa using tolerancePositive
  have pairingZero := weak tests 0 (core.strong_zero_of_norm_tendsto_zero testsNormZero)
  have selectedPairing : ∀ index,
      inner ℝ (sequence (selection index)) (tests (selection index)) = 1 := by
    intro index
    simp only [tests, Set.mem_range_self, if_true, real_inner_smul_right, real_inner_self_eq_norm_sq]
    exact inv_mul_cancel₀ (pow_ne_zero 2 (selectedNormPositive index).ne')
  have impossible : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 0) := by
    have subsequenceZero : Tendsto (fun index =>
        inner ℝ (sequence (selection index)) (tests (selection index))) atTop (nhds 0) := by
      simpa only [inner_zero_right] using pairingZero.comp selectionStrict.tendsto_atTop
    simpa only [selectedPairing] using subsequenceZero
  have equal : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds impossible
  norm_num at equal

theorem weak_norm_bounded_positive (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    {sequence : ∀ level, LevelHilbert level} {limit : Hilbert}
    (weak : core.Weak sequence limit) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ level, ‖sequence level‖ ≤ bound := by
  obtain ⟨bound, bounded⟩ := core.weak_norm_bounded weak
  exact ⟨max bound 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun level => (bounded level).trans (le_max_left _ _)⟩

end IGS.Sec31.VaryingHilbertCore

#print axioms IGS.Sec31.VaryingHilbertCore.strong_zero_of_norm_tendsto_zero
#print axioms IGS.Sec31.VaryingHilbertCore.weak_norm_bounded
#print axioms IGS.Sec31.VaryingHilbertCore.weak_norm_bounded_positive
