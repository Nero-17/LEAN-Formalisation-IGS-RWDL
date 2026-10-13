import RequestProject.Section31.VaryingHilbert
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Order.Filter.Finite

/-! # Strong recovery at every original discretization index

A dense core and asymptotic preservation of each core norm suffice to
construct a strongly convergent sequence for every limiting vector. A slow
diagonal selects core approximants, while the restrictions retain the original
level index. No subsequence of discretizations or concrete geometric limit is
assumed. The EIGS common-space geometry and speed-measure convergence remain
separate obligations.
-/

namespace IGS.Sec31

open Filter Topology

private theorem exists_slow_index (threshold : ℕ → ℕ) :
    ∃ selection : ℕ → ℕ, Tendsto selection atTop atTop ∧
      ∀ᶠ level in atTop, threshold (selection level) ≤ level := by
  classical
  let selection : ℕ → ℕ := fun level =>
    Nat.findGreatest (fun depth => threshold depth ≤ level) level
  refine ⟨selection, ?_, ?_⟩
  · apply tendsto_atTop.2
    intro depth
    filter_upwards [eventually_ge_atTop depth, eventually_ge_atTop (threshold depth)]
      with level depth_below_level threshold_below_level
    exact Nat.le_findGreatest depth_below_level threshold_below_level
  · filter_upwards [eventually_ge_atTop (threshold 0)] with level threshold_below_level
    exact Nat.findGreatest_spec (P := fun depth => threshold depth ≤ level)
      (Nat.zero_le level) threshold_below_level

namespace VaryingHilbertCore

variable {Core Hilbert : Type*} [AddCommGroup Core] [Module ℝ Core]
  [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
  {LevelHilbert : ℕ → Type*}
  [∀ level, NormedAddCommGroup (LevelHilbert level)]
  [∀ level, InnerProductSpace ℝ (LevelHilbert level)]

/-- Recovery is a restriction of a core element at each original level. -/
theorem exists_strong_core_recovery
    (core : VaryingHilbertCore Core Hilbert LevelHilbert) (target : Hilbert) :
    ∃ approximants : ℕ → Core,
      core.Strong (fun level => core.restrict level (approximants level)) target := by
  classical
  have approximants_exist : ∀ depth : ℕ, ∃ element : Core,
      ‖core.embed element - target‖ < 1 / ((depth : ℝ) + 1) := by
    intro depth
    obtain ⟨element, close⟩ := core.dense.exists_dist_lt target
      (show 0 < 1 / ((depth : ℝ) + 1) by positivity)
    exact ⟨element, by simpa only [dist_eq_norm, norm_sub_rev] using close⟩
  choose approximants approximants_close using approximants_exist
  have pair_control_eventually (depth : ℕ) :
      ∀ᶠ level in atTop, ∀ earlier ≤ depth,
        ‖core.restrict level (approximants depth - approximants earlier)‖ <
          ‖core.embed (approximants depth - approximants earlier)‖ +
            1 / ((depth : ℝ) + 1) := by
    have finite_control : ∀ᶠ level in atTop,
        ∀ earlier ∈ Finset.range (depth + 1),
          ‖core.restrict level (approximants depth - approximants earlier)‖ <
            ‖core.embed (approximants depth - approximants earlier)‖ +
              1 / ((depth : ℝ) + 1) := by
      apply (Finset.eventually_all _).mpr
      intro earlier _
      exact (core.norm_converges (approximants depth - approximants earlier)).eventually
        (Iio_mem_nhds (lt_add_of_pos_right _ (by positivity)))
    filter_upwards [finite_control] with level control earlier earlier_below_depth
    exact control earlier (Finset.mem_range.mpr (Nat.lt_succ_of_le earlier_below_depth))
  have thresholds_exist : ∀ depth : ℕ, ∃ threshold : ℕ, ∀ level ≥ threshold,
      ∀ earlier ≤ depth,
        ‖core.restrict level (approximants depth - approximants earlier)‖ <
          ‖core.embed (approximants depth - approximants earlier)‖ +
            1 / ((depth : ℝ) + 1) :=
    fun depth => eventually_atTop.mp (pair_control_eventually depth)
  choose threshold pair_control using thresholds_exist
  obtain ⟨selection, selection_tendsto, selection_valid⟩ := exists_slow_index threshold
  refine ⟨fun level => approximants (selection level), ?_⟩
  intro tolerance tolerance_positive
  have small_tolerances : ∀ᶠ depth : ℕ in atTop,
      1 / ((depth : ℝ) + 1) < tolerance / 4 :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Iio_mem_nhds (by positivity))
  obtain ⟨depth, depth_small⟩ := small_tolerances.exists
  refine ⟨approximants depth,
    (approximants_close depth).trans (depth_small.trans (by linarith)), ?_⟩
  filter_upwards [selection_valid,
    selection_tendsto.eventually (eventually_ge_atTop depth),
    selection_tendsto.eventually small_tolerances]
    with level selected_valid depth_below_selected selected_small
  have restricted_bound := pair_control (selection level) level selected_valid
    depth depth_below_selected
  have limiting_bound :
      ‖core.embed (approximants (selection level) - approximants depth)‖ ≤
        ‖core.embed (approximants (selection level)) - target‖ +
          ‖core.embed (approximants depth) - target‖ := by
    rw [map_sub]
    simpa only [norm_sub_rev target] using
      norm_sub_le_norm_sub_add_norm_sub
        (core.embed (approximants (selection level))) target (core.embed (approximants depth))
  rw [map_sub] at restricted_bound
  exact restricted_bound.trans (by
    linarith [approximants_close (selection level), approximants_close depth])

/-- Every limiting vector has a genuine strongly convergent sequence at all levels. -/
theorem exists_strong_recovery
    (core : VaryingHilbertCore Core Hilbert LevelHilbert) (target : Hilbert) :
    ∃ sequence : ∀ level, LevelHilbert level, core.Strong sequence target := by
  obtain ⟨approximants, converges⟩ := core.exists_strong_core_recovery target
  exact ⟨fun level => core.restrict level (approximants level), converges⟩

/-- In particular the weak test-vector relation has every possible limiting target. -/
theorem exists_strong_and_weak_recovery
    (core : VaryingHilbertCore Core Hilbert LevelHilbert) (target : Hilbert) :
    ∃ sequence : ∀ level, LevelHilbert level,
      core.Strong sequence target ∧ core.Weak sequence target := by
  obtain ⟨sequence, converges⟩ := core.exists_strong_recovery target
  exact ⟨sequence, converges, core.strong_implies_weak converges⟩

end VaryingHilbertCore
end IGS.Sec31
