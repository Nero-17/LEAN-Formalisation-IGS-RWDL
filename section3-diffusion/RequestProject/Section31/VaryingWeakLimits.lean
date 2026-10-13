import RequestProject.Section31.VaryingWeakIdentification

/-! Uniqueness and closed norm bounds for the constructed varying-space weak relation. -/

namespace IGS.Sec31.VaryingHilbertCore

open Filter Topology

variable {Core Hilbert : Type*} [AddCommGroup Core] [Module ℝ Core]
  [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
  {LevelHilbert : ℕ → Type*}
  [∀ level, NormedAddCommGroup (LevelHilbert level)]
  [∀ level, InnerProductSpace ℝ (LevelHilbert level)]
  (core : IGS.Sec31.VaryingHilbertCore Core Hilbert LevelHilbert)

theorem weak_limit_unique (sequence : ∀ level, LevelHilbert level)
    (first second : Hilbert) (first_limit : core.Weak sequence first)
    (second_limit : core.Weak sequence second) : first = second := by
  have bound : ‖first - second‖ ≤ 0 := by
    apply IGS.Sec31.norm_le_of_inner_bound_on_denseRange core.embed core.dense
      (first - second) 0 le_rfl
    intro element
    have pairing_eq := tendsto_nhds_unique
      (first_limit _ _ (core.strong_restrict element))
      (second_limit _ _ (core.strong_restrict element))
    simpa only [inner_sub_left, pairing_eq, sub_self, zero_mul] using (le_rfl : (0 : ℝ) ≤ 0)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm bound (norm_nonneg _)))

theorem strong_limit_unique (sequence : ∀ level, LevelHilbert level)
    (first second : Hilbert) (first_limit : core.Strong sequence first)
    (second_limit : core.Strong sequence second) : first = second :=
  core.weak_limit_unique sequence first second
    (core.strong_implies_weak first_limit) (core.strong_implies_weak second_limit)

theorem weak_norm_le_of_frequently_norm_le
    (sequence : ∀ level, LevelHilbert level) (limit : Hilbert)
    (weak_convergence : core.Weak sequence limit) (bound : ℝ) (bound_nonnegative : 0 ≤ bound)
    (frequent_bound : ∃ᶠ level in atTop, ‖sequence level‖ ≤ bound) :
    ‖limit‖ ≤ bound := by
  apply IGS.Sec31.norm_le_of_inner_bound_on_denseRange core.embed core.dense
    limit bound bound_nonnegative
  intro element
  exact le_of_tendsto_of_tendsto_of_frequently
    (weak_convergence _ _ (core.strong_restrict element))
    (tendsto_const_nhds.mul (core.norm_converges element))
    (frequent_bound.mono (fun level bound_at_level =>
      (real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right bound_at_level (norm_nonneg _))))

end IGS.Sec31.VaryingHilbertCore
