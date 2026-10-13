import RequestProject.Section31.VaryingHilbert
import RequestProject.Section31.VaryingWeakResidual
import Mathlib.Analysis.InnerProductSpace.Continuous

/-! Weak residual bounds for the explicitly defined asymptotic relation.

Testing on the dense core suffices. Thus no assumed strong approximation of
the unknown residual, and no false L² orthogonality of harmonic extensions,
is required to identify its norm bound.
-/

namespace IGS.Sec31

open Filter Topology

theorem norm_le_of_inner_bound_on_denseRange
    {Core Hilbert : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    (embedding : Core → Hilbert) (dense : DenseRange embedding)
    (residual : Hilbert) (bound : ℝ) (bound_nonnegative : 0 ≤ bound)
    (test_bounds : ∀ element, inner ℝ residual (embedding element) ≤ bound * ‖embedding element‖) :
    ‖residual‖ ≤ bound := by
  have closed : IsClosed {test : Hilbert | inner ℝ residual test ≤ bound * ‖test‖} :=
    isClosed_le (continuous_const.inner continuous_id) (continuous_const.mul continuous_norm)
  have subset : Set.range embedding ⊆ {test : Hilbert | inner ℝ residual test ≤ bound * ‖test‖} := by
    rintro _ ⟨element, rfl⟩
    exact test_bounds element
  have all_tests := closure_minimal subset closed
  have self_bound : inner ℝ residual residual ≤ bound * ‖residual‖ := all_tests (dense residual)
  rw [real_inner_self_eq_norm_sq] at self_bound
  by_contra not_bounded
  have positive_residual : 0 < ‖residual‖ := bound_nonnegative.trans_lt (lt_of_not_ge not_bounded)
  nlinarith

variable {Core Hilbert : Type*} [AddCommGroup Core] [Module ℝ Core]
  [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
  {LevelHilbert : ℕ → Type*}
  [∀ level, NormedAddCommGroup (LevelHilbert level)]
  [∀ level, InnerProductSpace ℝ (LevelHilbert level)]

theorem asymptotic_weak_residual_norm_bound
    (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    (functions approximations : ∀ level, LevelHilbert level)
    (function approximation : Hilbert) (error : ℝ) (error_nonnegative : 0 ≤ error)
    (weak_convergence : core.Weak functions function)
    (strong_convergence : core.Strong approximations approximation)
    (error_bound : ∀ᶠ level in atTop, ‖functions level - approximations level‖ ≤ error) :
    ‖function - approximation‖ ≤ error := by
  apply norm_le_of_inner_bound_on_denseRange core.embed core.dense
    (function - approximation) error error_nonnegative
  intro element
  have functions_pairings := weak_convergence (fun level => core.restrict level element)
    (core.embed element) (core.strong_restrict element)
  have approximations_pairings := core.strong_inner_tendsto strong_convergence
    (core.strong_restrict element)
  have residual_pairings : Tendsto
      (fun level => inner ℝ (functions level - approximations level) (core.restrict level element))
        atTop (𝓝 (inner ℝ (function - approximation) (core.embed element))) := by
    simpa only [inner_sub_left] using functions_pairings.sub approximations_pairings
  exact le_of_tendsto_of_tendsto residual_pairings
    (tendsto_const_nhds.mul (core.norm_converges element))
    (error_bound.mono (fun level bound => (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right bound (norm_nonneg _))))

theorem asymptotic_harmonic_limits_identified
    (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    (functions : ∀ level, LevelHilbert level) (function : Hilbert)
    (approximations : ℕ → ∀ level, LevelHilbert level)
    (limits : ℕ → Hilbert) (errors : ℕ → ℝ)
    (weak_convergence : core.Weak functions function)
    (strong_convergence : ∀ depth, core.Strong (approximations depth) (limits depth))
    (errors_nonnegative : ∀ depth, 0 ≤ errors depth)
    (error_bounds : ∀ depth, ∀ᶠ level in atTop,
      ‖functions level - approximations depth level‖ ≤ errors depth)
    (errors_vanish : Tendsto errors atTop (𝓝 0)) :
    (∀ depth, ‖function - limits depth‖ ≤ errors depth) ∧
      Tendsto limits atTop (𝓝 function) := by
  have bounds : ∀ depth, ‖function - limits depth‖ ≤ errors depth := fun depth =>
    asymptotic_weak_residual_norm_bound core functions (approximations depth)
      function (limits depth) (errors depth) (errors_nonnegative depth)
      weak_convergence (strong_convergence depth) (error_bounds depth)
  exact ⟨bounds, tendsto_of_vanishing_norm_error limits function errors bounds errors_vanish⟩

end IGS.Sec31
