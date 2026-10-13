import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-! Weak identification through actual inner products on varying spaces.

Harmonic extensions are energy projections, not in general L² orthogonal
projections. This argument uses their norm error instead of false L² normal
equations: pass Cauchy--Schwarz to the limit against an approximation of the
limiting residual itself. It supplies the identification step once concrete
Kuwae--Shioya test approximations and spline pairing limits are constructed.
-/

namespace IGS.Sec31

open Filter Topology

variable {Hilbert : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
  {LevelHilbert : ℕ → Type*}
  [∀ level, NormedAddCommGroup (LevelHilbert level)]
  [∀ level, InnerProductSpace ℝ (LevelHilbert level)]

theorem varying_weak_residual_norm_bound
    (functions approximations tests : ∀ level, LevelHilbert level)
    (function approximation : Hilbert) (error : ℝ) (error_nonnegative : 0 ≤ error)
    (norm_convergence : Tendsto (fun level => ‖tests level‖)
      atTop (𝓝 ‖function - approximation‖))
    (function_pairings : Tendsto (fun level => inner ℝ (functions level) (tests level))
      atTop (𝓝 (inner ℝ function (function - approximation))))
    (approximation_pairings :
      Tendsto (fun level => inner ℝ (approximations level) (tests level))
        atTop (𝓝 (inner ℝ approximation (function - approximation))))
    (error_bound : ∀ᶠ level in atTop, ‖functions level - approximations level‖ ≤ error) :
    ‖function - approximation‖ ≤ error := by
  have pairing_convergence :
      Tendsto (fun level => inner ℝ (functions level - approximations level) (tests level))
        atTop (𝓝 (inner ℝ (function - approximation) (function - approximation))) := by
    simpa only [inner_sub_left] using function_pairings.sub approximation_pairings
  have limiting_bound := le_of_tendsto_of_tendsto pairing_convergence
    (tendsto_const_nhds.mul norm_convergence)
    (error_bound.mono (fun level bound =>
      (real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right bound (norm_nonneg _))))
  rw [real_inner_self_eq_norm_sq] at limiting_bound
  by_contra not_bounded
  have positive_residual : 0 < ‖function - approximation‖ :=
    error_nonnegative.trans_lt (lt_of_not_ge not_bounded)
  nlinarith

theorem tendsto_of_vanishing_norm_error
    (approximations : ℕ → Hilbert) (function : Hilbert) (errors : ℕ → ℝ)
    (bounds : ∀ depth, ‖function - approximations depth‖ ≤ errors depth)
    (errors_vanish : Tendsto errors atTop (𝓝 0)) :
    Tendsto approximations atTop (𝓝 function) := by
  apply Metric.tendsto_nhds.2
  intro tolerance tolerance_positive
  filter_upwards [(tendsto_order.1 errors_vanish).2 tolerance tolerance_positive]
    with depth error_small
  simpa only [dist_eq_norm, norm_sub_rev] using
    (bounds depth).trans_lt error_small

theorem varying_harmonic_limits_identified
    (functions : ∀ level, LevelHilbert level)
    (approximations tests : ℕ → ∀ level, LevelHilbert level)
    (function : Hilbert) (limits : ℕ → Hilbert) (errors : ℕ → ℝ)
    (errors_nonnegative : ∀ depth, 0 ≤ errors depth)
    (norm_convergence : ∀ depth, Tendsto (fun level => ‖tests depth level‖)
      atTop (𝓝 ‖function - limits depth‖))
    (function_pairings : ∀ depth,
      Tendsto (fun level => inner ℝ (functions level) (tests depth level))
        atTop (𝓝 (inner ℝ function (function - limits depth))))
    (approximation_pairings : ∀ depth,
      Tendsto (fun level => inner ℝ (approximations depth level) (tests depth level))
        atTop (𝓝 (inner ℝ (limits depth) (function - limits depth))))
    (error_bound : ∀ depth, ∀ᶠ level in atTop,
      ‖functions level - approximations depth level‖ ≤ errors depth)
    (errors_vanish : Tendsto errors atTop (𝓝 0)) :
    (∀ depth, ‖function - limits depth‖ ≤ errors depth) ∧
      Tendsto limits atTop (𝓝 function) := by
  have bounds : ∀ depth, ‖function - limits depth‖ ≤ errors depth := fun depth =>
    varying_weak_residual_norm_bound functions (approximations depth) (tests depth)
      function (limits depth) (errors depth) (errors_nonnegative depth)
      (norm_convergence depth) (function_pairings depth) (approximation_pairings depth)
      (error_bound depth)
  exact ⟨bounds, tendsto_of_vanishing_norm_error limits function errors bounds errors_vanish⟩

end IGS.Sec31
