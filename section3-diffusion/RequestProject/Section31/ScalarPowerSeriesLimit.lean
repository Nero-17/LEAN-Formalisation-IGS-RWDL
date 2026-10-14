import RequestProject.Section31.ScalarCoefficientSubsequence
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Normed.Group.Tannery

/-! A pointwise limit of scalar series with one uniform geometric coefficient
bound has a power series locally. A common coefficient subsequence and Tannery's
theorem prove the result. The model consumer must supply the actual exponential
series, its proved uniform bound, and its actual strong-limit convergence.
Analyticity of the limiting function is a conclusion, never a premise.
Candidate source, awaiting whole-file compilation. -/

namespace IGS.Sec31

open Filter Topology

theorem scalar_series_limit_hasFPowerSeriesAt
    (coefficients : ℕ → ℕ → ℝ) (approximations : ℕ → ℝ → ℝ)
    (target : ℝ → ℝ) (center constant rate : ℝ)
    (constantNonnegative : 0 ≤ constant) (ratePositive : 0 < rate)
    (bounded : ∀ index power, |coefficients index power| ≤ constant * rate ^ power)
    (series : ∀ index increment,
      HasSum (fun power => coefficients index power * increment ^ power) (approximations index increment))
    (convergence : ∀ increment, |increment| < rate⁻¹ →
      Tendsto (fun index => approximations index increment) atTop (𝓝 (target (center + increment)))) :
    ∃ limitCoefficients : ℕ → ℝ,
      (∀ power, |limitCoefficients power| ≤ constant * rate ^ power) ∧
      HasFPowerSeriesAt target (FormalMultilinearSeries.ofScalars ℝ limitCoefficients) center := by
  obtain ⟨indices, indicesStrictMono, limitCoefficients, limitBounded, coefficientConvergence⟩ :=
    exists_scalar_coefficient_subsequence coefficients (fun power => constant * rate ^ power) bounded
  have representation (increment : ℝ) (incrementBound : |increment| < rate⁻¹) :
      HasSum (fun power => limitCoefficients power * increment ^ power) (target (center + increment)) := by
    have ratioNonnegative : 0 ≤ rate * |increment| := mul_nonneg ratePositive.le (abs_nonneg _)
    have ratioLessThanOne : rate * |increment| < 1 := by
      have multiplied := mul_lt_mul_of_pos_left incrementBound ratePositive
      simpa only [mul_inv_cancel₀ ratePositive.ne'] using multiplied
    have summableBound : Summable (fun power : ℕ => constant * (rate * |increment|) ^ power) :=
      (summable_geometric_of_lt_one ratioNonnegative ratioLessThanOne).mul_left constant
    have termBound (index power : ℕ) :
        ‖coefficients (indices index) power * increment ^ power‖ ≤
          constant * (rate * |increment|) ^ power := by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      calc
        _ ≤ (constant * rate ^ power) * |increment| ^ power :=
          mul_le_mul_of_nonneg_right (bounded (indices index) power) (pow_nonneg (abs_nonneg _) _)
        _ = _ := by rw [mul_pow]; ring
    have limitSummable : Summable (fun power => limitCoefficients power * increment ^ power) :=
      summableBound.of_norm_bounded (fun power => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
        calc
          _ ≤ (constant * rate ^ power) * |increment| ^ power :=
            mul_le_mul_of_nonneg_right (limitBounded power) (pow_nonneg (abs_nonneg _) _)
          _ = _ := by rw [mul_pow]; ring)
    have sumConvergence := tendsto_tsum_of_dominated_convergence summableBound
      (fun power => (coefficientConvergence power).mul_const (increment ^ power))
      (Eventually.of_forall (fun index power => termBound index power))
    have sumEquality :
        (fun index => ∑' power, coefficients (indices index) power * increment ^ power) =
          (fun index => approximations (indices index) increment) := by
      funext index
      exact (series (indices index) increment).tsum_eq
    rw [sumEquality] at sumConvergence
    have targetEquality := tendsto_nhds_unique sumConvergence
      ((convergence increment incrementBound).comp indicesStrictMono.tendsto_atTop)
    have limitSum := limitSummable.hasSum
    rw [targetEquality] at limitSum
    exact limitSum
  refine ⟨limitCoefficients, limitBounded, ?_⟩
  apply hasFPowerSeriesAt_iff.mpr
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (inv_pos.mpr ratePositive)] with increment member
  have incrementBound : |increment| < rate⁻¹ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using member
  simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm] using
    representation increment incrementBound

theorem scalar_series_pointwise_limit_analyticAt
    (coefficients : ℕ → ℕ → ℝ) (approximations : ℕ → ℝ → ℝ)
    (target : ℝ → ℝ) (center constant rate : ℝ)
    (constantNonnegative : 0 ≤ constant) (ratePositive : 0 < rate)
    (bounded : ∀ index power, |coefficients index power| ≤ constant * rate ^ power)
    (series : ∀ index increment,
      HasSum (fun power => coefficients index power * increment ^ power) (approximations index increment))
    (convergence : ∀ increment, |increment| < rate⁻¹ →
      Tendsto (fun index => approximations index increment) atTop (𝓝 (target (center + increment)))) :
    AnalyticAt ℝ target center := by
  obtain ⟨_, _, representation⟩ := scalar_series_limit_hasFPowerSeriesAt coefficients approximations target
    center constant rate constantNonnegative ratePositive bounded series convergence
  exact representation.analyticAt

end IGS.Sec31

#print axioms IGS.Sec31.scalar_series_limit_hasFPowerSeriesAt
#print axioms IGS.Sec31.scalar_series_pointwise_limit_analyticAt
