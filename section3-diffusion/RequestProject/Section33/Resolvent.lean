import RequestProject.Section33.ExitTime

/-!
# Section 3.3: the continuity step in Proposition "heat-kernel"

Proposition "heat-kernel" of arXiv:2603.13798 first quotes the multiscale Nash
argument of Hambly–Kumagai for ultracontractivity (that part is a black box, and
its bookkeeping is in `Section33.HeatUpper`), and then proves that the resolvent

`U_λ f(x) = E_x[∫_0^∞ e^{-λt} f(W_t) dt]`

maps `L^∞(μ)` into `C(Ξ_M)`.  The argument is: apply the strong Markov property
at the exit time from `B(x₀,r)`, which splits `U_λ f` into

* a **harmonic** part `E_y[e^{-λτ} U_λ f(W_τ)]`, continuous because harmonic
  functions are uniform limits of harmonic splines (Lemma
  `sec31_continuous_harmonics`), and
* an **error** `E_y[∫_0^τ e^{-λt} f(W_t) dt]`, whose absolute value is at most
  `‖f‖_∞ E_y[τ]  ≤ C‖f‖_∞ r^{d_walk}` by Lemma "heat-exit";

so the oscillation of `U_λ f` exceeds that of the harmonic part by at most
`2C‖f‖_∞ r^{d_walk}`, which tends to `0` with `r`.

This file proves the two elementary ingredients: the bound on the error term
(`abs_integral_le_of_le_mul`) and the resulting oscillation estimate
(`osc_le_of_decomposition`, `resolvent_osc_bound`).  The strong Markov property
itself, and the continuity of the harmonic part, are the quoted inputs.
-/

namespace IGS
namespace Sec33

open Real MeasureTheory

/--
**The error term of the strong Markov decomposition.**
If `|F| ≤ M τ` pointwise (almost everywhere) and `E[τ] ≤ T`, then
`|E[F]| ≤ M T`.  Applied with `F = ∫_0^τ e^{-λt}f(W_t)dt` and `M = ‖f‖_∞`, and
with the exit-time bound `E_y[τ] ≤ C r^{d_walk}` of Lemma "heat-exit", this is
the estimate `|E_y[∫_0^τ e^{-λt} f(W_t) dt]| ≤ C‖f‖_∞ r^{d_walk}`.
-/
theorem abs_integral_le_of_le_mul {Omega : Type*} [MeasurableSpace Omega]
    (Pr : Measure Omega) (F tau : Omega → ℝ) {M T : ℝ} (hM : 0 ≤ M)
    (hF : ∀ᵐ om ∂Pr, |F om| ≤ M * tau om)
    (hint : Integrable F Pr) (hinttau : Integrable tau Pr)
    (hT : ∫ om, tau om ∂Pr ≤ T) :
    |∫ om, F om ∂Pr| ≤ M * T := by
  calc |∫ om, F om ∂Pr| ≤ ∫ om, |F om| ∂Pr := abs_integral_le_integral_abs
    _ ≤ ∫ om, M * tau om ∂Pr := integral_mono_ae hint.abs (hinttau.const_mul M) hF
    _ = M * ∫ om, tau om ∂Pr := integral_const_mul _ _
    _ ≤ M * T := mul_le_mul_of_nonneg_left hT hM

/--
**The oscillation estimate.**
If `U = err + h` with `|err| ≤ E`, then the oscillation of `U` exceeds the
oscillation of `h` by at most `2E`.
-/
theorem osc_le_of_decomposition {X : Type*} (U h err : X → ℝ) {E : ℝ}
    (hdecomp : ∀ y, U y = err y + h y) (herr : ∀ y, |err y| ≤ E) (y z : X) :
    |U y - U z| ≤ |h y - h z| + 2 * E := by
  have hy := herr y
  have hz := herr z
  have hrw : U y - U z = (h y - h z) + (err y - err z) := by
    rw [hdecomp y, hdecomp z]; ring
  calc |U y - U z| = |(h y - h z) + (err y - err z)| := by rw [hrw]
    _ ≤ |h y - h z| + |err y - err z| := abs_add_le _ _
    _ ≤ |h y - h z| + 2 * E := by
        have : |err y - err z| ≤ 2 * E := by
          calc |err y - err z| ≤ |err y| + |err z| := abs_sub _ _
            _ ≤ 2 * E := by linarith
        linarith

namespace Params

variable (P : Params)

/--
**The continuity step of Proposition "heat-kernel"**, in the form used by the
paper: with the strong Markov decomposition `U_λ f = err + h` at the exit time
from `B(x₀,r)` and the exit-time bound of Lemma "heat-exit"
(`E_y[τ] ≤ C_exit r^{d_walk}`), the oscillation of `U_λ f` is that of the
harmonic function `h`, up to an error of order `‖f‖_∞ r^{d_walk}`.
-/
theorem resolvent_osc_bound {X : Type*} (U h err : X → ℝ) {Cexit Cf r : ℝ}
    (hdecomp : ∀ y, U y = err y + h y)
    (herr : ∀ y, |err y| ≤ Cf * (Cexit * r ^ P.dwalk)) (y z : X) :
    |U y - U z| ≤ |h y - h z| + 2 * (Cf * Cexit * r ^ P.dwalk) := by
  have h1 := osc_le_of_decomposition U h err hdecomp herr y z
  have hrw : Cf * (Cexit * r ^ P.dwalk) = Cf * Cexit * r ^ P.dwalk := by ring
  rwa [hrw] at h1

end Params

end Sec33
end IGS
