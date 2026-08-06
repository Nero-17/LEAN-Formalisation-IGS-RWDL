import Mathlib

/-!
# §3.1, step 6: exit times
(Lemma `sec31_one_step_stay` and Theorem `sec31_discrete_eld_tightness`)

Reference: arXiv:2603.13798, §3.1.

## Lemma `sec31_one_step_stay`

Section 2 provides two-sided bounds on the mean exit time from a ball,
`c_exit a_n δ^{d_w} ≤ E_x[τ_n(x,δ)] ≤ C_exit a_n δ^{d_w}`, the upper bound being
uniform over all starting points inside the ball.  The paper then applies the
strong Markov property at time `t := ½ c_exit a_n δ^{d_w}`.  What this gives is
the inequality

  `E_x[τ] ≤ t + (sup_y E_y[τ]) · P_x(τ > t)`,

and combined with the lower bound it forces `P_x(τ ≥ t) ≥ c_exit /(2 C_exit)`,
which is the assertion with `p_stay := c_exit/(2C_exit)` and
`c_stay := c_exit/2`.  The arithmetic step is `stay_probability_lower`, and the
elementary half of the strong-Markov inequality, `E[τ] ≤ t + E[(τ-t)^+]`, is
proved in `integral_le_add_pos_part` (the remaining half,
`E[(τ-t)^+] ≤ sup_y E_y[τ] · P(τ > t)`, is exactly the strong Markov property
and stays a hypothesis).

## Theorem `sec31_discrete_eld_tightness`

The chaining proof needs a radial increment size `δ` such that

* the number of radial increments `K = r/δ` equals `(r^{d_w}/t)^{1/(d_w-1)}`,
  which is precisely the exponent appearing in the stated tail bound
  `C exp[-c (r^{d_w}/t)^{1/(d_w-1)}]`;
* the total time consumed by `K` increments, `K · δ^{d_w} = r δ^{d_w-1}`, equals
  the time budget `t`, so that exiting `B(x,r)` before `a_n t` really does force
  an abnormally small number of long increments.

Both identities hold for the paper's choice `δ = (t/r)^{1/(d_w-1)}` and are
proved in `radial_step_time` and `radial_step_count`.  They require `d_w > 1`,
which is where the exponent `1/(d_w - 1)` comes from.  Azuma–Hoeffding and
Aldous' tightness criterion, which the paper cites, are not formalised here.
-/

namespace IGS.Sec31

open MeasureTheory Real

/--
**Unrolling the cell-exit recursion of Lemma `sec31_one_step_stay`.**

The uniform mean hitting time `T_s` of the two terminals of an `s`-step
substituted copy satisfies `T_{s+1} ≤ T_s + A q^{s}` with `q = ρ(M)ρ(Ψ) > 1`
(one pass to the level-one skeleton, then a bounded expected number of skeleton
jumps each of expected length `≲ q^{s}`).  Unrolling gives
`T_s ≤ (T_0 + A/(q-1)) q^s`, which is the claim `T_s ≤ C_T (ρ(M)ρ(Ψ))^s`.
-/
theorem geometric_recursion_bound (T : ℕ → ℝ) (q A : ℝ) (hq : 1 < q) (hA : 0 ≤ A)
    (h0 : 0 ≤ T 0) (hrec : ∀ s : ℕ, T (s + 1) ≤ T s + A * q ^ s) :
    ∀ s : ℕ, T s ≤ (T 0 + A / (q - 1)) * q ^ s := by
  have hq1 : 0 < q - 1 := by linarith
  have hqpos : 0 < q := by linarith
  set C : ℝ := T 0 + A / (q - 1) with hC
  have hCA : C + A ≤ C * q := by
    have hdiv : A / (q - 1) * (q - 1) = A := div_mul_cancel₀ A (ne_of_gt hq1)
    have : C * q - C = T 0 * (q - 1) + A := by
      rw [hC]; nlinarith [hdiv]
    nlinarith [mul_nonneg h0 (le_of_lt hq1)]
  intro s
  induction s with
  | zero => simp [hC]; positivity
  | succ s ih =>
      have hqs : (0:ℝ) < q ^ s := pow_pos hqpos s
      calc T (s + 1) ≤ T s + A * q ^ s := hrec s
        _ ≤ C * q ^ s + A * q ^ s := by linarith
        _ = (C + A) * q ^ s := by ring
        _ ≤ (C * q) * q ^ s := mul_le_mul_of_nonneg_right hCA (le_of_lt hqs)
        _ = C * q ^ (s + 1) := by ring

/--
**Arithmetic core of Lemma `sec31_one_step_stay`.**
`A = a_n δ^{d_w}`.  From `c A ≤ E[τ]` and `E[τ] ≤ cA/2 + C A p` (the strong
Markov estimate at time `t = cA/2`, with `p = P(τ ≥ t)`) one gets
`p ≥ c/(2C)`.
-/
theorem stay_probability_lower (A c C p Etau : ℝ) (hA : 0 < A) (hC : 0 < C)
    (hlow : c * A ≤ Etau) (hup : Etau ≤ c * A / 2 + C * A * p) : c / (2 * C) ≤ p := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/--
**The elementary half of the strong-Markov estimate.**
For an integrable `τ ≥ 0` and any level `t`, `E[τ] ≤ t + E[(τ - t)^+]`.
-/
theorem integral_le_add_pos_part {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (tau : Ω → ℝ) (htau : Integrable tau P) (t : ℝ) :
    ∫ ω, tau ω ∂P ≤ t + ∫ ω, max (tau ω - t) 0 ∂P := by
  have hsub : Integrable (fun ω => tau ω - t) P := htau.sub (integrable_const t)
  have hint : Integrable (fun ω => max (tau ω - t) 0) P := hsub.pos_part
  have h2 : Integrable (fun ω => t + max (tau ω - t) 0) P := (integrable_const t).add hint
  have hmono := integral_mono htau h2 (fun ω => by
    rcases le_or_gt (tau ω) t with h | h
    · have hm : (0 : ℝ) ≤ max (tau ω - t) 0 := le_max_right _ _
      simp only
      linarith
    · have hm : max (tau ω - t) 0 = tau ω - t := max_eq_left (by linarith)
      simp only [hm]
      linarith)
  rw [integral_add (integrable_const t) hint] at hmono
  simpa using hmono

/--
**Time budget of the radial chaining (Theorem `sec31_discrete_eld_tightness`).**
With `δ = (t/r)^{1/(d_w-1)}`, the `r/δ` radial increments of size `δ` consume
exactly the time `t`: `r · δ^{d_w - 1} = t`.
-/
theorem radial_step_time (r t dw : ℝ) (hr : 0 < r) (ht : 0 < t) (hdw : 1 < dw) :
    r * ((t / r) ^ (1 / (dw - 1)) : ℝ) ^ (dw - 1) = t := by
  have h1 : (0 : ℝ) < dw - 1 := by linarith
  have hq : (0 : ℝ) ≤ t / r := (div_pos ht hr).le
  rw [← Real.rpow_mul hq, one_div, inv_mul_cancel₀ (ne_of_gt h1), Real.rpow_one]
  field_simp

/--
**Number of radial increments (Theorem `sec31_discrete_eld_tightness`).**
With `δ = (t/r)^{1/(d_w-1)}` the number of increments is
`r/δ = (r^{d_w}/t)^{1/(d_w-1)}`, i.e. exactly the quantity in the exponent of
the stated tail estimate.
-/
theorem radial_step_count (r t dw : ℝ) (hr : 0 < r) (ht : 0 < t) (hdw : 1 < dw) :
    r / ((t / r) ^ (1 / (dw - 1)) : ℝ) = (r ^ dw / t) ^ (1 / (dw - 1)) := by
  set e := 1 / (dw - 1) with he
  have h1 : (0 : ℝ) < dw - 1 := by linarith
  have htr : (0 : ℝ) ≤ t / r := (div_pos ht hr).le
  have hrt : (0 : ℝ) ≤ r / t := (div_pos hr ht).le
  have hinv : ((t / r) ^ e : ℝ)⁻¹ = (r / t) ^ e := by rw [← Real.inv_rpow htr, inv_div]
  have hr1 : ((r ^ (dw - 1) : ℝ)) ^ e = r := by
    rw [← Real.rpow_mul hr.le, he, mul_one_div, div_self (ne_of_gt h1), Real.rpow_one]
  have hpow : (r ^ (dw - 1) : ℝ) * r = r ^ dw := by
    nth_rewrite 2 [← Real.rpow_one r]
    rw [← Real.rpow_add hr]
    ring_nf
  calc r / ((t / r) ^ e : ℝ) = r * ((t / r) ^ e)⁻¹ := by rw [div_eq_mul_inv]
    _ = ((r ^ (dw - 1) : ℝ)) ^ e * (r / t) ^ e := by rw [hinv, hr1]
    _ = ((r ^ (dw - 1) : ℝ) * (r / t)) ^ e := by rw [← Real.mul_rpow (by positivity) hrt]
    _ = (r ^ dw / t) ^ e := by
        congr 1
        rw [eq_div_iff (ne_of_gt ht)]
        field_simp
        linarith [hpow]

end IGS.Sec31
