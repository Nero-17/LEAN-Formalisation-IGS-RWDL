import Mathlib

/-!
# Section 3, step 1: on-diagonal heat-kernel exponents ⟹ local spectral dimension

This file formalises the purely analytic step behind Theorem "diffusion-spectral"
of *Iterated Graph Systems (I): random walks and diffusion limits*
(arXiv:2603.13798), namely the passage

  two-sided on-diagonal bounds for `p_t(x,x)`  ⟹  the limit
  `d_s(x) = -2 lim_{t↓0} log p_t(x,x) / log t` exists and equals twice the exponent.

Everything about the diffusion `W`, its Dirichlet form and its heat kernel is left
outside: the heat kernel enters only as an abstract function `p : ℝ → ℝ`
(think `t ↦ p_t(x,x)` for a fixed `x`) subject to the bounds proved in the paper.
The point of the file is that the log-correction appearing at
`μ`-almost every infinite-born point (`|log t|^{-(1+1/(d_deg-1))-ε}`) does *not*
change the value of the local spectral dimension; this is what makes both cases of
the paper's spectral-dimension theorem follow from one lemma.
-/

namespace IGS

open Filter Topology

/-- `log |L| / L → 0` as `L → -∞`. -/
lemma tendsto_log_abs_div_atBot :
    Tendsto (fun L : ℝ => Real.log |L| / L) atBot (𝓝 0) := by
  have h1 : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Tendsto (fun L : ℝ => -(Real.log (-L) / (-L))) atBot (𝓝 0) := by
    have := (h1.comp tendsto_neg_atBot_atTop).neg
    simpa using this
  refine h2.congr' ?_
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with L hL
  rw [abs_of_neg hL]
  field_simp

/-- `1 / log t → 0` as `t ↓ 0`. -/
lemma tendsto_inv_log_nhdsGT_zero :
    Tendsto (fun t : ℝ => (Real.log t)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero

/-- `log |log t| / log t → 0` as `t ↓ 0`. -/
lemma tendsto_log_abs_log_div_log_nhdsGT_zero :
    Tendsto (fun t : ℝ => Real.log |Real.log t| / Real.log t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  tendsto_log_abs_div_atBot.comp Real.tendsto_log_nhdsGT_zero

/--
**Local spectral dimension from log-corrected on-diagonal bounds.**

If, for all small `t > 0`,
`c * |log t|^(-b) * t^(-a) ≤ p t ≤ C * t^(-a)`,
then `-2 * log (p t) / log t → 2 * a` as `t ↓ 0`.

With `b = 0` this is the finite-born case (`x ∈ 𝒱`, exponent
`a = d_box (1 - 1/d_deg)/d_walk`); with `b = (1 + 1/(d_deg - 1)) + ε` it is the
almost-every infinite-born case (`a = d_box/d_walk`) of the paper.
-/
theorem tendsto_spectral_dimension_of_bounds
    (p : ℝ → ℝ) (a b c C t₀ : ℝ) (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 < t₀)
    (hlow : ∀ t ∈ Set.Ioo (0 : ℝ) t₀, c * |Real.log t| ^ (-b) * t ^ (-a) ≤ p t)
    (hup : ∀ t ∈ Set.Ioo (0 : ℝ) t₀, p t ≤ C * t ^ (-a)) :
    Tendsto (fun t => -2 * Real.log (p t) / Real.log t) (𝓝[>] (0 : ℝ)) (𝓝 (2 * a)) := by
  -- the two comparison functions
  set G : ℝ → ℝ := fun t =>
    -2 * Real.log c / Real.log t + 2 * b * (Real.log |Real.log t| / Real.log t) + 2 * a with hG
  set H : ℝ → ℝ := fun t => -2 * Real.log C / Real.log t + 2 * a with hH
  have hinv := tendsto_inv_log_nhdsGT_zero
  have hll := tendsto_log_abs_log_div_log_nhdsGT_zero
  have hGlim : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 (2 * a)) := by
    have : Tendsto (fun t : ℝ =>
        -2 * Real.log c * (Real.log t)⁻¹ + 2 * b * (Real.log |Real.log t| / Real.log t) + 2 * a)
        (𝓝[>] (0 : ℝ)) (𝓝 (-2 * Real.log c * 0 + 2 * b * 0 + 2 * a)) :=
      ((hinv.const_mul _).add ((hll.const_mul _))).add tendsto_const_nhds
    simpa [hG, div_eq_mul_inv] using this
  have hHlim : Tendsto H (𝓝[>] (0 : ℝ)) (𝓝 (2 * a)) := by
    have : Tendsto (fun t : ℝ => -2 * Real.log C * (Real.log t)⁻¹ + 2 * a)
        (𝓝[>] (0 : ℝ)) (𝓝 (-2 * Real.log C * 0 + 2 * a)) :=
      (hinv.const_mul _).add tendsto_const_nhds
    simpa [hH, div_eq_mul_inv] using this
  -- the squeeze, valid for `0 < t < min t₀ (exp (-1))`
  have key : ∀ᶠ t in 𝓝[>] (0 : ℝ), G t ≤ -2 * Real.log (p t) / Real.log t ∧
      -2 * Real.log (p t) / Real.log t ≤ H t := by
    have hmem : Set.Ioo (0 : ℝ) (min t₀ (Real.exp (-1))) ∈ 𝓝[>] (0 : ℝ) :=
      Ioo_mem_nhdsGT (by positivity)
    filter_upwards [hmem] with t ht
    obtain ⟨ht0, htlt⟩ := ht
    have htt₀ : t < t₀ := lt_of_lt_of_le htlt (min_le_left _ _)
    have hte : t < Real.exp (-1) := lt_of_lt_of_le htlt (min_le_right _ _)
    have hLneg : Real.log t < -1 := by
      have := Real.log_lt_log ht0 hte
      simpa using this
    have hL : Real.log t < 0 := by linarith
    have hLne : Real.log t ≠ 0 := ne_of_lt hL
    -- monotone rescaling by the negative number `log t`
    have mono : ∀ x y : ℝ, x ≤ y → -2 * x / Real.log t ≤ -2 * y / Real.log t := by
      intro x y hxy
      have hcoef : 0 ≤ -2 / Real.log t := le_of_lt (div_pos_of_neg_of_neg (by norm_num) hL)
      have h1 : -2 * x / Real.log t = (-2 / Real.log t) * x := by ring
      have h2 : -2 * y / Real.log t = (-2 / Real.log t) * y := by ring
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_left hxy hcoef
    -- positivity of `p t`
    have habs : (0 : ℝ) < |Real.log t| := abs_pos.mpr hLne
    have hlowt := hlow t ⟨ht0, htt₀⟩
    have hupt := hup t ⟨ht0, htt₀⟩
    have hppos : 0 < p t :=
      lt_of_lt_of_le (by positivity) hlowt
    -- logarithms of the two bounds
    have hlog_low : Real.log c - b * Real.log |Real.log t| - a * Real.log t
        ≤ Real.log (p t) := by
      have := Real.log_le_log (by positivity) hlowt
      calc Real.log c - b * Real.log |Real.log t| - a * Real.log t
          = Real.log (c * |Real.log t| ^ (-b) * t ^ (-a)) := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
              (by positivity), Real.log_rpow habs, Real.log_rpow ht0]
            ring
        _ ≤ Real.log (p t) := this
    have hlog_up : Real.log (p t) ≤ Real.log C - a * Real.log t := by
      have := Real.log_le_log hppos hupt
      calc Real.log (p t) ≤ Real.log (C * t ^ (-a)) := this
        _ = Real.log C - a * Real.log t := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow ht0]; ring
    constructor
    · have := mono _ _ hlog_low
      have hrw : -2 * (Real.log c - b * Real.log |Real.log t| - a * Real.log t)
          / Real.log t = G t := by
        rw [hG]
        field_simp
        ring
      rwa [hrw] at this
    · have := mono _ _ hlog_up
      have hrw : -2 * (Real.log C - a * Real.log t) / Real.log t = H t := by
        rw [hH]
        field_simp
        ring
      rwa [hrw] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hGlim hHlim
    (key.mono fun _ h => h.1) (key.mono fun _ h => h.2)

/--
The finite-born case: plain two-sided bounds `c t^(-a) ≤ p t ≤ C t^(-a)` give
local spectral dimension `2a`.
-/
theorem tendsto_spectral_dimension_of_pure_bounds
    (p : ℝ → ℝ) (a c C t₀ : ℝ) (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 < t₀)
    (hlow : ∀ t ∈ Set.Ioo (0 : ℝ) t₀, c * t ^ (-a) ≤ p t)
    (hup : ∀ t ∈ Set.Ioo (0 : ℝ) t₀, p t ≤ C * t ^ (-a)) :
    Tendsto (fun t => -2 * Real.log (p t) / Real.log t) (𝓝[>] (0 : ℝ)) (𝓝 (2 * a)) := by
  refine tendsto_spectral_dimension_of_bounds p a 0 c C t₀ hc hC ht₀ ?_ hup
  intro t ht
  simpa using hlow t ht

end IGS
