import RequestProject.Section33.BrownianHeat

/-!
# Example 3.30: the two-coloured EIGS of Figure 3

From Example 2.12 of the paper the scaling data of the two-coloured EIGS of
Figure 3 are

`ρ(M) = 3 + √6`,  `ρ(N) = 2`,  `ρ_min(D) = 2`,

and `ρ(Ψ)` is the unique root in `(1, ∞)` of `27λ⁴ + 6λ³ - 50λ² + 6λ + 6 = 0`
(`psiPoly`), numerically `ρ(Ψ) ≈ 1.1061`.  Hence

`dim_B(Ξ) = dim_D(Ξ) = log(3+√6)/log 2 ≈ 2.4461`,
`dim_R(Ξ) = log ρ(Ψ)/log 2 ≈ 0.1455`,
`dim_W(Ξ) = log((3+√6)ρ(Ψ))/log 2`.

This file proves:

* `psiPoly_strictMonoOn`, `exists_unique_rPsi`, `rPsi_mem_Ioo` — the Perron
  root `ρ(Ψ)` exists, is unique in `(1,∞)`, and satisfies
  `1.1061 < ρ(Ψ) < 1.1062`;
* `twoColour_dbox_eq_ddeg`, `twoColour_dR_pos` — the dimension identities of
  Example 2.12 in the form needed here (in particular the example is in the
  Brownian regime `dim_R > 0`, so Corollary 3.27 and Theorem 3.28 apply);
* `twoColour_spectral_finite_eq`, `twoColour_spectral_infinite_eq` — the two
  closed formulas of Example 3.30,
  `2 log((3+√6)/2)/log((3+√6)ρ(Ψ))` and `2 log(3+√6)/log((3+√6)ρ(Ψ))`;
* `twoColour_spectral_finite_numeric`, `twoColour_spectral_infinite_numeric` —
  rigorous numerical enclosures `1.1159 < · < 1.1161` and `1.8876 < · < 1.8878`,
  confirming the values `≈ 1.1160` and `≈ 1.8877` quoted in the paper;
* `twoColour_spectral_finite`, `twoColour_spectral_infinite` — the resulting
  statements of Theorem 3.28 for this example: the diffusion and Brownian
  spectral dimensions coincide and are given by those two numbers.

The numerical bounds use only `Real.exp_one_gt_d9`, `Real.exp_one_lt_d9`,
`Real.log_two_gt_d9`, `Real.log_two_lt_d9` and the elementary inequalities
`1 - 1/x ≤ log x ≤ x - 1`; nothing is assumed.
-/

namespace IGS
namespace Sec33

open Real Filter Topology

/-! ## Elementary logarithm bounds -/

/-- `1 - 1/x ≤ log x` for `x > 0`. -/
lemma one_sub_inv_le_log {x : ℝ} (hx : 0 < x) : 1 - 1 / x ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (x := 1 / x) (by positivity)
  rw [one_div, Real.log_inv] at h
  rw [one_div]
  linarith

/-- `log a ≤ a/e`, the case of equality being `a = e`. -/
lemma log_le_div_exp_one {a : ℝ} (ha : 0 < a) : Real.log a ≤ a / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (x := a / Real.exp 1) (by positivity)
  rw [Real.log_div (ne_of_gt ha) (Real.exp_ne_zero 1), Real.log_exp] at h
  linarith

/-- `2 - e/a ≤ log a`, the companion lower bound. -/
lemma two_sub_exp_div_le_log {a : ℝ} (ha : 0 < a) : 2 - Real.exp 1 / a ≤ Real.log a := by
  have h := one_sub_inv_le_log (x := a / Real.exp 1) (by positivity)
  rw [Real.log_div (ne_of_gt ha) (Real.exp_ne_zero 1), Real.log_exp] at h
  have he : 1 / (a / Real.exp 1) = Real.exp 1 / a := by field_simp
  rw [he] at h
  linarith

/-! ## The Perron root `ρ(Ψ)` -/

/-- The polynomial `27λ⁴ + 6λ³ - 50λ² + 6λ + 6` of Example 2.12, whose unique
root in `(1,∞)` is `ρ(Ψ)`. -/
noncomputable def psiPoly (l : ℝ) : ℝ := 27 * l ^ 4 + 6 * l ^ 3 - 50 * l ^ 2 + 6 * l + 6

lemma psiPoly_continuous : Continuous psiPoly := by
  unfold psiPoly; fun_prop

/-- `psiPoly` is strictly increasing on `[1,∞)`; this is what makes the root
`ρ(Ψ)` unique there. -/
lemma psiPoly_strictMonoOn : StrictMonoOn psiPoly (Set.Ici (1:ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : (0:ℝ) < y := lt_of_lt_of_le zero_lt_one hy
  have h1 : x ^ 3 ≥ x := by
    nlinarith [mul_nonneg (mul_nonneg hx0.le (sub_nonneg.2 hx)) (by linarith : (0:ℝ) ≤ x + 1)]
  have h2 : x ^ 2 * y ≥ y := by
    nlinarith [mul_nonneg (sub_nonneg.2 hx) (by linarith : (0:ℝ) ≤ x + 1)]
  have h3 : x * y ^ 2 ≥ x := by
    nlinarith [mul_nonneg (sub_nonneg.2 hy) (by linarith : (0:ℝ) ≤ y + 1)]
  have h4 : y ^ 3 ≥ y := by
    nlinarith [mul_nonneg (mul_nonneg hy0.le (sub_nonneg.2 hy)) (by linarith : (0:ℝ) ≤ y + 1)]
  have key : 0 < 27 * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3)
      + 6 * (x ^ 2 + x * y + y ^ 2) - 50 * (x + y) + 6 := by nlinarith
  have hfac : psiPoly y - psiPoly x = (y - x) *
      (27 * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3)
        + 6 * (x ^ 2 + x * y + y ^ 2) - 50 * (x + y) + 6) := by
    simp only [psiPoly]; ring
  nlinarith [mul_pos (sub_pos.2 hxy) key]

/-- **Existence and uniqueness of `ρ(Ψ)`**: `psiPoly` has exactly one root in
`(1,∞)`, and it lies in `(1.1061, 1.1062)`. -/
theorem exists_unique_rPsi : ∃! r : ℝ, 1 < r ∧ psiPoly r = 0 := by
  have hc : ContinuousOn psiPoly (Set.Icc (1.1061:ℝ) 1.1062) := psiPoly_continuous.continuousOn
  have h1 : psiPoly 1.1061 < 0 := by norm_num [psiPoly]
  have h2 : (0:ℝ) < psiPoly 1.1062 := by norm_num [psiPoly]
  obtain ⟨r, hr, hr0⟩ :=
    intermediate_value_Ioo (by norm_num : (1.1061:ℝ) ≤ 1.1062) hc ⟨h1, h2⟩
  refine ⟨r, ⟨by linarith [hr.1], hr0⟩, ?_⟩
  rintro s ⟨hs1, hs0⟩
  by_contra hne
  have hr1 : (1:ℝ) ≤ r := by linarith [hr.1]
  rcases lt_or_gt_of_ne hne with h | h
  · have := psiPoly_strictMonoOn (Set.mem_Ici.2 hs1.le) (Set.mem_Ici.2 hr1) h
    rw [hs0, hr0] at this
    exact lt_irrefl 0 this
  · have := psiPoly_strictMonoOn (Set.mem_Ici.2 hr1) (Set.mem_Ici.2 hs1.le) h
    rw [hs0, hr0] at this
    exact lt_irrefl 0 this

/-- Any root of `psiPoly` in `(1,∞)` — that is, `ρ(Ψ)` — satisfies
`1.1061 < ρ(Ψ) < 1.1062`, so `ρ(Ψ) ≈ 1.1061` as stated in Example 2.12. -/
theorem rPsi_mem_Ioo {r : ℝ} (h1 : 1 < r) (h0 : psiPoly r = 0) :
    1.1061 < r ∧ r < 1.1062 := by
  have hlow : psiPoly 1.1061 < 0 := by norm_num [psiPoly]
  have hhigh : (0:ℝ) < psiPoly 1.1062 := by norm_num [psiPoly]
  constructor
  · by_contra hcon
    push_neg at hcon
    rcases eq_or_lt_of_le hcon with heq | hlt
    · rw [← heq, h0] at hlow; exact lt_irrefl 0 hlow
    · have := psiPoly_strictMonoOn (Set.mem_Ici.2 h1.le)
        (Set.mem_Ici.2 (by norm_num : (1:ℝ) ≤ 1.1061)) hlt
      rw [h0] at this
      linarith
  · by_contra hcon
    push_neg at hcon
    rcases eq_or_lt_of_le hcon with heq | hlt
    · rw [heq, h0] at hhigh; exact lt_irrefl 0 hhigh
    · have := psiPoly_strictMonoOn (Set.mem_Ici.2 (by norm_num : (1:ℝ) ≤ 1.1062))
        (Set.mem_Ici.2 h1.le) hlt
      rw [h0] at this
      linarith

/-- The polynomial `3t⁴ + 10t³ + 4t² - 8t - 3` of Example 2.12, whose unique
positive root `t ≈ 0.8200` is the ratio of the two coordinates of the Perron
eigenvector of `Ψ`. -/
noncomputable def tPoly (t : ℝ) : ℝ := 3 * t ^ 4 + 10 * t ^ 3 + 4 * t ^ 2 - 8 * t - 3

/--
**The elimination step of Example 2.12.**  If `t > 0` solves
`3t⁴+10t³+4t²-8t-3 = 0`, then `ρ(Ψ) = (t+2)(t+1)/(2t+3)` solves
`27λ⁴+6λ³-50λ²+6λ+6 = 0`.  Indeed

`(2t+3)⁴ · psiPoly((t+2)(t+1)/(2t+3)) = tPoly(t) · (9t⁴+82t³+248t²+310t+138)`,

which is the identity used by the `linear_combination` below; so the two
descriptions of `ρ(Ψ)` in Example 2.12 agree.
-/
theorem psiPoly_of_tPoly {t : ℝ} (ht : 0 < t) (hg : tPoly t = 0) :
    psiPoly ((t + 2) * (t + 1) / (2 * t + 3)) = 0 := by
  have hq : (2 * t + 3) ≠ 0 := by positivity
  unfold psiPoly
  unfold tPoly at hg
  field_simp
  linear_combination (9 * t ^ 4 + 82 * t ^ 3 + 248 * t ^ 2 + 310 * t + 138) * hg

/-- Consequently `(t+2)(t+1)/(2t+3)` *is* the Perron root `ρ(Ψ)`, as soon as it
exceeds `1`. -/
theorem rPsi_eq_of_tPoly {t r : ℝ} (ht : 0 < t) (hg : tPoly t = 0)
    (hlam : 1 < (t + 2) * (t + 1) / (2 * t + 3)) (hr1 : 1 < r) (hr0 : psiPoly r = 0) :
    (t + 2) * (t + 1) / (2 * t + 3) = r := by
  obtain ⟨s, -, huniq⟩ := exists_unique_rPsi
  rw [huniq _ ⟨hlam, psiPoly_of_tPoly ht hg⟩, huniq _ ⟨hr1, hr0⟩]

/-! ## The parameters of the two-coloured EIGS -/

lemma sqrt6_lb : (2.4494897 : ℝ) < Real.sqrt 6 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6), Real.sqrt_nonneg 6]

lemma sqrt6_ub : Real.sqrt 6 < 2.4494898 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6), Real.sqrt_nonneg 6]

/-- The scaling parameters of the two-coloured EIGS of Figure 3:
`ρ(M) = 3+√6`, `ρ(N) = 2`, `ρ_min(D) = 2` and the Perron root `ρ(Ψ) > 1`. -/
noncomputable def twoColour (rPsi : ℝ) (h : 1 < rPsi) : Params where
  rM := 3 + Real.sqrt 6
  rN := 2
  rPsi := rPsi
  rD := 2
  hrD := by norm_num
  hrN := by norm_num
  hrNM := by nlinarith [Real.sqrt_nonneg 6]
  hrPsi := by linarith
  hrMPsi := by nlinarith [Real.sqrt_nonneg 6]

variable {r : ℝ}

lemma twoColour_rM (h : 1 < r) : (twoColour r h).rM = 3 + Real.sqrt 6 := rfl

lemma twoColour_dbox (h : 1 < r) :
    (twoColour r h).dbox = Real.log (3 + Real.sqrt 6) / Real.log 2 := rfl

lemma twoColour_ddeg (h : 1 < r) :
    (twoColour r h).ddeg = Real.log (3 + Real.sqrt 6) / Real.log 2 := rfl

/-- For this EIGS the box and degree dimensions coincide (`≈ 2.4461`), because
`ρ(N) = ρ_min(D) = 2`. -/
lemma twoColour_dbox_eq_ddeg (h : 1 < r) : (twoColour r h).dbox = (twoColour r h).ddeg := rfl

lemma twoColour_dR (h : 1 < r) : (twoColour r h).dR = Real.log r / Real.log 2 := rfl

lemma twoColour_dwalk (h : 1 < r) :
    (twoColour r h).dwalk = Real.log ((3 + Real.sqrt 6) * r) / Real.log 2 := rfl

/-- The two-coloured EIGS is in the Brownian regime `dim_R(Ξ) > 0`, so
Corollary 3.27 and Theorem 3.28 apply to it. -/
lemma twoColour_dR_pos (h : 1 < r) : 0 < (twoColour r h).dR :=
  (twoColour r h).dR_pos_iff_one_lt_rPsi.2 h

/-! ## The two closed formulas of Example 3.30 -/

private lemma log_rM_split : Real.log (3 + Real.sqrt 6)
    = Real.log 2 + Real.log ((3 + Real.sqrt 6) / 2) := by
  rw [Real.log_div (by nlinarith [Real.sqrt_nonneg 6]) (by norm_num)]
  ring

/-- **Example 3.30, finite-born value.**
`2 dim_B(1 - 1/dim_D)/dim_W = 2 log((3+√6)/2)/log((3+√6)ρ(Ψ))`. -/
theorem twoColour_spectral_finite_eq (h : 1 < r) :
    2 * ((twoColour r h).dbox * (1 - 1 / (twoColour r h).ddeg) / (twoColour r h).dwalk)
      = 2 * Real.log ((3 + Real.sqrt 6) / 2) / Real.log ((3 + Real.sqrt 6) * r) := by
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hM : (0:ℝ) < 3 + Real.sqrt 6 := by nlinarith [Real.sqrt_nonneg 6]
  have hprod : (1:ℝ) < (3 + Real.sqrt 6) * r := by nlinarith [Real.sqrt_nonneg 6]
  have hden : Real.log ((3 + Real.sqrt 6) * r) ≠ 0 := ne_of_gt (Real.log_pos hprod)
  have halpha : (twoColour r h).dbox * (1 - 1 / (twoColour r h).ddeg)
      = Real.log ((3 + Real.sqrt 6) / 2) / Real.log 2 := by
    have := (twoColour r h).alphaFin_eq
    unfold Params.alphaFin at this
    rw [this]
    show (Real.log (3 + Real.sqrt 6) - Real.log 2) / Real.log 2
      = Real.log ((3 + Real.sqrt 6) / 2) / Real.log 2
    rw [log_rM_split]
    ring_nf
  rw [halpha, twoColour_dwalk h]
  field_simp

/-- **Example 3.30, infinite-born value.**
`2 dim_B/dim_W = 2 log(3+√6)/log((3+√6)ρ(Ψ))`. -/
theorem twoColour_spectral_infinite_eq (h : 1 < r) :
    2 * ((twoColour r h).dbox / (twoColour r h).dwalk)
      = 2 * Real.log (3 + Real.sqrt 6) / Real.log ((3 + Real.sqrt 6) * r) := by
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hprod : (1:ℝ) < (3 + Real.sqrt 6) * r := by nlinarith [Real.sqrt_nonneg 6]
  have hden : Real.log ((3 + Real.sqrt 6) * r) ≠ 0 := ne_of_gt (Real.log_pos hprod)
  rw [twoColour_dbox h, twoColour_dwalk h]
  field_simp

/-! ## Rigorous numerical enclosures -/

private lemma halfM_pos : (0:ℝ) < (3 + Real.sqrt 6) / 2 := by
  nlinarith [Real.sqrt_nonneg 6]

/-- `log((3+√6)/2) < 1.0023777`. -/
lemma log_halfM_lt : Real.log ((3 + Real.sqrt 6) / 2) < 1.0023777 := by
  have h := log_le_div_exp_one halfM_pos
  have he : (2.7182818283:ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have ha : (3 + Real.sqrt 6) / 2 < 2.7247449 := by linarith [sqrt6_ub]
  have hdiv : (3 + Real.sqrt 6) / 2 / Real.exp 1 < 1.0023777 := by
    rw [div_lt_iff₀ (Real.exp_pos 1)]
    nlinarith
  linarith

/-- `1.0023719 < log((3+√6)/2)`. -/
lemma lt_log_halfM : (1.0023719:ℝ) < Real.log ((3 + Real.sqrt 6) / 2) := by
  have h := two_sub_exp_div_le_log halfM_pos
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have ha : (2.72474485:ℝ) < (3 + Real.sqrt 6) / 2 := by linarith [sqrt6_lb]
  have hdiv : Real.exp 1 / ((3 + Real.sqrt 6) / 2) < 0.9976281 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- Numerical enclosure of `log ρ(Ψ)`, obtained from `1.1061 < ρ(Ψ) < 1.1062`
through `log ρ(Ψ) = (log 2 + log(ρ(Ψ)⁷/2))/7`, the seventh power bringing
`ρ(Ψ)⁷/2` close to `1` where the elementary bounds are sharp. -/
lemma log_rPsi_bounds (hlo : (1.1061:ℝ) < r) (hhi : r < 1.1062) :
    (0.1008287:ℝ) < Real.log r ∧ Real.log r < 0.1009436 := by
  have hr0 : (0:ℝ) < r := by linarith
  have hw0 : (0:ℝ) < r ^ 7 / 2 := by positivity
  have hlog7 : Real.log (r ^ 7) = 7 * Real.log r := by
    rw [Real.log_pow]; norm_num
  have hsplit : Real.log (r ^ 7) = Real.log 2 + Real.log (r ^ 7 / 2) := by
    rw [Real.log_div (by positivity) (by norm_num)]
    ring
  have hpl : (1.1061:ℝ) ^ 7 < r ^ 7 := by gcongr
  have hpu : r ^ 7 < (1.1062:ℝ) ^ 7 := by gcongr
  norm_num at hpl hpu
  have hup : Real.log (r ^ 7 / 2) < 0.0134576 := by
    have h := Real.log_le_sub_one_of_pos hw0
    nlinarith
  have hlow : (0.0126542:ℝ) < Real.log (r ^ 7 / 2) := by
    have h := one_sub_inv_le_log hw0
    have hinv : 1 / (r ^ 7 / 2) < 0.9873458 := by
      rw [div_lt_iff₀ hw0]; nlinarith
    linarith
  have hl2l : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2u : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  constructor <;> nlinarith [hlog7, hsplit]

/-- Numerical enclosure of the walk-dimension denominator
`log((3+√6)ρ(Ψ)) = log 2 + log((3+√6)/2) + log ρ(Ψ)`. -/
lemma log_denom_bounds (h1 : 1 < r) (h0 : psiPoly r = 0) :
    (1.7963477:ℝ) < Real.log ((3 + Real.sqrt 6) * r) ∧
      Real.log ((3 + Real.sqrt 6) * r) < 1.7964685 := by
  obtain ⟨hlo, hhi⟩ := rPsi_mem_Ioo h1 h0
  obtain ⟨hpl, hpu⟩ := log_rPsi_bounds hlo hhi
  have hM : (0:ℝ) < 3 + Real.sqrt 6 := by nlinarith [Real.sqrt_nonneg 6]
  have hsplit : Real.log ((3 + Real.sqrt 6) * r)
      = Real.log 2 + Real.log ((3 + Real.sqrt 6) / 2) + Real.log r := by
    rw [Real.log_mul (ne_of_gt hM) (by linarith), log_rM_split]
  have hl2l : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2u : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [hsplit]
  constructor
  · linarith [lt_log_halfM]
  · linarith [log_halfM_lt]

/-- **Example 3.30, finite-born numerics**: the spectral dimension at a
finite-born point is `≈ 1.1160`. -/
theorem twoColour_spectral_finite_numeric (h1 : 1 < r) (h0 : psiPoly r = 0) :
    (1.1159:ℝ) < 2 * Real.log ((3 + Real.sqrt 6) / 2) / Real.log ((3 + Real.sqrt 6) * r) ∧
      2 * Real.log ((3 + Real.sqrt 6) / 2) / Real.log ((3 + Real.sqrt 6) * r) < 1.1161 := by
  obtain ⟨hdl, hdu⟩ := log_denom_bounds h1 h0
  have hd : (0:ℝ) < Real.log ((3 + Real.sqrt 6) * r) := by linarith
  constructor
  · rw [lt_div_iff₀ hd]
    nlinarith [lt_log_halfM]
  · rw [div_lt_iff₀ hd]
    nlinarith [log_halfM_lt]

/-- **Example 3.30, infinite-born numerics**: the spectral dimension at
`μ`-almost every infinite-born point is `≈ 1.8877`. -/
theorem twoColour_spectral_infinite_numeric (h1 : 1 < r) (h0 : psiPoly r = 0) :
    (1.8876:ℝ) < 2 * Real.log (3 + Real.sqrt 6) / Real.log ((3 + Real.sqrt 6) * r) ∧
      2 * Real.log (3 + Real.sqrt 6) / Real.log ((3 + Real.sqrt 6) * r) < 1.8878 := by
  obtain ⟨hdl, hdu⟩ := log_denom_bounds h1 h0
  have hd : (0:ℝ) < Real.log ((3 + Real.sqrt 6) * r) := by linarith
  have hl2l : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2u : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [log_rM_split]
  constructor
  · rw [lt_div_iff₀ hd]
    nlinarith [lt_log_halfM]
  · rw [div_lt_iff₀ hd]
    nlinarith [log_halfM_lt]

/-! ## Example 3.30 itself -/

/--
**Example 3.30, finite-born case.**
For the two-coloured EIGS of Figure 3, at every `x ∈ 𝒱` the diffusion and the
Brownian spectral dimensions coincide and equal
`2 log((3+√6)/2)/log((3+√6)ρ(Ψ)) ≈ 1.1160`.
-/
theorem twoColour_spectral_finite (h1 : 1 < r) (h0 : psiPoly r = 0) (p q : ℝ → ℝ)
    {c C t₀ : ℝ}
    (hqp : 0 < (twoColour r h1).dR → ∀ t, 0 < t → q t = p t)
    (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 < t₀)
    (hlow : ∀ t ∈ Set.Ioo (0:ℝ) t₀,
      c * t ^ (-((twoColour r h1).alphaFin / (twoColour r h1).dwalk)) ≤ p t)
    (hup : ∀ t ∈ Set.Ioo (0:ℝ) t₀,
      p t ≤ C * t ^ (-((twoColour r h1).alphaFin / (twoColour r h1).dwalk))) :
    Tendsto (fun t => -2 * Real.log (q t) / Real.log t) (𝓝[>] (0:ℝ))
        (𝓝 (2 * Real.log ((3 + Real.sqrt 6) / 2) / Real.log ((3 + Real.sqrt 6) * r))) ∧
      Tendsto (fun t => -2 * Real.log (p t) / Real.log t) (𝓝[>] (0:ℝ))
        (𝓝 (2 * Real.log ((3 + Real.sqrt 6) / 2) / Real.log ((3 + Real.sqrt 6) * r))) ∧
      (1.1159:ℝ) < 2 * Real.log ((3 + Real.sqrt 6) / 2) / Real.log ((3 + Real.sqrt 6) * r) ∧
      2 * Real.log ((3 + Real.sqrt 6) / 2) / Real.log ((3 + Real.sqrt 6) * r) < 1.1161 := by
  have hmain := (twoColour r h1).brownian_spectral_finite_born p q
    (twoColour_dR_pos h1) hqp hc hC ht₀ hlow hup
  rw [twoColour_spectral_finite_eq h1] at hmain
  exact ⟨hmain.1, hmain.2, (twoColour_spectral_finite_numeric h1 h0).1,
    (twoColour_spectral_finite_numeric h1 h0).2⟩

/--
**Example 3.30, almost-every infinite-born case.**
For the two-coloured EIGS of Figure 3, at `μ`-almost every `x ∈ V^∞` the
diffusion and the Brownian spectral dimensions coincide and equal
`2 log(3+√6)/log((3+√6)ρ(Ψ)) ≈ 1.8877`.
-/
theorem twoColour_spectral_infinite (h1 : 1 < r) (h0 : psiPoly r = 0) (p q : ℝ → ℝ)
    {c C t₀ theta : ℝ}
    (hqp : 0 < (twoColour r h1).dR → ∀ t, 0 < t → q t = p t)
    (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 < t₀)
    (hlow : ∀ t ∈ Set.Ioo (0:ℝ) t₀,
      c * |Real.log t| ^ (-theta) * t ^ (-((twoColour r h1).dbox / (twoColour r h1).dwalk))
        ≤ p t)
    (hup : ∀ t ∈ Set.Ioo (0:ℝ) t₀,
      p t ≤ C * t ^ (-((twoColour r h1).dbox / (twoColour r h1).dwalk))) :
    Tendsto (fun t => -2 * Real.log (q t) / Real.log t) (𝓝[>] (0:ℝ))
        (𝓝 (2 * Real.log (3 + Real.sqrt 6) / Real.log ((3 + Real.sqrt 6) * r))) ∧
      Tendsto (fun t => -2 * Real.log (p t) / Real.log t) (𝓝[>] (0:ℝ))
        (𝓝 (2 * Real.log (3 + Real.sqrt 6) / Real.log ((3 + Real.sqrt 6) * r))) ∧
      (1.8876:ℝ) < 2 * Real.log (3 + Real.sqrt 6) / Real.log ((3 + Real.sqrt 6) * r) ∧
      2 * Real.log (3 + Real.sqrt 6) / Real.log ((3 + Real.sqrt 6) * r) < 1.8878 := by
  have hmain := (twoColour r h1).brownian_spectral_infinite_born p q
    (twoColour_dR_pos h1) hqp hc hC ht₀ hlow hup
  rw [twoColour_spectral_infinite_eq h1] at hmain
  exact ⟨hmain.1, hmain.2, (twoColour_spectral_infinite_numeric h1 h0).1,
    (twoColour_spectral_infinite_numeric h1 h0).2⟩

end Sec33
end IGS
