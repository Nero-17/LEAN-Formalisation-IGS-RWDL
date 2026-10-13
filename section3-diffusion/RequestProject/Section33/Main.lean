import RequestProject.Section33.Volume
import RequestProject.Section33.VolumeAE
import RequestProject.Section33.ExitTime
import RequestProject.Section33.HeatUpper
import RequestProject.Section3.OnDiagonalLower
import RequestProject.Section3.SpectralDimension
import RequestProject.Section3.Recursions

/-!
# Section 3.3, step 6: Theorem "diffusion-heat" and Theorem "diffusion-spectral"

This file puts the pieces together the way the paper does.

* Theorem "general-lower" (already formalised in `Section3.OnDiagonalLower`)
  gives `p_{2t}(x,x) ≥ p_x²/μ(B(x,C t^{1/d_walk}))`.  Combined with the volume
  estimates of Lemma "heat-volume" — `μ(B(x,r)) ≤ C r^{γ}` resp.
  `μ(B(x,r)) ≤ C |log r|^{θ} r^{γ}` — this yields the on-diagonal *lower* bounds
  of Theorem "diffusion-heat" (`on_diagonal_lower_of_volume`,
  `on_diagonal_lower_of_volume_log`), with the exponent conversion
  `(t^{1/d_walk})^{γ} = t^{γ/d_walk}` and the elementary bound
  `|log (a t^{b})| ≤ (|log a| + b)|log t|` proved here.
* The on-diagonal *upper* bounds come from `Section33.HeatUpper`.
* Finally Theorem "diffusion-spectral" is the limit computation of
  `Section3.SpectralDimension`, and Proposition "final_recurrent" is the
  algebraic equivalence `2 d_box/d_walk < 2 ↔ d_R > 0`, which here follows from
  the Einstein relation `d_walk = d_box + d_R`.
-/

namespace IGS
namespace Sec33

open Real Filter Topology

namespace Params

variable (P : Params)

/-- `(t^{1/d_walk})^{γ} = t^{γ/d_walk}`. -/
lemma rpow_radius_pow {t : ℝ} (ht : 0 < t) (gamma : ℝ) :
    (t ^ (1 / P.dwalk)) ^ gamma = t ^ (gamma / P.dwalk) := by
  rw [← Real.rpow_mul (le_of_lt ht)]
  congr 1
  field_simp

/--
**On-diagonal lower bound from a polynomial volume bound.**
This is the finite-born case of Theorem "diffusion-heat": Theorem "general-lower"
plus `μ(B(x,r)) ≤ C_vol r^γ` give `p_{2t}(x,x) ≥ c t^{-γ/d_walk}`.
-/
theorem on_diagonal_lower_of_volume (pdiag vol : ℝ → ℝ) {pstay Cr Cvol gamma t : ℝ}
    (hpstay : 0 < pstay) (hCr : 0 < Cr) (hCvol : 0 < Cvol)
    (ht : 0 < t) (hvol0 : 0 ≤ vol (Cr * t ^ (1 / P.dwalk)))
    (hlower : pstay ^ 2 ≤ vol (Cr * t ^ (1 / P.dwalk)) * pdiag (2 * t))
    (hvol : vol (Cr * t ^ (1 / P.dwalk)) ≤ Cvol * (Cr * t ^ (1 / P.dwalk)) ^ gamma) :
    (pstay ^ 2 / (Cvol * Cr ^ gamma)) * t ^ (-(gamma / P.dwalk)) ≤ pdiag (2 * t) := by
  have htpow : (0:ℝ) < t ^ (1 / P.dwalk) := Real.rpow_pos_of_pos ht _
  have hB : Cvol * (Cr * t ^ (1 / P.dwalk)) ^ gamma
      = (Cvol * Cr ^ gamma) * t ^ (gamma / P.dwalk) := by
    rw [Real.mul_rpow (le_of_lt hCr) (le_of_lt htpow), P.rpow_radius_pow ht]
    ring
  have hBpos : 0 < (Cvol * Cr ^ gamma) * t ^ (gamma / P.dwalk) := by
    have h1 : (0:ℝ) < Cr ^ gamma := Real.rpow_pos_of_pos hCr _
    have h2 : (0:ℝ) < t ^ (gamma / P.dwalk) := Real.rpow_pos_of_pos ht _
    positivity
  -- the heat kernel value is nonnegative
  have hp0 : 0 ≤ pdiag (2 * t) := by
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg pstay, mul_nonneg hvol0 (le_of_lt (neg_pos.2 h))]
  have hkey : pstay ^ 2 ≤ ((Cvol * Cr ^ gamma) * t ^ (gamma / P.dwalk)) * pdiag (2 * t) := by
    calc pstay ^ 2 ≤ vol (Cr * t ^ (1 / P.dwalk)) * pdiag (2 * t) := hlower
      _ ≤ (Cvol * (Cr * t ^ (1 / P.dwalk)) ^ gamma) * pdiag (2 * t) :=
          mul_le_mul_of_nonneg_right hvol hp0
      _ = ((Cvol * Cr ^ gamma) * t ^ (gamma / P.dwalk)) * pdiag (2 * t) := by rw [hB]
  have hdiv : pstay ^ 2 / ((Cvol * Cr ^ gamma) * t ^ (gamma / P.dwalk)) ≤ pdiag (2 * t) := by
    rw [div_le_iff₀ hBpos]
    linarith [hkey]
  have hsplit : pstay ^ 2 / ((Cvol * Cr ^ gamma) * t ^ (gamma / P.dwalk))
      = (pstay ^ 2 / (Cvol * Cr ^ gamma)) * t ^ (-(gamma / P.dwalk)) := by
    rw [Real.rpow_neg (le_of_lt ht)]
    field_simp
  rwa [hsplit] at hdiv

end Params

/-- `|log (a t^b)| ≤ (|log a| + b)|log t|` for `0 < t ≤ e^{-1}`, `a > 0`, `b ≥ 0`. -/
theorem log_comp_le {a b t : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (ht : 0 < t)
    (hte : t ≤ Real.exp (-1)) :
    |Real.log (a * t ^ b)| ≤ (|Real.log a| + b) * |Real.log t| := by
  have hlogt : Real.log t ≤ -1 := by
    have := Real.log_le_log ht hte
    simpa using this
  have habs : (1:ℝ) ≤ |Real.log t| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hsplit : Real.log (a * t ^ b) = Real.log a + b * Real.log t := by
    rw [Real.log_mul (ne_of_gt ha) (ne_of_gt (Real.rpow_pos_of_pos ht b)), Real.log_rpow ht]
  rw [hsplit]
  calc |Real.log a + b * Real.log t| ≤ |Real.log a| + |b * Real.log t| := abs_add_le _ _
    _ = |Real.log a| + b * |Real.log t| := by rw [abs_mul, abs_of_nonneg hb]
    _ ≤ |Real.log a| * |Real.log t| + b * |Real.log t| := by nlinarith [abs_nonneg (Real.log a)]
    _ = (|Real.log a| + b) * |Real.log t| := by ring

namespace Params

variable (P : Params)

/--
**On-diagonal lower bound from a volume bound with a logarithmic correction.**
This is the almost-every infinite-born case of Theorem "diffusion-heat":
`μ(B(x,r)) ≤ C_vol |log r|^{θ} r^{γ}` gives
`p_{2t}(x,x) ≥ c |log t|^{-θ} t^{-γ/d_walk}`.
-/
theorem on_diagonal_lower_of_volume_log (pdiag vol : ℝ → ℝ)
    {pstay Cr Cvol gamma theta t : ℝ}
    (hpstay : 0 < pstay) (hCr : 0 < Cr) (hCvol : 0 < Cvol)
    (htheta : 0 ≤ theta) (ht : 0 < t) (hte : t ≤ Real.exp (-1))
    (hvol0 : 0 ≤ vol (Cr * t ^ (1 / P.dwalk)))
    (hlower : pstay ^ 2 ≤ vol (Cr * t ^ (1 / P.dwalk)) * pdiag (2 * t))
    (hvol : vol (Cr * t ^ (1 / P.dwalk))
      ≤ Cvol * |Real.log (Cr * t ^ (1 / P.dwalk))| ^ theta
        * (Cr * t ^ (1 / P.dwalk)) ^ gamma) :
    (pstay ^ 2 / (Cvol * (|Real.log Cr| + 1 / P.dwalk) ^ theta * Cr ^ gamma))
      * |Real.log t| ^ (-theta) * t ^ (-(gamma / P.dwalk)) ≤ pdiag (2 * t) := by
  have hdw : 0 < P.dwalk := P.dwalk_pos
  have hinv : 0 ≤ 1 / P.dwalk := by positivity
  have htpow : (0:ℝ) < t ^ (1 / P.dwalk) := Real.rpow_pos_of_pos ht _
  have hK : 0 < |Real.log Cr| + 1 / P.dwalk := by
    have : 0 < 1 / P.dwalk := by positivity
    linarith [abs_nonneg (Real.log Cr)]
  have hlogt : Real.log t ≤ -1 := by
    have := Real.log_le_log ht hte
    simpa using this
  have hlogabs : (1:ℝ) ≤ |Real.log t| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  -- control the logarithmic factor
  have hlogfac : |Real.log (Cr * t ^ (1 / P.dwalk))| ^ theta
      ≤ (|Real.log Cr| + 1 / P.dwalk) ^ theta * |Real.log t| ^ theta := by
    have h1 := log_comp_le hCr hinv ht hte
    have h2 : |Real.log (Cr * t ^ (1 / P.dwalk))| ^ theta
        ≤ ((|Real.log Cr| + 1 / P.dwalk) * |Real.log t|) ^ theta :=
      Real.rpow_le_rpow (abs_nonneg _) h1 htheta
    rwa [Real.mul_rpow (le_of_lt hK) (abs_nonneg _)] at h2
  -- the heat kernel value is nonnegative
  have hp0 : 0 ≤ pdiag (2 * t) := by
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg pstay, mul_nonneg hvol0 (le_of_lt (neg_pos.2 h))]
  have hCrg : (0:ℝ) < Cr ^ gamma := Real.rpow_pos_of_pos hCr _
  have hKt : (0:ℝ) < (|Real.log Cr| + 1 / P.dwalk) ^ theta := Real.rpow_pos_of_pos hK _
  have hlogp : (0:ℝ) < |Real.log t| ^ theta :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hlogabs) _
  have htg : (0:ℝ) < t ^ (gamma / P.dwalk) := Real.rpow_pos_of_pos ht _
  -- assemble the volume bound
  have hvol' : vol (Cr * t ^ (1 / P.dwalk))
      ≤ (Cvol * (|Real.log Cr| + 1 / P.dwalk) ^ theta * Cr ^ gamma)
        * (|Real.log t| ^ theta * t ^ (gamma / P.dwalk)) := by
    have hgeom : (Cr * t ^ (1 / P.dwalk)) ^ gamma = Cr ^ gamma * t ^ (gamma / P.dwalk) := by
      rw [Real.mul_rpow (le_of_lt hCr) (le_of_lt htpow), P.rpow_radius_pow ht]
    refine le_trans hvol ?_
    rw [hgeom]
    have hstep : Cvol * |Real.log (Cr * t ^ (1 / P.dwalk))| ^ theta
        ≤ Cvol * ((|Real.log Cr| + 1 / P.dwalk) ^ theta * |Real.log t| ^ theta) :=
      mul_le_mul_of_nonneg_left hlogfac (le_of_lt hCvol)
    have hpos : (0:ℝ) ≤ Cr ^ gamma * t ^ (gamma / P.dwalk) := by positivity
    nlinarith [hstep, hpos]
  set B : ℝ := (Cvol * (|Real.log Cr| + 1 / P.dwalk) ^ theta * Cr ^ gamma) with hB
  have hBpos : 0 < B := by
    rw [hB]; positivity
  have hkey : pstay ^ 2 ≤ (B * (|Real.log t| ^ theta * t ^ (gamma / P.dwalk))) * pdiag (2 * t) := by
    calc pstay ^ 2 ≤ vol (Cr * t ^ (1 / P.dwalk)) * pdiag (2 * t) := hlower
      _ ≤ (B * (|Real.log t| ^ theta * t ^ (gamma / P.dwalk))) * pdiag (2 * t) :=
          mul_le_mul_of_nonneg_right hvol' hp0
  have hden : 0 < B * (|Real.log t| ^ theta * t ^ (gamma / P.dwalk)) := by positivity
  have hdiv : pstay ^ 2 / (B * (|Real.log t| ^ theta * t ^ (gamma / P.dwalk))) ≤ pdiag (2 * t) := by
    rw [div_le_iff₀ hden]
    linarith [hkey]
  have hsplit : pstay ^ 2 / (B * (|Real.log t| ^ theta * t ^ (gamma / P.dwalk)))
      = (pstay ^ 2 / B) * |Real.log t| ^ (-theta) * t ^ (-(gamma / P.dwalk)) := by
    rw [Real.rpow_neg (abs_nonneg _), Real.rpow_neg (le_of_lt ht)]
    field_simp
  rwa [hsplit] at hdiv


/--
**Theorem "diffusion-heat", lower bound: the whole chain.**

This is Theorem "general-lower" (`IGS.heat_kernel_on_diagonal_lower`, proved in
`Section3.OnDiagonalLower` from the survival estimate and Chapman–Kolmogorov)
composed with the volume bound of Lemma "heat-volume": the conclusion is the
on-diagonal lower bound `p_{2t}(x,x) ≥ c t^{-γ/d_walk}` where `γ` is the volume
exponent at `x` (`γ = d_box(1-1/d_deg)` at a finite-born point).
-/
theorem on_diagonal_lower_of_survival {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (p : ℝ → X → X → ℝ) (mu : MeasureTheory.Measure X) (x : X)
    {t pstay Cr Cvol gamma : ℝ}
    (hpstay : 0 < pstay) (hCr : 0 < Cr) (hCvol : 0 < Cvol) (ht : 0 < t)
    (hp0 : 0 ≤ᵐ[mu] fun y => p t x y)
    (hmem : MeasureTheory.MemLp (fun y => p t x y) 2 mu)
    (hball : mu (Metric.ball x (Cr * t ^ (1 / P.dwalk))) ≠ ⊤)
    (hstay : pstay ≤ ∫ y in Metric.ball x (Cr * t ^ (1 / P.dwalk)), p t x y ∂mu)
    (hCK : ∫ y, (p t x y) ^ 2 ∂mu = p (2 * t) x x)
    (hvol : (mu (Metric.ball x (Cr * t ^ (1 / P.dwalk)))).toReal
      ≤ Cvol * (Cr * t ^ (1 / P.dwalk)) ^ gamma) :
    (pstay ^ 2 / (Cvol * Cr ^ gamma)) * t ^ (-(gamma / P.dwalk)) ≤ p (2 * t) x x := by
  have hlower := heat_kernel_on_diagonal_lower p mu x t (Cr * t ^ (1 / P.dwalk)) pstay
    (le_of_lt hpstay) hp0 hmem hball hstay hCK
  exact P.on_diagonal_lower_of_volume (fun s => p s x x)
    (fun r => (mu (Metric.ball x r)).toReal) hpstay hCr hCvol ht
    ENNReal.toReal_nonneg hlower hvol

/--
**Theorem "diffusion-spectral", finite-born case**, for the exponents of §3.3:
two-sided bounds `c t^{-α/d_walk} ≤ p_t(x,x) ≤ C t^{-α/d_walk}` with
`α = d_box(1-1/d_deg)` give the local spectral dimension
`2 d_box(1-1/d_deg)/d_walk`.
-/
theorem spectral_dim_finite_born (pdiag : ℝ → ℝ) {c C t₀ : ℝ}
    (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 < t₀)
    (hlow : ∀ t ∈ Set.Ioo (0:ℝ) t₀, c * t ^ (-(P.alphaFin / P.dwalk)) ≤ pdiag t)
    (hup : ∀ t ∈ Set.Ioo (0:ℝ) t₀, pdiag t ≤ C * t ^ (-(P.alphaFin / P.dwalk))) :
    Tendsto (fun t => -2 * Real.log (pdiag t) / Real.log t) (𝓝[>] (0:ℝ))
      (𝓝 (2 * (P.dbox * (1 - 1 / P.ddeg) / P.dwalk))) := by
  have := tendsto_spectral_dimension_of_pure_bounds pdiag (P.alphaFin / P.dwalk) c C t₀
    hc hC ht₀ hlow hup
  simpa [Params.alphaFin] using this

/--
**Theorem "diffusion-spectral", almost-every infinite-born case**: the
logarithmic correction of exponent `θ` does not change the spectral dimension,
which equals `2 d_box/d_walk`.
-/
theorem spectral_dim_infinite_born (pdiag : ℝ → ℝ) {c C t₀ theta : ℝ}
    (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 < t₀)
    (hlow : ∀ t ∈ Set.Ioo (0:ℝ) t₀,
      c * |Real.log t| ^ (-theta) * t ^ (-(P.dbox / P.dwalk)) ≤ pdiag t)
    (hup : ∀ t ∈ Set.Ioo (0:ℝ) t₀, pdiag t ≤ C * t ^ (-(P.dbox / P.dwalk))) :
    Tendsto (fun t => -2 * Real.log (pdiag t) / Real.log t) (𝓝[>] (0:ℝ))
      (𝓝 (2 * (P.dbox / P.dwalk))) :=
  tendsto_spectral_dimension_of_bounds pdiag (P.dbox / P.dwalk) theta c C t₀ hc hC ht₀ hlow hup

/--
**Proposition "final_recurrent" (algebraic part).**
The infinite-born spectral dimension `2 d_box/d_walk` is `< 2` exactly when the
resistance dimension is positive; by the Einstein relation this is the recurrence
regime of the simple random walk.
-/
theorem spectral_lt_two_iff : 2 * P.dbox / P.dwalk < 2 ↔ 0 < P.dR := by
  have hE : P.dwalk = P.dbox + P.dR := P.dwalk_eq_dbox_add_dR
  have hsum : 0 < P.dbox + P.dR := by rw [← hE]; exact P.dwalk_pos
  rw [hE]
  exact spectral_lt_two_iff_resistance_pos P.dbox P.dR hsum

end Params

end Sec33
end IGS
