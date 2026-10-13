import RequestProject.Section33.Skeleton

/-!
# Section 3.3, step 3: the volume upper bound with its logarithmic correction

Combining the Borel–Cantelli output of `Section33.Skeleton` (almost every point
avoids the `L_m`-skeleton neighbourhood eventually, so the nearby level-`m`
terminal is born after level `m - L_m`) with the finite-born volume estimate of
`Section33.Volume`, the paper obtains, at `μ`-almost every infinite-born point,

`μ(B(x, c ρ_min(D)^{-m})) ≲ ρ(N)^{L_m} ρ(M)^{-m}`.

This file performs the last conversion, into the form stated in Lemma
"heat-volume":

`μ(B(x,r)) ≤ C |log r|^{(1+ε)/(d_deg-1)} r^{d_box}`  for all small `r`.
-/

namespace IGS
namespace Sec33

open Real

namespace Params

variable (P : Params)

/--
**Lemma "heat-volume", upper bound at an infinite-born point.**

`volx r` is `μ(B(x,r))`.  The hypotheses are:

* `hmono`: `r ↦ μ(B(x,r))` is monotone (true for balls);
* `hgeo`: the geometric estimate `μ(B(x,ρ_min(D)^{-m})) ≤ C_geo ρ(N)^{L_m}ρ(M)^{-m}`
  for all `m ≥ m₀`, which is what the Borel–Cantelli argument together with the
  finite-born estimate provides.

The conclusion is the stated power of `r` with a logarithmic correction of
exponent `(1+ε)/(d_deg-1)`, valid for all `r` below an explicit threshold.
-/
theorem volume_upper_log (volx : ℝ → ℝ) {eps Cgeo : ℝ} (heps : 0 ≤ eps) (hCgeo : 0 ≤ Cgeo)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀)
    (hmono : ∀ r s : ℝ, 0 < r → r ≤ s → volx r ≤ volx s)
    (hgeo : ∀ m : ℕ, m₀ ≤ m →
      volx (P.rD ^ (-(m : ℝ))) ≤ Cgeo * (P.rN ^ (P.Lscale eps m) * P.rM ^ (-(m : ℝ)))) :
    ∀ r : ℝ, 0 < r → r ≤ P.rD ^ (-(m₀ : ℝ)) →
      volx r ≤ (Cgeo * P.rN * (log P.rD)⁻¹ ^ ((1 + eps) / (P.ddeg - 1)) * P.rD ^ P.dbox)
        * |log r| ^ ((1 + eps) / (P.ddeg - 1)) * r ^ P.dbox := by
  intro r hr0 hrle
  set theta : ℝ := (1 + eps) / (P.ddeg - 1) with hth
  have hddeg1 : 0 < P.ddeg - 1 := by linarith [P.ddeg_one_lt]
  have htheta : 0 ≤ theta := by
    rw [hth]; positivity
  have hr1 : r ≤ 1 := by
    refine le_trans hrle ?_
    have : P.rD ^ (-(m₀ : ℝ)) ≤ P.rD ^ (0 : ℝ) :=
      Real.rpow_le_rpow_left_iff P.hrD |>.2 (neg_nonpos.2 (Nat.cast_nonneg m₀))
    simpa using this
  obtain ⟨m, hm1, hm2⟩ := P.exists_dyadic_scale hr0 hr1
  -- the scale is at least `m₀`
  have hmm₀ : m₀ ≤ m := by
    by_contra h
    push_neg at h
    have hc : (m : ℝ) + 1 ≤ (m₀ : ℝ) := by exact_mod_cast h
    have : P.rD ^ (-(m₀ : ℝ)) ≤ P.rD ^ (-((m : ℝ) + 1)) :=
      Real.rpow_le_rpow_left_iff P.hrD |>.2 (by linarith)
    linarith [lt_of_le_of_lt (le_trans hrle this) hm1]
  have hm1' : 1 ≤ m := le_trans hm₀ hmm₀
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm1'
  -- monotonicity and the geometric estimate
  have step1 : volx r ≤ Cgeo * (P.rN ^ (P.Lscale eps m) * P.rM ^ (-(m : ℝ))) :=
    le_trans (hmono r _ hr0 hm2) (hgeo m hmm₀)
  -- the logarithmic factor
  have hlogm : (m : ℝ) ≤ |log r| * (log P.rD)⁻¹ := by
    have h : log r ≤ -(m : ℝ) * log P.rD := by
      have := Real.log_le_log hr0 hm2
      rwa [Real.log_rpow P.rD_pos] at this
    have habs : |log r| = -log r := abs_of_nonpos (Real.log_nonpos (le_of_lt hr0) hr1)
    rw [habs, ← div_eq_mul_inv, le_div_iff₀ P.log_rD_pos]
    linarith
  have hlogpow : (m : ℝ) ^ theta ≤ (|log r| * (log P.rD)⁻¹) ^ theta :=
    Real.rpow_le_rpow (le_of_lt hmpos) hlogm htheta
  have hNL : P.rN ^ (P.Lscale eps m) ≤ P.rN * (m : ℝ) ^ theta :=
    P.rN_pow_Lscale_le heps hm1'
  -- the mass factor
  have hscale_up : P.rD ^ (-(m : ℝ)) < P.rD * r := by
    have key : P.rD ^ (-((m : ℝ) + 1)) * P.rD = P.rD ^ (-(m : ℝ)) := by
      rw [← Real.rpow_add_one (ne_of_gt P.rD_pos)]
      ring_nf
    have h := mul_lt_mul_of_pos_right hm1 P.rD_pos
    rw [key] at h
    linarith [h, mul_comm P.rD r]
  have hmass : P.rM ^ (-(m : ℝ)) ≤ P.rD ^ P.dbox * r ^ P.dbox := by
    rw [P.mass_scaling (m : ℝ)]
    have h1 : (P.rD ^ (-(m : ℝ))) ^ P.dbox ≤ (P.rD * r) ^ P.dbox :=
      Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos P.rD_pos _))
        (le_of_lt hscale_up) (le_of_lt P.dbox_pos)
    rwa [Real.mul_rpow (le_of_lt P.rD_pos) (le_of_lt hr0)] at h1
  -- put the pieces together
  have hsplit : (|log r| * (log P.rD)⁻¹) ^ theta
      = |log r| ^ theta * ((log P.rD)⁻¹) ^ theta := by
    exact Real.mul_rpow (abs_nonneg _) (le_of_lt (inv_pos.2 P.log_rD_pos))
  have hNLr : P.rN ^ (P.Lscale eps m)
      ≤ P.rN * ((log P.rD)⁻¹ ^ theta) * |log r| ^ theta := by
    calc P.rN ^ (P.Lscale eps m) ≤ P.rN * (m : ℝ) ^ theta := hNL
      _ ≤ P.rN * ((|log r| * (log P.rD)⁻¹) ^ theta) := by
          have : (0:ℝ) < P.rN := P.rN_pos
          nlinarith
      _ = P.rN * ((log P.rD)⁻¹ ^ theta) * |log r| ^ theta := by rw [hsplit]; ring
  have hNLpos : 0 ≤ P.rN ^ (P.Lscale eps m) := le_of_lt (pow_pos P.rN_pos _)
  have hmasspos : 0 ≤ P.rM ^ (-(m : ℝ)) := le_of_lt (Real.rpow_pos_of_pos P.rM_pos _)
  have hprod : P.rN ^ (P.Lscale eps m) * P.rM ^ (-(m : ℝ))
      ≤ (P.rN * ((log P.rD)⁻¹ ^ theta) * |log r| ^ theta) * (P.rD ^ P.dbox * r ^ P.dbox) := by
    have h1 : 0 ≤ P.rN * ((log P.rD)⁻¹ ^ theta) * |log r| ^ theta := by
      have h2 : (0:ℝ) ≤ (log P.rD)⁻¹ ^ theta :=
        le_of_lt (Real.rpow_pos_of_pos (by simpa using inv_pos.2 P.log_rD_pos) _)
      have h3 : (0:ℝ) ≤ |log r| ^ theta := Real.rpow_nonneg (abs_nonneg _) _
      exact mul_nonneg (mul_nonneg (le_of_lt P.rN_pos) h2) h3
    exact mul_le_mul hNLr hmass hmasspos h1
  calc volx r ≤ Cgeo * (P.rN ^ (P.Lscale eps m) * P.rM ^ (-(m : ℝ))) := step1
    _ ≤ Cgeo * ((P.rN * ((log P.rD)⁻¹ ^ theta) * |log r| ^ theta)
          * (P.rD ^ P.dbox * r ^ P.dbox)) := by
        exact mul_le_mul_of_nonneg_left hprod hCgeo
    _ = (Cgeo * P.rN * (log P.rD)⁻¹ ^ theta * P.rD ^ P.dbox) * |log r| ^ theta * r ^ P.dbox := by
        ring

/--
**Lemma "heat-volume", upper bound at an infinite-born point, as stated in the
current version of the paper.**

Same statement as `volume_upper_log`, with the parameter of `L_m` calibrated so
that the logarithmic exponent is literally the one displayed in the paper,

`μ(B(x,r)) ≤ C |log r|^{1/(d_deg-1)+ε} r^{d_box}`.
-/
theorem volume_upper_logExp (volx : ℝ → ℝ) {eps Cgeo : ℝ} (heps : 0 ≤ eps) (hCgeo : 0 ≤ Cgeo)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀)
    (hmono : ∀ r s : ℝ, 0 < r → r ≤ s → volx r ≤ volx s)
    (hgeo : ∀ m : ℕ, m₀ ≤ m →
      volx (P.rD ^ (-(m : ℝ)))
        ≤ Cgeo * (P.rN ^ (P.Lscale (eps * (P.ddeg - 1)) m) * P.rM ^ (-(m : ℝ)))) :
    ∀ r : ℝ, 0 < r → r ≤ P.rD ^ (-(m₀ : ℝ)) →
      volx r ≤ (Cgeo * P.rN * (log P.rD)⁻¹ ^ (P.logExp + eps) * P.rD ^ P.dbox)
        * |log r| ^ (P.logExp + eps) * r ^ P.dbox := by
  have hcal := P.calibrated_exponent eps
  have h := P.volume_upper_log volx (eps := eps * (P.ddeg - 1))
    (mul_nonneg heps (le_of_lt P.ddeg_sub_one_pos)) hCgeo m₀ hm₀ hmono hgeo
  rwa [hcal] at h

end Params

end Sec33
end IGS
