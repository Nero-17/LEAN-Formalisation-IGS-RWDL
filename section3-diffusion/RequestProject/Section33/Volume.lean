import RequestProject.Section33.Exponents

/-!
# Section 3.3, step 1: the volume estimates (Lemma "heat-volume")

This file contains the *elementary* half of Lemma "heat-volume" of
arXiv:2603.13798: the passage from the geometric estimates

* `μ(B(x,r)) ≍ ρ(N)^{m-k} ρ(M)^{-m}` at a finite-born point of birth level `k`,
* `μ(B(x,r)) ≳ ρ(M)^{-m}` at any point (the cell containing `x` is inside the
  ball),

valid whenever `ρ_min(D)^{-(m+1)} < r ≤ ρ_min(D)^{-m}`, to the stated powers of
`r`:

* `μ(B(x,r)) ≍ r^{d_box(1 - 1/d_deg)}` for `x ∈ 𝒱`,
* `μ(B(x,r)) ≳ r^{d_box}`.

What is *taken as a hypothesis* is exactly what the paper quotes from §2 and from
Lemma "GHP_convergence": the counting estimate
`|V(B_{Ξ^n}(v,R_n))| ≍ ρ(N)^{m-k}ρ(M)^{n-m}` and the cell-mass estimate
`μ(Λ_m(x)) ≍ ρ(M)^{-m}`.  Everything else — the choice of the scale `m = m(r)`
and the conversion of `ρ(N)^{m-k}ρ(M)^{-m}` into a power of `r` — is proved.
-/

namespace IGS
namespace Sec33

open Real

namespace Params

variable (P : Params)

/-- `ρ_min(D) ^ (log r / log ρ_min(D)) = r` for `r > 0`. -/
lemma rD_rpow_log {r : ℝ} (hr : 0 < r) : P.rD ^ (log r / log P.rD) = r := by
  rw [Real.rpow_def_of_pos P.rD_pos]
  have hD : log P.rD ≠ 0 := ne_of_gt P.log_rD_pos
  have h : log P.rD * (log r / log P.rD) = log r := by
    field_simp
  rw [h, Real.exp_log hr]

/--
**Choice of the scale.**  For `0 < r ≤ 1` there is a unique integer `m ≥ 0` with
`ρ_min(D)^{-(m+1)} < r ≤ ρ_min(D)^{-m}`; this is the `m = m(r)` of the paper.
-/
lemma exists_dyadic_scale {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∃ m : ℕ, P.rD ^ (-((m : ℝ) + 1)) < r ∧ r ≤ P.rD ^ (-(m : ℝ)) := by
  set x : ℝ := -(log r / log P.rD) with hx
  have hx0 : 0 ≤ x := by
    have : log r ≤ 0 := Real.log_nonpos (le_of_lt hr0) hr1
    have := div_nonpos_of_nonpos_of_nonneg this (le_of_lt P.log_rD_pos)
    simpa [hx] using neg_nonneg.2 this
  refine ⟨⌊x⌋₊, ?_, ?_⟩
  · -- `x < ⌊x⌋₊ + 1` gives `ρ_min(D)^{-(⌊x⌋₊+1)} < r`
    have hlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have : P.rD ^ (-((⌊x⌋₊ : ℝ) + 1)) < P.rD ^ (-x) := by
      exact Real.rpow_lt_rpow_left_iff P.hrD |>.2 (by linarith)
    calc P.rD ^ (-((⌊x⌋₊ : ℝ) + 1)) < P.rD ^ (-x) := this
      _ = r := by rw [hx, neg_neg]; exact P.rD_rpow_log hr0
  · have hle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
    have : P.rD ^ (-x) ≤ P.rD ^ (-(⌊x⌋₊ : ℝ)) :=
      Real.rpow_le_rpow_left_iff P.hrD |>.2 (by linarith)
    calc r = P.rD ^ (-x) := by rw [hx, neg_neg]; exact (P.rD_rpow_log hr0).symm
      _ ≤ P.rD ^ (-(⌊x⌋₊ : ℝ)) := this

/--
The geometric quantity `ρ(N)^{m-k}ρ(M)^{-m}` of the paper equals
`ρ(N)^{-k} (ρ_min(D)^{-m})^{d_box(1-1/d_deg)}`.
-/
lemma geom_eq (k m : ℝ) :
    P.rN ^ (m - k) * P.rM ^ (-m) = P.rN ^ (-k) * (P.rD ^ (-m)) ^ P.alphaFin := by
  have hN : (0:ℝ) < P.rN := P.rN_pos
  have hM : (0:ℝ) < P.rM := P.rM_pos
  have hNm : (0:ℝ) < P.rN ^ m := Real.rpow_pos_of_pos hN m
  have hNk : (0:ℝ) < P.rN ^ k := Real.rpow_pos_of_pos hN k
  have hMm : (0:ℝ) < P.rM ^ m := Real.rpow_pos_of_pos hM m
  have h1 : P.rN ^ (m - k) * P.rM ^ (-m) = P.rN ^ (-k) * (P.rN / P.rM) ^ m := by
    rw [Real.div_rpow (le_of_lt hN) (le_of_lt hM), Real.rpow_sub hN,
      Real.rpow_neg (le_of_lt hM), Real.rpow_neg (le_of_lt hN)]
    field_simp
  rw [h1, P.volume_scaling]

/--
**Lemma "heat-volume", finite-born case.**

Hypothesis `hgeom` is the estimate the paper imports from §2 (Lemma 2.14) and
Lemma "GHP_convergence": at scale `m` the ball around a `k`-born point has mass
comparable to `ρ(N)^{m-k}ρ(M)^{-m}`.  The conclusion is the stated power of `r`,
with explicit constants.
-/
theorem volume_finite_born (vol : ℝ → ℝ) (k : ℕ) (cl cu : ℝ) (hcl : 0 < cl) (hcu : 0 < cu)
    (hgeom : ∀ m : ℕ, k ≤ m → ∀ r : ℝ, 0 < r → P.rD ^ (-((m : ℝ) + 1)) < r →
      r ≤ P.rD ^ (-(m : ℝ)) →
      cl * (P.rN ^ ((m : ℝ) - k) * P.rM ^ (-(m : ℝ))) ≤ vol r ∧
      vol r ≤ cu * (P.rN ^ ((m : ℝ) - k) * P.rM ^ (-(m : ℝ)))) :
    ∀ r : ℝ, 0 < r → r ≤ P.rD ^ (-(k : ℝ)) →
      cl * P.rN ^ (-(k : ℝ)) * r ^ P.alphaFin ≤ vol r ∧
      vol r ≤ cu * P.rN ^ (-(k : ℝ)) * P.rD ^ P.alphaFin * r ^ P.alphaFin := by
  intro r hr0 hrk
  have hr1 : r ≤ 1 := by
    refine le_trans hrk ?_
    have : P.rD ^ (-(k : ℝ)) ≤ P.rD ^ (0 : ℝ) :=
      Real.rpow_le_rpow_left_iff P.hrD |>.2 (neg_nonpos.2 (Nat.cast_nonneg k))
    simpa using this
  obtain ⟨m, hm1, hm2⟩ := P.exists_dyadic_scale hr0 hr1
  -- the scale is at least the birth level
  have hkm : k ≤ m := by
    by_contra h
    push_neg at h
    have hmk : (m : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast h
    have : P.rD ^ (-(k : ℝ)) ≤ P.rD ^ (-((m : ℝ) + 1)) :=
      Real.rpow_le_rpow_left_iff P.hrD |>.2 (by linarith)
    linarith [lt_of_le_of_lt (le_trans hrk this) hm1]
  obtain ⟨hlow, hup⟩ := hgeom m hkm r hr0 hm1 hm2
  rw [P.geom_eq (k : ℝ) (m : ℝ)] at hlow hup
  have halpha : 0 < P.alphaFin := P.alphaFin_pos
  have hNk : 0 < P.rN ^ (-(k : ℝ)) := Real.rpow_pos_of_pos P.rN_pos _
  -- `r ≤ ρ_min(D)^{-m} < ρ_min(D) * r`
  have hscale_up : P.rD ^ (-(m : ℝ)) < P.rD * r := by
    have key : P.rD ^ (-((m : ℝ) + 1)) * P.rD = P.rD ^ (-(m : ℝ)) := by
      rw [← Real.rpow_add_one (ne_of_gt P.rD_pos)]
      ring_nf
    have h := mul_lt_mul_of_pos_right hm1 P.rD_pos
    rw [key] at h
    linarith [h, mul_comm P.rD r]
  constructor
  · -- lower bound
    have h1 : r ^ P.alphaFin ≤ (P.rD ^ (-(m : ℝ))) ^ P.alphaFin :=
      Real.rpow_le_rpow (le_of_lt hr0) hm2 (le_of_lt halpha)
    calc cl * P.rN ^ (-(k : ℝ)) * r ^ P.alphaFin
        ≤ cl * P.rN ^ (-(k : ℝ)) * (P.rD ^ (-(m : ℝ))) ^ P.alphaFin := by
          have : 0 < cl * P.rN ^ (-(k : ℝ)) := by positivity
          nlinarith
      _ = cl * (P.rN ^ (-(k : ℝ)) * (P.rD ^ (-(m : ℝ))) ^ P.alphaFin) := by ring
      _ ≤ vol r := hlow
  · -- upper bound
    have h1 : (P.rD ^ (-(m : ℝ))) ^ P.alphaFin ≤ (P.rD * r) ^ P.alphaFin :=
      Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos P.rD_pos _))
        (le_of_lt hscale_up) (le_of_lt halpha)
    have h2 : (P.rD * r) ^ P.alphaFin = P.rD ^ P.alphaFin * r ^ P.alphaFin :=
      Real.mul_rpow (le_of_lt P.rD_pos) (le_of_lt hr0)
    calc vol r ≤ cu * (P.rN ^ (-(k : ℝ)) * (P.rD ^ (-(m : ℝ))) ^ P.alphaFin) := hup
      _ ≤ cu * (P.rN ^ (-(k : ℝ)) * (P.rD ^ P.alphaFin * r ^ P.alphaFin)) := by
          have : 0 < cu * P.rN ^ (-(k : ℝ)) := by positivity
          rw [h2] at h1
          nlinarith
      _ = cu * P.rN ^ (-(k : ℝ)) * P.rD ^ P.alphaFin * r ^ P.alphaFin := by ring

/--
**Lemma "heat-volume", the lower bound at an arbitrary point.**

If the level-`m` cell containing `x` is contained in `B(x,r)` whenever
`ρ_min(D)^{-(m+1)} < r ≤ ρ_min(D)^{-m}`, and cells of level `m` have mass at
least `c ρ(M)^{-m}` (Lemma "GHP_convergence"), then `μ(B(x,r)) ≥ c r^{d_box}`.
-/
theorem volume_lower_cell (vol : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hcell : ∀ m : ℕ, ∀ r : ℝ, 0 < r → P.rD ^ (-((m : ℝ) + 1)) < r → r ≤ P.rD ^ (-(m : ℝ)) →
      c * P.rM ^ (-(m : ℝ)) ≤ vol r) :
    ∀ r : ℝ, 0 < r → r ≤ 1 → c * r ^ P.dbox ≤ vol r := by
  intro r hr0 hr1
  obtain ⟨m, hm1, hm2⟩ := P.exists_dyadic_scale hr0 hr1
  have h := hcell m r hr0 hm1 hm2
  rw [P.mass_scaling (m : ℝ)] at h
  have h1 : r ^ P.dbox ≤ (P.rD ^ (-(m : ℝ))) ^ P.dbox :=
    Real.rpow_le_rpow (le_of_lt hr0) hm2 (le_of_lt P.dbox_pos)
  nlinarith

end Params

end Sec33
end IGS
