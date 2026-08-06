import Mathlib

/-!
# Section 3.3, step 0: the scaling exponents

Every estimate of §3.3 of *Iterated Graph Systems (I): random walks and diffusion
limits* (arXiv:2603.13798) is first proved in the "geometric" form

* a volume `≍ ρ(N)^{m-k} ρ(M)^{-m}` at scale `r ≍ ρ_min(D)^{-m}`,
* a heat-kernel value `≍ (ρ(M)/ρ(N))^{n}` at time `t ≍ (ρ(M)ρ(Ψ))^{-n}`,

and only then converted into a power of `r`, resp. of `t`.  This file contains
that conversion, i.e. the algebra of the four dimensions

`d_box = log ρ(M)/log ρ_min(D)`, `d_deg = log ρ(M)/log ρ(N)`,
`d_R = log ρ(Ψ)/log ρ_min(D)`, `d_walk = log(ρ(M)ρ(Ψ))/log ρ_min(D)`,

as they are defined in §1 and §2 of the paper (Einstein relation
`d_walk = d_box + d_R`, Theorem "Einstein").

Nothing here is a black box: these are honest identities between real numbers.
-/

namespace IGS
namespace Sec33

open Real

/--
The Perron/scaling data of an edge iterated graph system: the Perron roots
`ρ(M)` (global growth), `ρ(N)` (degree amplification), `ρ(Ψ)` (resistance
renormalisation) and the distance growth rate `ρ_min(D)`.

The standing inequalities are those of the scale-free regime of the paper:
distances and sizes grow (`1 < ρ_min(D)`, `1 < ρ(N) < ρ(M)`; `ρ(N) < ρ(M)` is
what makes `d_deg > 1`), resistances are renormalised by a positive factor, and
the parabolic scale `ρ(M)ρ(Ψ)` is `> 1` (equivalently `d_walk > 0`; the paper
even proves `d_walk ≥ 2`).
-/
structure Params where
  /-- `ρ(M)` -/
  rM : ℝ
  /-- `ρ(N)` -/
  rN : ℝ
  /-- `ρ(Ψ)` -/
  rPsi : ℝ
  /-- `ρ_min(D)` -/
  rD : ℝ
  hrD : 1 < rD
  hrN : 1 < rN
  hrNM : rN < rM
  hrPsi : 0 < rPsi
  hrMPsi : 1 < rM * rPsi

namespace Params

variable (P : Params)

lemma rM_pos : 0 < P.rM := lt_trans (lt_trans zero_lt_one P.hrN) P.hrNM
lemma rN_pos : 0 < P.rN := lt_trans zero_lt_one P.hrN
lemma rD_pos : 0 < P.rD := lt_trans zero_lt_one P.hrD
lemma rM_one_lt : 1 < P.rM := lt_trans P.hrN P.hrNM

lemma log_rD_pos : 0 < log P.rD := Real.log_pos P.hrD
lemma log_rN_pos : 0 < log P.rN := Real.log_pos P.hrN
lemma log_rM_pos : 0 < log P.rM := Real.log_pos P.rM_one_lt
lemma log_rMPsi_pos : 0 < log (P.rM * P.rPsi) := Real.log_pos P.hrMPsi

lemma log_rN_lt_log_rM : log P.rN < log P.rM := Real.log_lt_log P.rN_pos P.hrNM

/-- The box dimension `d_box(Ξ) = log ρ(M)/log ρ_min(D)`. -/
noncomputable def dbox : ℝ := log P.rM / log P.rD

/-- The degree dimension `d_deg(Ξ) = log ρ(M)/log ρ(N)`. -/
noncomputable def ddeg : ℝ := log P.rM / log P.rN

/-- The resistance dimension `d_R(Ξ) = log ρ(Ψ)/log ρ_min(D)`. -/
noncomputable def dR : ℝ := log P.rPsi / log P.rD

/-- The walk dimension `d_walk(Ξ) = log (ρ(M)ρ(Ψ))/log ρ_min(D)`. -/
noncomputable def dwalk : ℝ := log (P.rM * P.rPsi) / log P.rD

lemma dbox_pos : 0 < P.dbox := div_pos P.log_rM_pos P.log_rD_pos
lemma dwalk_pos : 0 < P.dwalk := div_pos P.log_rMPsi_pos P.log_rD_pos
lemma ddeg_one_lt : 1 < P.ddeg := (one_lt_div P.log_rN_pos).2 P.log_rN_lt_log_rM
lemma ddeg_pos : 0 < P.ddeg := lt_trans zero_lt_one P.ddeg_one_lt

/-- **Einstein relation** `d_walk = d_box + d_R` (Theorem "Einstein" of the paper). -/
lemma dwalk_eq_dbox_add_dR : P.dwalk = P.dbox + P.dR := by
  unfold dwalk dbox dR
  rw [Real.log_mul (ne_of_gt P.rM_pos) (ne_of_gt P.hrPsi)]
  ring

/-- The exponent appearing at finite-born points, `d_box (1 - 1/d_deg)`. -/
noncomputable def alphaFin : ℝ := P.dbox * (1 - 1 / P.ddeg)

lemma alphaFin_eq : P.alphaFin = (log P.rM - log P.rN) / log P.rD := by
  unfold alphaFin dbox ddeg
  have hM : log P.rM ≠ 0 := ne_of_gt P.log_rM_pos
  have hN : log P.rN ≠ 0 := ne_of_gt P.log_rN_pos
  have hD : log P.rD ≠ 0 := ne_of_gt P.log_rD_pos
  field_simp

lemma alphaFin_pos : 0 < P.alphaFin := by
  rw [alphaFin_eq]
  exact div_pos (by linarith [P.log_rN_lt_log_rM]) P.log_rD_pos

lemma alphaFin_lt_dbox : P.alphaFin < P.dbox := by
  rw [alphaFin_eq]
  unfold dbox
  exact div_lt_div_of_pos_right (by linarith [P.log_rN_pos]) P.log_rD_pos

end Params

/--
**The basic rescaling identity.**  For `A > 0` and `s > 0` with `log s ≠ 0`,
`A ^ m = (s ^ (-m)) ^ (-(log A / log s))`: a geometric sequence in the "size"
parameter `s^{-m}` is a power of that parameter, with exponent `-log A/log s`.

All the exponent computations of §3.3 are instances of this identity.
-/
lemma rpow_scale {A s : ℝ} (hA : 0 < A) (hs : 0 < s) (hls : log s ≠ 0) (m : ℝ) :
    A ^ m = (s ^ (-m)) ^ (-(log A / log s)) := by
  rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos (Real.rpow_pos_of_pos hs _),
    Real.log_rpow hs]
  congr 1
  field_simp

namespace Params

variable (P : Params)

/-- The volume scaling: `(ρ(N)/ρ(M))^m = (ρ_min(D)^{-m})^{d_box(1-1/d_deg)}`. -/
lemma volume_scaling (m : ℝ) :
    (P.rN / P.rM) ^ m = (P.rD ^ (-m)) ^ P.alphaFin := by
  have h := rpow_scale (A := P.rN / P.rM) (s := P.rD)
    (div_pos P.rN_pos P.rM_pos) P.rD_pos (ne_of_gt P.log_rD_pos) m
  rw [h]
  congr 1
  rw [Real.log_div (ne_of_gt P.rN_pos) (ne_of_gt P.rM_pos), alphaFin_eq]
  ring

/-- The mass scaling: `ρ(M)^{-m} = (ρ_min(D)^{-m})^{d_box}`. -/
lemma mass_scaling (m : ℝ) :
    (P.rM) ^ (-m) = (P.rD ^ (-m)) ^ P.dbox := by
  have h := rpow_scale (A := (P.rM)⁻¹) (s := P.rD) (inv_pos.2 P.rM_pos) P.rD_pos
    (ne_of_gt P.log_rD_pos) m
  rw [Real.inv_rpow (le_of_lt P.rM_pos), ← Real.rpow_neg (le_of_lt P.rM_pos),
    Real.log_inv] at h
  rw [h]
  congr 1
  unfold dbox
  ring

/--
The parabolic (time) scaling at finite-born points:
`(ρ(M)/ρ(N))^n = ((ρ(M)ρ(Ψ))^{-n})^{-d_box(1-1/d_deg)/d_walk}`.
-/
lemma time_scaling_fin (n : ℝ) :
    (P.rM / P.rN) ^ n = ((P.rM * P.rPsi) ^ (-n)) ^ (-(P.alphaFin / P.dwalk)) := by
  have hs : 0 < P.rM * P.rPsi := mul_pos P.rM_pos P.hrPsi
  have h := rpow_scale (A := P.rM / P.rN) (s := P.rM * P.rPsi)
    (div_pos P.rM_pos P.rN_pos) hs (ne_of_gt P.log_rMPsi_pos) n
  rw [h]
  congr 1
  rw [Real.log_div (ne_of_gt P.rM_pos) (ne_of_gt P.rN_pos), alphaFin_eq]
  unfold dwalk
  have hD : log P.rD ≠ 0 := ne_of_gt P.log_rD_pos
  have hMP : log (P.rM * P.rPsi) ≠ 0 := ne_of_gt P.log_rMPsi_pos
  field_simp

/--
The parabolic (time) scaling at infinite-born points:
`ρ(M)^n = ((ρ(M)ρ(Ψ))^{-n})^{-d_box/d_walk}`.
-/
lemma time_scaling_inf (n : ℝ) :
    (P.rM) ^ n = ((P.rM * P.rPsi) ^ (-n)) ^ (-(P.dbox / P.dwalk)) := by
  have hs : 0 < P.rM * P.rPsi := mul_pos P.rM_pos P.hrPsi
  have h := rpow_scale (A := P.rM) (s := P.rM * P.rPsi) P.rM_pos hs
    (ne_of_gt P.log_rMPsi_pos) n
  rw [h]
  congr 1
  unfold dbox dwalk
  have hD : log P.rD ≠ 0 := ne_of_gt P.log_rD_pos
  have hMP : log (P.rM * P.rPsi) ≠ 0 := ne_of_gt P.log_rMPsi_pos
  field_simp

/--
The exponent occurring in the logarithmic correction:
`log ρ(N) / log (ρ(M)/ρ(N)) = 1/(d_deg - 1)`.
-/
lemma log_ratio_eq_inv_ddeg_sub_one :
    log P.rN / log (P.rM / P.rN) = 1 / (P.ddeg - 1) := by
  rw [Real.log_div (ne_of_gt P.rM_pos) (ne_of_gt P.rN_pos)]
  unfold ddeg
  have hN : log P.rN ≠ 0 := ne_of_gt P.log_rN_pos
  have h : log P.rM - log P.rN ≠ 0 := sub_ne_zero.mpr (ne_of_gt P.log_rN_lt_log_rM)
  field_simp

/--
The **logarithmic exponent of Lemma "heat-volume"**, `1/(d_deg - 1)`.

This is the exponent of the current version of the paper: the volume upper bound
at `μ`-almost every infinite-born point is `C|log r|^{1/(d_deg-1)+ε}r^{d_box}`,
and correspondingly the on-diagonal heat-kernel lower bound carries the factor
`|log t|^{-1/(d_deg-1)-ε}`.  The paper explains it as the large-deviation rate of
the age of the nearest terminal.
-/
noncomputable def logExp : ℝ := 1 / (P.ddeg - 1)

/--
The logarithmic exponent produced by the route of Hambly–Kumagai (radius strictly
below the cell scale, so that the ball avoids the skeleton altogether):
`d_deg/(d_deg - 1)`.  For the DHL it equals `2`.
-/
noncomputable def logExpHK : ℝ := P.ddeg / (P.ddeg - 1)

lemma ddeg_sub_one_pos : 0 < P.ddeg - 1 := by linarith [P.ddeg_one_lt]

lemma logExp_pos : 0 < P.logExp := div_pos zero_lt_one P.ddeg_sub_one_pos

/-- The two logarithmic exponents differ by exactly `1`. -/
lemma logExpHK_eq : P.logExpHK = P.logExp + 1 := by
  unfold logExpHK logExp
  have h : P.ddeg - 1 ≠ 0 := ne_of_gt P.ddeg_sub_one_pos
  field_simp
  ring

/--
**The sharpening claimed in the discussion after Theorem "diffusion-heat"**: the
exponent obtained by keeping the radius at the cell scale is strictly smaller
than the one obtained by staying inside a single cell.
-/
lemma logExp_lt_logExpHK : P.logExp < P.logExpHK := by
  rw [P.logExpHK_eq]; linarith

/--
The exponent produced by the choice `L_m = ⌈(1+ε)log m/log(ρ(M)/ρ(N))⌉`, namely
`(1+ε)/(d_deg-1)`, is the paper's `1/(d_deg-1) + ε'` after the calibration
`ε = ε'(d_deg-1)`.  (Both forms describe the same family of estimates as the
parameter ranges over the positive reals.)
-/
lemma calibrated_exponent (eps : ℝ) :
    (1 + eps * (P.ddeg - 1)) / (P.ddeg - 1) = P.logExp + eps := by
  unfold logExp
  have h : P.ddeg - 1 ≠ 0 := ne_of_gt P.ddeg_sub_one_pos
  field_simp

end Params

end Sec33
end IGS
