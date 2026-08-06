import RequestProject.Section33.GeneralLower

/-!
# Section 3.3: the diamond hierarchical lattice, and a non-vacuity check

The example closing §3.3 of arXiv:2603.13798 is the one-colour EIGS generating
the diamond hierarchical lattice, for which

`ρ(M) = 4`, `ρ(N) = 2`, `ρ(Ψ) = 1`, `ρ_min(D) = 2`,

so that `d_box = 2`, `d_deg = 2`, `d_R = 0`, `d_walk = 2` and the two on-diagonal
exponents of Theorem "diffusion-heat" are

`d_box(1-1/d_deg)/d_walk = 1/2`  and  `d_box/d_walk = 1`,

with logarithmic correction of exponent `1/(d_deg-1) + ε = 1 + ε`.  This file
verifies all of that, derives the two spectral dimensions `1` and `2` from the
general theorems, and checks that the hypotheses of the volume lemma are
satisfiable (so that the results of this section are not vacuous).

The logarithmic exponent `1 + ε` is the one of the current version of the paper;
the route of Hambly–Kumagai, which keeps the ball inside a single cell, gives
instead `d_deg/(d_deg-1) = 2`, so the estimate here is a genuine sharpening
(`dhl_log_exponent_lt_HK`).
-/

namespace IGS
namespace Sec33

open Real Filter Topology

/-- The parameters of the diamond hierarchical lattice. -/
noncomputable def dhl : Params where
  rM := 4
  rN := 2
  rPsi := 1
  rD := 2
  hrD := by norm_num
  hrN := by norm_num
  hrNM := by norm_num
  hrPsi := by norm_num
  hrMPsi := by norm_num

lemma log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]
  push_cast
  ring

lemma dhl_dbox : dhl.dbox = 2 := by
  unfold Params.dbox
  show Real.log 4 / Real.log 2 = 2
  rw [log_four]
  field_simp

lemma dhl_ddeg : dhl.ddeg = 2 := by
  unfold Params.ddeg
  show Real.log 4 / Real.log 2 = 2
  rw [log_four]
  field_simp

lemma dhl_dR : dhl.dR = 0 := by
  unfold Params.dR
  show Real.log 1 / Real.log 2 = 0
  simp

lemma dhl_dwalk : dhl.dwalk = 2 := by
  unfold Params.dwalk
  show Real.log (4 * 1) / Real.log 2 = 2
  rw [show (4:ℝ) * 1 = 4 by ring, log_four]
  field_simp

lemma dhl_alphaFin : dhl.alphaFin = 1 := by
  unfold Params.alphaFin
  rw [dhl_dbox, dhl_ddeg]
  norm_num

/-- The finite-born on-diagonal exponent of the DHL is `1/2`. -/
lemma dhl_exponent_finite : dhl.alphaFin / dhl.dwalk = 1 / 2 := by
  rw [dhl_alphaFin, dhl_dwalk]

/-- The infinite-born on-diagonal exponent of the DHL is `1`. -/
lemma dhl_exponent_infinite : dhl.dbox / dhl.dwalk = 1 := by
  rw [dhl_dbox, dhl_dwalk]
  norm_num

/-- The logarithmic exponent of the DHL: `1/(d_deg - 1) = 1`. -/
lemma dhl_log_exponent : dhl.logExp = 1 := by
  unfold Params.logExp
  rw [dhl_ddeg]
  norm_num

/-- The logarithmic exponent of the Hambly–Kumagai route for the DHL:
`d_deg/(d_deg - 1) = 2`. -/
lemma dhl_log_exponent_HK : dhl.logExpHK = 2 := by
  unfold Params.logExpHK
  rw [dhl_ddeg]
  norm_num

/-- For the DHL the exponent of Lemma "heat-volume" is strictly better than the
one of the Hambly–Kumagai route: `1 < 2`. -/
lemma dhl_log_exponent_lt_HK : dhl.logExp < dhl.logExpHK := dhl.logExp_lt_logExpHK

/--
**The DHL example, finite-born case.**
`c t^{-1/2} ≤ p_t(x,x) ≤ C t^{-1/2}` gives local spectral dimension `1`.
-/
theorem dhl_spectral_finite (pdiag : ℝ → ℝ) {c C t₀ : ℝ}
    (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 < t₀)
    (hlow : ∀ t ∈ Set.Ioo (0:ℝ) t₀, c * t ^ (-(1/2 : ℝ)) ≤ pdiag t)
    (hup : ∀ t ∈ Set.Ioo (0:ℝ) t₀, pdiag t ≤ C * t ^ (-(1/2 : ℝ))) :
    Tendsto (fun t => -2 * Real.log (pdiag t) / Real.log t) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have h := dhl.spectral_dim_finite_born pdiag hc hC ht₀
    (by rw [dhl_exponent_finite]; exact hlow) (by rw [dhl_exponent_finite]; exact hup)
  rw [show dhl.dbox * (1 - 1 / dhl.ddeg) / dhl.dwalk = dhl.alphaFin / dhl.dwalk from rfl,
    dhl_exponent_finite] at h
  simpa using h

/--
**The DHL example, almost-every infinite-born case** (Example 3.26 of the current
version): `c |log t|^{-1-ε} t^{-1} ≤ p_t(x,x) ≤ C t^{-1}` gives local spectral
dimension `2`.
-/
theorem dhl_spectral_infinite (pdiag : ℝ → ℝ) {c C t₀ eps : ℝ}
    (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 < t₀)
    (hlow : ∀ t ∈ Set.Ioo (0:ℝ) t₀,
      c * |Real.log t| ^ (-(dhl.logExp + eps)) * t ^ (-(1 : ℝ)) ≤ pdiag t)
    (hup : ∀ t ∈ Set.Ioo (0:ℝ) t₀, pdiag t ≤ C * t ^ (-(1 : ℝ))) :
    Tendsto (fun t => -2 * Real.log (pdiag t) / Real.log t) (𝓝[>] (0:ℝ)) (𝓝 2) := by
  have h := dhl.spectral_dim_infinite_born (theta := dhl.logExp + eps) pdiag hc hC ht₀
    (by rw [dhl_exponent_infinite]; exact hlow) (by rw [dhl_exponent_infinite]; exact hup)
  rw [dhl_exponent_infinite] at h
  simpa using h

/--
The same statement with the logarithmic exponent written out: for the DHL the
lower bound of Theorem "diffusion-heat" at a typical infinite-born point reads
`c|log t|^{-1-ε}t^{-1}`.
-/
theorem dhl_spectral_infinite' (pdiag : ℝ → ℝ) {c C t₀ eps : ℝ}
    (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 < t₀)
    (hlow : ∀ t ∈ Set.Ioo (0:ℝ) t₀,
      c * |Real.log t| ^ (-(1 + eps)) * t ^ (-(1 : ℝ)) ≤ pdiag t)
    (hup : ∀ t ∈ Set.Ioo (0:ℝ) t₀, pdiag t ≤ C * t ^ (-(1 : ℝ))) :
    Tendsto (fun t => -2 * Real.log (pdiag t) / Real.log t) (𝓝[>] (0:ℝ)) (𝓝 2) :=
  dhl_spectral_infinite pdiag hc hC ht₀ (by rwa [dhl_log_exponent]) hup

/--
**Non-vacuity of Lemma "heat-volume".**
The hypotheses of `Params.volume_finite_born` are satisfiable: for the DHL
parameters and the volume function `vol r = r` (the correct behaviour at a
finite-born point, since `d_box(1-1/d_deg) = 1`), the geometric input holds with
`c_l = 1/2` and `c_u = 1`, and the conclusion is the two-sided bound
`r/2 ≤ vol r ≤ 2 r`.
-/
theorem dhl_volume_nonvacuous :
    ∀ r : ℝ, 0 < r → r ≤ dhl.rD ^ (-((0 : ℕ) : ℝ)) →
      (1/2 : ℝ) * dhl.rN ^ (-((0:ℕ) : ℝ)) * r ^ dhl.alphaFin ≤ r ∧
      r ≤ (1:ℝ) * dhl.rN ^ (-((0:ℕ) : ℝ)) * dhl.rD ^ dhl.alphaFin * r ^ dhl.alphaFin := by
  refine dhl.volume_finite_born (fun r => r) 0 (1/2) 1 (by norm_num) (by norm_num) ?_
  intro m _ r hr0 hm1 hm2
  have hgeom : dhl.rN ^ ((m : ℝ) - (0:ℕ)) * dhl.rM ^ (-(m : ℝ)) = dhl.rD ^ (-(m : ℝ)) := by
    show (2:ℝ) ^ ((m : ℝ) - (0:ℕ)) * (4:ℝ) ^ (-(m : ℝ)) = (2:ℝ) ^ (-(m : ℝ))
    rw [show (4:ℝ) = (2:ℝ) ^ (2:ℝ) by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num]
    rw [← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    push_cast
    ring_nf
  rw [hgeom]
  constructor
  · -- `2^{-(m+1)} < r` gives `(1/2) 2^{-m} ≤ r`
    have hhalf : (1/2 : ℝ) * (2:ℝ) ^ (-(m : ℝ)) = (2:ℝ) ^ (-((m : ℝ) + 1)) := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num),
        Real.rpow_add (by norm_num), Real.rpow_one]
      have h2 : (0:ℝ) < (2:ℝ) ^ (m : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
      field_simp
    show (1/2 : ℝ) * dhl.rD ^ (-(m : ℝ)) ≤ r
    show (1/2 : ℝ) * (2:ℝ) ^ (-(m : ℝ)) ≤ r
    rw [hhalf]
    exact le_of_lt hm1
  · show r ≤ 1 * (2:ℝ) ^ (-(m : ℝ))
    rw [one_mul]
    exact hm2


/--
**Non-vacuity of the Nash-type upper bound.**
All the hypotheses of `Params.finite_born_on_diagonal_upper` can be met
simultaneously with a *non-zero* function `q`: take the DHL parameters, a
constant `q ≡ 1`, vanishing energy, `κ = 2`, `K = 0`, `c_deg = 1`, `d_n = 1`,
`k = n = 0` and `t = 1` (so `T_0 = 1 ≤ t ≤ ρ(M)ρ(Ψ)T_0 = 4`); the theorem then
gives the displayed bound, whose right-hand side is `4^{1/2} = 2`.
-/
theorem dhl_nash_upper_nonvacuous :
    (1:ℝ) ≤ (2 / 2 * (1 + 0) * ((1:ℝ)⁻¹ * dhl.rN ^ ((0:ℕ) : ℝ))
        * (dhl.rM * dhl.rPsi) ^ (dhl.alphaFin / dhl.dwalk))
      * (1:ℝ) ^ (-(dhl.alphaFin / dhl.dwalk)) :=
  dhl.finite_born_on_diagonal_upper (fun _ => (1:ℝ)) (fun _ => (0:ℝ))
    (t := 1) (kappa := 2) (K := 0) (cdeg := 1) (dn := 1) (k := 0) (n := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x => by norm_num)
    (fun a b _ _ => le_refl 1)
    (fun s => le_refl 0)
    (by simp)
    (by simp)
    (by norm_num)
    (by simp)
    (by simp [Params.Tscale, dhl])
    (by norm_num [Params.Tscale, dhl])
    (by intro s hs; simp [dhl])

end Sec33
end IGS
