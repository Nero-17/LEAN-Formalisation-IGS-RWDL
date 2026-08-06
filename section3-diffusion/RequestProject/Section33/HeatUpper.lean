import RequestProject.Section33.Exponents

/-!
# Section 3.3, step 5: the on-diagonal upper bounds

This file formalises the arguments the paper gives for the *upper* bounds of
Proposition "heat-kernel" and Theorem "diffusion-heat" of arXiv:2603.13798.

Two things happen there.

* **The exponent bookkeeping.**  Every estimate is first obtained at the
  parabolic scale `T_n = (ρ(M)ρ(Ψ))^{-n}` of a level-`n` cell, in the geometric
  form `q(t) ≲ ρ(M)^n` (global bound) resp. `q(t) ≲ (ρ(M)/ρ(N))^n`
  (finite-born bound), for `T_n ≤ t < T_{n-1}`.  `power_of_geometric` converts
  such a statement into the stated power of `t`; the two instances are
  `global_upper_of_geometric` (exponent `d_box/d_walk`) and
  `finite_born_upper_of_geometric` (exponent `d_box(1-1/d_deg)/d_walk`).

* **The Nash-type iteration at a finite-born point.**  Replacing `u_s = p_s(x,·)`
  by its harmonic interpolant on each of the `d_n ≍ ρ(N)^{n-k}` level-`n` cells
  incident to `x` gives, through
  `‖h‖² ≤ 2‖u_s‖² + 2‖u_s-h‖²`, the inequality
  `q(s)² ≲ (ρ(M)^n/d_n)(q(2s) + T_n ℰ(u_s,u_s))`  (`nash_step`);
  choosing `s ∈ [t/2,t]` with `ℰ(u_s,u_s) ≤ q(t)/t` (`exists_small_energy`, a
  genuine mean-value argument) and `n` with `T_n ≤ t < T_{n-1}` turns this into
  `q(t) ≲ ρ(M)^n/d_n` (`nash_chain`).

The inputs the paper quotes — the Poincaré/eigenvalue estimate on a prototype
cell, the mass of a harmonic profile, the degree growth `d_n ≍ ρ(N)^{n-k}`, and
the multiscale Nash argument of Hambly–Kumagai behind the global bound — are
hypotheses.
-/

namespace IGS
namespace Sec33

open Real MeasureTheory

namespace Params

variable (P : Params)

/-- `T_n = (ρ(M)ρ(Ψ))^{-n}`, the parabolic time scale of a level-`n` cell. -/
noncomputable def Tscale (n : ℝ) : ℝ := (P.rM * P.rPsi) ^ (-n)

lemma Tscale_pos (n : ℝ) : 0 < P.Tscale n :=
  Real.rpow_pos_of_pos (mul_pos P.rM_pos P.hrPsi) _

/--
**From a geometric bound at scale `n` to a power of `t`.**
If `A = T_n^{-β}` with `β ≥ 0` and `t < T_{n-1} = (ρ(M)ρ(Ψ)) T_n`, then
`A ≤ (ρ(M)ρ(Ψ))^β t^{-β}`.
-/
theorem power_of_geometric {beta A t : ℝ} {n : ℝ} (hbeta : 0 ≤ beta) (ht : 0 < t)
    (hA : A = (P.Tscale n) ^ (-beta))
    (htn : t ≤ (P.rM * P.rPsi) * P.Tscale n) :
    A ≤ (P.rM * P.rPsi) ^ beta * t ^ (-beta) := by
  have hs : 0 < P.rM * P.rPsi := mul_pos P.rM_pos P.hrPsi
  have hT : 0 < P.Tscale n := P.Tscale_pos n
  have hlow : t / (P.rM * P.rPsi) ≤ P.Tscale n := by
    rw [div_le_iff₀ hs]
    linarith [htn, mul_comm (P.rM * P.rPsi) (P.Tscale n)]
  have hdivpos : 0 < t / (P.rM * P.rPsi) := div_pos ht hs
  have hmono : (P.Tscale n) ^ (-beta) ≤ (t / (P.rM * P.rPsi)) ^ (-beta) :=
    Real.rpow_le_rpow_of_nonpos hdivpos hlow (neg_nonpos.2 hbeta)
  have hSb : (0:ℝ) < (P.rM * P.rPsi) ^ beta := Real.rpow_pos_of_pos hs beta
  have hsplit : (t / (P.rM * P.rPsi)) ^ (-beta) = (P.rM * P.rPsi) ^ beta * t ^ (-beta) := by
    rw [Real.div_rpow (le_of_lt ht) (le_of_lt hs), Real.rpow_neg (le_of_lt hs)]
    field_simp
  rw [hA, ← hsplit]
  exact hmono

/--
**Proposition "heat-kernel", exponent bookkeeping.**
A global bound `q(t) ≤ Cu ρ(M)^n` valid for `T_n ≤ t < T_{n-1}` is exactly the
stated bound `q(t) ≤ Cu (ρ(M)ρ(Ψ))^{d_box/d_walk} t^{-d_box/d_walk}`.
-/
theorem global_upper_of_geometric {Cu t : ℝ} {n : ℕ} (hCu : 0 ≤ Cu) (ht : 0 < t)
    (htn : t ≤ (P.rM * P.rPsi) * P.Tscale (n : ℝ)) {qt : ℝ}
    (hq : qt ≤ Cu * P.rM ^ (n : ℝ)) :
    qt ≤ Cu * (P.rM * P.rPsi) ^ (P.dbox / P.dwalk) * t ^ (-(P.dbox / P.dwalk)) := by
  have hbeta : 0 ≤ P.dbox / P.dwalk := le_of_lt (div_pos P.dbox_pos P.dwalk_pos)
  have hid : P.rM ^ (n : ℝ) = (P.Tscale (n : ℝ)) ^ (-(P.dbox / P.dwalk)) :=
    P.time_scaling_inf (n : ℝ)
  have h := P.power_of_geometric (beta := P.dbox / P.dwalk) (A := P.rM ^ (n : ℝ))
    hbeta ht hid htn
  calc qt ≤ Cu * P.rM ^ (n : ℝ) := hq
    _ ≤ Cu * ((P.rM * P.rPsi) ^ (P.dbox / P.dwalk) * t ^ (-(P.dbox / P.dwalk))) :=
        mul_le_mul_of_nonneg_left h hCu
    _ = Cu * (P.rM * P.rPsi) ^ (P.dbox / P.dwalk) * t ^ (-(P.dbox / P.dwalk)) := by ring

/--
**Theorem "diffusion-heat", finite-born exponent bookkeeping.**
A bound `q(t) ≤ Cu (ρ(M)/ρ(N))^n` valid for `T_n ≤ t < T_{n-1}` is the stated
bound with exponent `d_box(1-1/d_deg)/d_walk`.
-/
theorem finite_born_upper_of_geometric {Cu t : ℝ} {n : ℕ} (hCu : 0 ≤ Cu) (ht : 0 < t)
    (htn : t ≤ (P.rM * P.rPsi) * P.Tscale (n : ℝ)) {qt : ℝ}
    (hq : qt ≤ Cu * (P.rM / P.rN) ^ (n : ℝ)) :
    qt ≤ Cu * (P.rM * P.rPsi) ^ (P.alphaFin / P.dwalk)
      * t ^ (-(P.alphaFin / P.dwalk)) := by
  have hbeta : 0 ≤ P.alphaFin / P.dwalk := le_of_lt (div_pos P.alphaFin_pos P.dwalk_pos)
  have hid : (P.rM / P.rN) ^ (n : ℝ) = (P.Tscale (n : ℝ)) ^ (-(P.alphaFin / P.dwalk)) :=
    P.time_scaling_fin (n : ℝ)
  have h := P.power_of_geometric (beta := P.alphaFin / P.dwalk)
    (A := (P.rM / P.rN) ^ (n : ℝ)) hbeta ht hid htn
  calc qt ≤ Cu * (P.rM / P.rN) ^ (n : ℝ) := hq
    _ ≤ Cu * ((P.rM * P.rPsi) ^ (P.alphaFin / P.dwalk)
        * t ^ (-(P.alphaFin / P.dwalk))) := mul_le_mul_of_nonneg_left h hCu
    _ = Cu * (P.rM * P.rPsi) ^ (P.alphaFin / P.dwalk)
        * t ^ (-(P.alphaFin / P.dwalk)) := by ring

end Params

/--
**The mean-value choice of the time `s`.**
Since `∫_{t/2}^{t} ℰ(u_s,u_s) ds = (q(t) - q(2t))/2 ≤ q(t)/2`, some
`s ∈ [t/2,t]` satisfies `ℰ(u_s,u_s) ≤ q(t)/t`: a point where an integrable
function is at most its average.
-/
theorem exists_small_energy (En : ℝ → ℝ) (qt t : ℝ) (ht : 0 < t)
    (hint : IntegrableOn En (Set.Icc (t / 2) t))
    (hle : ∫ s in Set.Icc (t / 2) t, En s ≤ qt / 2) :
    ∃ s ∈ Set.Icc (t / 2) t, En s ≤ qt / t := by
  have hmeas : (volume (Set.Icc (t / 2) t)) = ENNReal.ofReal (t / 2) := by
    rw [Real.volume_Icc]
    congr 1
    ring
  have hne0 : volume (Set.Icc (t / 2) t) ≠ 0 := by
    rw [hmeas]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  have hnetop : volume (Set.Icc (t / 2) t) ≠ ⊤ := by
    rw [hmeas]; exact ENNReal.ofReal_ne_top
  obtain ⟨s, hs, hsle⟩ := exists_le_setAverage hne0 hnetop hint
  refine ⟨s, hs, le_trans hsle ?_⟩
  rw [setAverage_eq, Measure.real, hmeas, ENNReal.toReal_ofReal (by linarith)]
  rw [smul_eq_mul]
  have hpos : 0 < (t / 2)⁻¹ := by positivity
  calc (t / 2)⁻¹ * ∫ s in Set.Icc (t / 2) t, En s
      ≤ (t / 2)⁻¹ * (qt / 2) := by exact mul_le_mul_of_nonneg_left hle (le_of_lt hpos)
    _ = qt / t := by field_simp

/--
**The Nash step.**
`H = ‖h_{n,s}‖²`, `D = ‖u_s - h_{n,s}‖²`, `q2s = ‖u_s‖² = q(2s)`, `qs = u_s(x) = q(s)`.
From the three estimates of the paper,
`D ≤ K T_n ℰ`, `κ d_n ρ(M)^{-n} q(s)² ≤ H` and `H ≤ 2 q(2s) + 2 D`,
one gets `q(s)² ≤ (2/κ)(ρ(M)^n/d_n)(q(2s) + K T_n ℰ)`.
-/
theorem nash_step {kappa dn rMn K Tn En qs q2s D H : ℝ}
    (hkappa : 0 < kappa) (hdn : 0 < dn) (hrMn : 0 < rMn)
    (hD : D ≤ K * Tn * En)
    (hH1 : kappa * dn * rMn⁻¹ * qs ^ 2 ≤ H)
    (hH2 : H ≤ 2 * q2s + 2 * D) :
    qs ^ 2 ≤ (2 / kappa) * (rMn / dn) * (q2s + K * Tn * En) := by
  have hchain : kappa * dn * rMn⁻¹ * qs ^ 2 ≤ 2 * q2s + 2 * (K * Tn * En) := by
    linarith
  have hcoef : 0 < kappa * dn * rMn⁻¹ := by positivity
  have hmul : qs ^ 2 ≤ (2 * q2s + 2 * (K * Tn * En)) / (kappa * dn * rMn⁻¹) := by
    rw [le_div_iff₀ hcoef]
    linarith [hchain]
  refine le_trans hmul (le_of_eq ?_)
  field_simp

/-- If `q ≥ 0` and `q² ≤ A q` then `q ≤ A`. -/
theorem le_of_sq_le_mul {q A : ℝ} (hq : 0 ≤ q) (hA : 0 ≤ A) (h : q ^ 2 ≤ A * q) : q ≤ A := by
  rcases eq_or_lt_of_le hq with hq0 | hqpos
  · rw [← hq0]; exact hA
  · exact le_of_mul_le_mul_right (by nlinarith : q * q ≤ A * q) hqpos

/--
**The Nash chain.**
Feeding into `nash_step` the choice `s ∈ [t/2,t]` with `ℰ(u_s,u_s) ≤ q(t)/t`,
the monotonicity of `q` and `T_n ≤ t`, one obtains the geometric bound
`q(t) ≤ (2/κ)(1+K) ρ(M)^n/d_n`.
-/
theorem nash_chain (qfun En : ℝ → ℝ) (t s Tn ratio K kappa : ℝ)
    (ht : 0 < t) (hs : t / 2 ≤ s) (hst : s ≤ t)
    (hmono : ∀ a b : ℝ, 0 < a → a ≤ b → qfun b ≤ qfun a)
    (hq0 : ∀ x, 0 ≤ qfun x)
    (hK : 0 ≤ K) (hkappa : 0 < kappa) (hratio : 0 ≤ ratio)
    (hTn : Tn ≤ t) (hE0 : 0 ≤ En s) (hE : En s ≤ qfun t / t)
    (hnash : qfun s ^ 2 ≤ (2 / kappa) * ratio * (qfun (2 * s) + K * Tn * En s)) :
    qfun t ≤ (2 / kappa) * (1 + K) * ratio := by
  have hspos : 0 < s := by linarith
  have hqts : qfun t ≤ qfun s := hmono s t hspos hst
  have hq2s : qfun (2 * s) ≤ qfun t := hmono t (2 * s) ht (by linarith)
  have hEbound : K * Tn * En s ≤ K * qfun t := by
    have h1 : Tn * En s ≤ t * (qfun t / t) :=
      mul_le_mul hTn hE hE0 (le_of_lt ht)
    have h2 : t * (qfun t / t) = qfun t := by field_simp
    rw [h2] at h1
    calc K * Tn * En s = K * (Tn * En s) := by ring
      _ ≤ K * qfun t := mul_le_mul_of_nonneg_left h1 hK
  have hcoef : 0 ≤ (2 / kappa) * ratio := by positivity
  have hstep : qfun t ^ 2 ≤ ((2 / kappa) * (1 + K) * ratio) * qfun t := by
    have h1 : qfun t ^ 2 ≤ qfun s ^ 2 := by
      have := hq0 t
      nlinarith [hqts, hq0 s]
    have h2 : qfun (2 * s) + K * Tn * En s ≤ (1 + K) * qfun t := by linarith
    calc qfun t ^ 2 ≤ qfun s ^ 2 := h1
      _ ≤ (2 / kappa) * ratio * (qfun (2 * s) + K * Tn * En s) := hnash
      _ ≤ (2 / kappa) * ratio * ((1 + K) * qfun t) :=
          mul_le_mul_of_nonneg_left h2 hcoef
      _ = ((2 / kappa) * (1 + K) * ratio) * qfun t := by ring
  refine le_of_sq_le_mul (hq0 t) ?_ hstep
  have : (0:ℝ) ≤ 1 + K := by linarith
  positivity

namespace Params

variable (P : Params)

/--
**The degree growth turns `ρ(M)^n/d_n` into `(ρ(M)/ρ(N))^n`.**
With `d_n ≥ c_deg ρ(N)^{n-k}` (the degree-growth estimate of §2 at a `k`-born
point) one has `ρ(M)^n/d_n ≤ c_deg^{-1}ρ(N)^{k}(ρ(M)/ρ(N))^n`.
-/
theorem ratio_le_of_degree_growth {cdeg dn : ℝ} (hcdeg : 0 < cdeg) (k n : ℕ)
    (hdn : cdeg * P.rN ^ ((n : ℝ) - k) ≤ dn) :
    P.rM ^ (n : ℝ) / dn ≤ cdeg⁻¹ * P.rN ^ (k : ℝ) * (P.rM / P.rN) ^ (n : ℝ) := by
  have hNn : (0:ℝ) < P.rN ^ ((n : ℝ) - k) := Real.rpow_pos_of_pos P.rN_pos _
  have hMn : (0:ℝ) < P.rM ^ (n : ℝ) := Real.rpow_pos_of_pos P.rM_pos _
  have h1 : P.rM ^ (n : ℝ) / dn ≤ P.rM ^ (n : ℝ) / (cdeg * P.rN ^ ((n : ℝ) - k)) :=
    div_le_div_of_nonneg_left (le_of_lt hMn) (by positivity) hdn
  refine le_trans h1 (le_of_eq ?_)
  rw [Real.div_rpow (le_of_lt P.rM_pos) (le_of_lt P.rN_pos),
    Real.rpow_sub P.rN_pos]
  have hNk : (0:ℝ) < P.rN ^ (k : ℝ) := Real.rpow_pos_of_pos P.rN_pos _
  have hNn' : (0:ℝ) < P.rN ^ (n : ℝ) := Real.rpow_pos_of_pos P.rN_pos _
  field_simp

/--
**The finite-born on-diagonal upper bound of Theorem "diffusion-heat".**

All the steps of the paper's argument are combined here: the mean-value choice of
`s ∈ [t/2,t]` with `ℰ(u_s,u_s) ≤ q(t)/t`, the Nash inequality on the `d_n` cells
incident to the `k`-born point `x`, the degree growth `d_n ≥ c_deg ρ(N)^{n-k}`
and the choice of the scale `n` with `T_n ≤ t ≤ (ρ(M)ρ(Ψ))T_n`.  The conclusion
is the stated bound `q(t) ≤ C t^{-d_box(1-1/d_deg)/d_walk}` with an explicit
constant.
-/
theorem finite_born_on_diagonal_upper (qfun En : ℝ → ℝ)
    {t kappa K cdeg dn : ℝ} {k n : ℕ}
    (ht : 0 < t) (hkappa : 0 < kappa) (hK : 0 ≤ K) (hcdeg : 0 < cdeg)
    (hq0 : ∀ x, 0 ≤ qfun x)
    (hmono : ∀ a b : ℝ, 0 < a → a ≤ b → qfun b ≤ qfun a)
    (hE0 : ∀ s, 0 ≤ En s)
    (hint : IntegrableOn En (Set.Icc (t / 2) t))
    (hEint : ∫ s in Set.Icc (t / 2) t, En s ≤ qfun t / 2)
    (hdn0 : 0 < dn) (hdn : cdeg * P.rN ^ ((n : ℝ) - k) ≤ dn)
    (hTn : P.Tscale (n : ℝ) ≤ t) (htn : t ≤ (P.rM * P.rPsi) * P.Tscale (n : ℝ))
    (hnash : ∀ s ∈ Set.Icc (t / 2) t,
      qfun s ^ 2 ≤ (2 / kappa) * (P.rM ^ (n : ℝ) / dn)
        * (qfun (2 * s) + K * P.Tscale (n : ℝ) * En s)) :
    qfun t ≤ ((2 / kappa) * (1 + K) * (cdeg⁻¹ * P.rN ^ (k : ℝ))
        * (P.rM * P.rPsi) ^ (P.alphaFin / P.dwalk)) * t ^ (-(P.alphaFin / P.dwalk)) := by
  obtain ⟨s, hs, hsE⟩ := exists_small_energy En (qfun t) t ht hint hEint
  have hratio0 : 0 ≤ P.rM ^ (n : ℝ) / dn :=
    le_of_lt (div_pos (Real.rpow_pos_of_pos P.rM_pos _) hdn0)
  have hchain := nash_chain qfun En t s (P.Tscale (n : ℝ)) (P.rM ^ (n : ℝ) / dn) K kappa
    ht hs.1 hs.2 hmono hq0 hK hkappa hratio0 hTn (hE0 s) hsE (hnash s hs)
  -- degree growth
  have hdeg := P.ratio_le_of_degree_growth hcdeg k n hdn
  have hcoef : (0:ℝ) ≤ (2 / kappa) * (1 + K) := by positivity
  have hgeo : qfun t ≤ ((2 / kappa) * (1 + K) * (cdeg⁻¹ * P.rN ^ (k : ℝ)))
      * (P.rM / P.rN) ^ (n : ℝ) := by
    refine le_trans hchain ?_
    calc (2 / kappa) * (1 + K) * (P.rM ^ (n : ℝ) / dn)
        ≤ (2 / kappa) * (1 + K) * (cdeg⁻¹ * P.rN ^ (k : ℝ) * (P.rM / P.rN) ^ (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hdeg hcoef
      _ = ((2 / kappa) * (1 + K) * (cdeg⁻¹ * P.rN ^ (k : ℝ))) * (P.rM / P.rN) ^ (n : ℝ) := by
          ring
  have hCu : (0:ℝ) ≤ (2 / kappa) * (1 + K) * (cdeg⁻¹ * P.rN ^ (k : ℝ)) := by
    have h1 : (0:ℝ) < P.rN ^ (k : ℝ) := Real.rpow_pos_of_pos P.rN_pos _
    have h2 : (0:ℝ) < cdeg⁻¹ := inv_pos.2 hcdeg
    positivity
  exact P.finite_born_upper_of_geometric hCu ht htn hgeo

end Params

end Sec33
end IGS
