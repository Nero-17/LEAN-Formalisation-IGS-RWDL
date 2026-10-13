import RequestProject.Section33.Main

/-!
# Section 3.3: Theorem "general-lower" in the form of the current version

The current version of §3.3 of arXiv:2603.13798 states the general on-diagonal
lower bound as

`p_t(x,x) ≥ c_x / μ(B(x, C_x t^{1/d_walk}))`,

that is, at time `t` rather than at time `2t`, and with the volume of the ball
appearing explicitly rather than through a power of `r`.  Its proof is:

1. the survival estimate `P_x(τ_{B(x,r)} > a_x r^{d_walk}) ≥ p_x`;
2. hence `P_x(W_t ∈ B(x,r)) ≥ p_x` as soon as `t ≤ a_x r^{d_walk}`
   (`prob_mem_of_exit_time`);
3. Cauchy–Schwarz and Chapman–Kolmogorov, i.e. Theorem "general-lower" as
   already formalised in `Section3.OnDiagonalLower`;
4. the choice `r = (t/a_x)^{1/d_walk}`, for which `t = a_x r^{d_walk}` exactly
   (`exit_radius_eq`).

Steps 2 and 4 are proved here, and step 3 is applied at time `t/2` so that the
conclusion is about `p_t(x,x)`; the radius conversion
`C(t/2)^{1/d_walk} = (C 2^{-1/d_walk}) t^{1/d_walk}` is `halved_radius`.

The file closes with the two lower bounds of Theorem "diffusion-heat" in the form
displayed in the current version:

* `p_t(x,x) ≥ c t^{-d_box(1-1/d_deg)/d_walk}` at a finite-born point;
* `p_t(x,x) ≥ c |log t|^{-1/(d_deg-1)-ε} t^{-d_box/d_walk}` at `μ`-almost every
  infinite-born point — note the logarithmic exponent `1/(d_deg-1)+ε`, which is
  the one produced by `Section33.VolumeAE.volume_upper_logExp`.
-/

namespace IGS
namespace Sec33

open Real MeasureTheory Metric

/--
**Step 2 of Theorem "general-lower".**  "If `t ≤ a_x r^{d_walk}`, then
`P_x(W_t ∈ B(x,r)) ≥ p_x`": the event that the exit time exceeds `a` is
contained in the event that it exceeds `t`, which in turn is contained in the
event that the path is inside the ball at time `t`.
-/
theorem prob_mem_of_exit_time {Omega : Type*} [MeasurableSpace Omega] (Pr : Measure Omega)
    (tau : Omega → ℝ) (A : Set Omega) {t a : ℝ} (hta : t ≤ a)
    (hsub : {om | t < tau om} ⊆ A) :
    Pr {om | a < tau om} ≤ Pr A := by
  refine measure_mono ?_
  intro om hom
  exact hsub (lt_of_le_of_lt hta hom)

namespace Params

variable (P : Params)

/--
**Step 4: the choice of the radius.**  With `r = (t/a)^{1/d_walk}` one has
`t = a r^{d_walk}` exactly, so the survival estimate applies at time `t`.
-/
lemma exit_radius_eq {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    a * ((t / a) ^ (1 / P.dwalk)) ^ P.dwalk = t := by
  have hdw : P.dwalk ≠ 0 := ne_of_gt P.dwalk_pos
  rw [← Real.rpow_mul (le_of_lt (div_pos ht ha)), one_div, inv_mul_cancel₀ hdw,
    Real.rpow_one]
  field_simp

/-- `C (t/2)^{1/d_walk} = (C 2^{-1/d_walk}) t^{1/d_walk}`. -/
lemma halved_radius (C : ℝ) {t : ℝ} (ht : 0 < t) :
    C * (t / 2) ^ (1 / P.dwalk) = (C * 2 ^ (-(1 / P.dwalk))) * t ^ (1 / P.dwalk) := by
  rw [Real.div_rpow (le_of_lt ht) (by norm_num), Real.rpow_neg (by norm_num)]
  field_simp

/--
**Theorem "general-lower" as stated in the current version of the paper.**

`p_t(x,x) ≥ p_x² / μ(B(x, C_x t^{1/d_walk}))`.  This is the Cauchy–Schwarz
argument of `Section3.OnDiagonalLower` applied at time `t/2`; the survival
estimate is therefore required at time `t/2` and radius `C_x t^{1/d_walk}`,
which by `halved_radius` is the same as the paper's radius `C(t/2)^{1/d_walk}`
after renaming the constant.
-/
theorem on_diagonal_lower_ball {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (p : ℝ → X → X → ℝ) (mu : Measure X) (x : X) {t Cx pstay : ℝ}
    (hpstay : 0 ≤ pstay)
    (hp0 : 0 ≤ᵐ[mu] fun y => p (t / 2) x y)
    (hmem : MemLp (fun y => p (t / 2) x y) 2 mu)
    (hball : mu (Metric.ball x (Cx * t ^ (1 / P.dwalk))) ≠ ⊤)
    (hballpos : 0 < (mu (Metric.ball x (Cx * t ^ (1 / P.dwalk)))).toReal)
    (hstay : pstay ≤ ∫ y in Metric.ball x (Cx * t ^ (1 / P.dwalk)), p (t / 2) x y ∂mu)
    (hCK : ∫ y, (p (t / 2) x y) ^ 2 ∂mu = p t x x) :
    pstay ^ 2 / (mu (Metric.ball x (Cx * t ^ (1 / P.dwalk)))).toReal ≤ p t x x := by
  have ht2 : 2 * (t / 2) = t := by ring
  have hCK' : ∫ y, (p (t / 2) x y) ^ 2 ∂mu = p (2 * (t / 2)) x x := by rw [ht2]; exact hCK
  have h := heat_kernel_on_diagonal_lower' p mu x (t / 2) (Cx * t ^ (1 / P.dwalk)) pstay
    hpstay hp0 hmem hball hballpos hstay hCK'
  rwa [ht2] at h

/--
**Theorem "diffusion-heat", lower bound at a finite-born point.**

Theorem "general-lower" in the form above, composed with the volume upper bound
`μ(B(x,r)) ≤ C_vol r^{d_box(1-1/d_deg)}` of Lemma "heat-volume", gives
`p_t(x,x) ≥ c t^{-d_box(1-1/d_deg)/d_walk}`.
-/
theorem heat_lower_finite_born {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (p : ℝ → X → X → ℝ) (mu : Measure X) (x : X) {t Cx Cvol pstay : ℝ}
    (hpstay : 0 < pstay) (hCx : 0 < Cx) (hCvol : 0 < Cvol) (ht : 0 < t)
    (hp0 : 0 ≤ᵐ[mu] fun y => p (t / 2) x y)
    (hmem : MemLp (fun y => p (t / 2) x y) 2 mu)
    (hball : mu (Metric.ball x (Cx * t ^ (1 / P.dwalk))) ≠ ⊤)
    (hstay : pstay ≤ ∫ y in Metric.ball x (Cx * t ^ (1 / P.dwalk)), p (t / 2) x y ∂mu)
    (hCK : ∫ y, (p (t / 2) x y) ^ 2 ∂mu = p t x x)
    (hvol : (mu (Metric.ball x (Cx * t ^ (1 / P.dwalk)))).toReal
      ≤ Cvol * (Cx * t ^ (1 / P.dwalk)) ^ P.alphaFin) :
    (pstay ^ 2 / (Cvol * Cx ^ P.alphaFin)) * t ^ (-(P.alphaFin / P.dwalk)) ≤ p t x x := by
  have ht2 : 2 * (t / 2) = t := by ring
  have hCK' : ∫ y, (p (t / 2) x y) ^ 2 ∂mu = p (2 * (t / 2)) x x := by rw [ht2]; exact hCK
  have hlower := heat_kernel_on_diagonal_lower p mu x (t / 2) (Cx * t ^ (1 / P.dwalk)) pstay
    (le_of_lt hpstay) hp0 hmem hball hstay hCK'
  rw [ht2] at hlower
  exact P.on_diagonal_lower_of_volume (fun _ => p t x x)
    (fun _ => (mu (Metric.ball x (Cx * t ^ (1 / P.dwalk)))).toReal) (t := t)
    hpstay hCx hCvol ht ENNReal.toReal_nonneg hlower hvol

/--
**Theorem "diffusion-heat", lower bound at `μ`-almost every infinite-born
point**, with the logarithmic exponent of the current version.

The volume bound `μ(B(x,r)) ≤ C_vol |log r|^{1/(d_deg-1)+ε} r^{d_box}` of
Lemma "heat-volume" (`Params.volume_upper_logExp`) gives

`p_t(x,x) ≥ c |log t|^{-1/(d_deg-1)-ε} t^{-d_box/d_walk}`.
-/
theorem heat_lower_infinite_born {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (p : ℝ → X → X → ℝ) (mu : Measure X) (x : X) {t Cx Cvol pstay eps : ℝ}
    (hpstay : 0 < pstay) (hCx : 0 < Cx) (hCvol : 0 < Cvol) (heps : 0 ≤ eps)
    (ht : 0 < t) (hte : t ≤ Real.exp (-1))
    (hp0 : 0 ≤ᵐ[mu] fun y => p (t / 2) x y)
    (hmem : MemLp (fun y => p (t / 2) x y) 2 mu)
    (hball : mu (Metric.ball x (Cx * t ^ (1 / P.dwalk))) ≠ ⊤)
    (hstay : pstay ≤ ∫ y in Metric.ball x (Cx * t ^ (1 / P.dwalk)), p (t / 2) x y ∂mu)
    (hCK : ∫ y, (p (t / 2) x y) ^ 2 ∂mu = p t x x)
    (hvol : (mu (Metric.ball x (Cx * t ^ (1 / P.dwalk)))).toReal
      ≤ Cvol * |Real.log (Cx * t ^ (1 / P.dwalk))| ^ (P.logExp + eps)
        * (Cx * t ^ (1 / P.dwalk)) ^ P.dbox) :
    (pstay ^ 2 / (Cvol * (|Real.log Cx| + 1 / P.dwalk) ^ (P.logExp + eps) * Cx ^ P.dbox))
      * |Real.log t| ^ (-(P.logExp + eps)) * t ^ (-(P.dbox / P.dwalk)) ≤ p t x x := by
  have ht2 : 2 * (t / 2) = t := by ring
  have hCK' : ∫ y, (p (t / 2) x y) ^ 2 ∂mu = p (2 * (t / 2)) x x := by rw [ht2]; exact hCK
  have hlower := heat_kernel_on_diagonal_lower p mu x (t / 2) (Cx * t ^ (1 / P.dwalk)) pstay
    (le_of_lt hpstay) hp0 hmem hball hstay hCK'
  rw [ht2] at hlower
  have htheta : 0 ≤ P.logExp + eps := by linarith [P.logExp_pos]
  exact P.on_diagonal_lower_of_volume_log (fun _ => p t x x)
    (fun _ => (mu (Metric.ball x (Cx * t ^ (1 / P.dwalk)))).toReal) (t := t)
    hpstay hCx hCvol htheta ht hte ENNReal.toReal_nonneg hlower hvol

end Params

end Sec33
end IGS
