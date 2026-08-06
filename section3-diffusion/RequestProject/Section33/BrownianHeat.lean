import RequestProject.Section33.Main

/-!
# Section 3.3, last step: Corollary 3.27 and Theorem 3.28

The paper closes §3.3 by transporting the heat-kernel estimates of
Theorem 3.23 ("diffusion-heat") and the spectral dimensions of Theorem 3.24
("diffusion-spectral") from the diffusion `W` — whose heat kernel is `p_t` — to
the Brownian motion of the resistance form `(ℰ_R, ℱ_R)`, whose heat kernel is
`q_t`.  The bridge is Theorem 3.18 ("sec32_brownian_motion", formalised in
`RequestProject/Section32`): *if* `dim_R(Ξ) > 0`, the two processes coincide as
`L²(Ξ_M, μ)`-processes, hence `q_t(x,y) = p_t(x,y)` for all `t > 0`.

That identification is the only input, and it is the one the paper itself
quotes; here it appears as the explicit hypothesis

`hqp : 0 < P.dR → ∀ t, 0 < t → q t = p t`,

which is stated exactly under the paper's standing assumption `dim_R(Ξ) > 0`
of this part of the section (the assumption is therefore genuinely used).
Everything else — the transfer of the two-sided bounds, of the limits defining
the spectral dimensions, and the final Einstein-relation identity

`2 dim_B/dim_W = 2 (dim_B/dim_R)/(1 + dim_B/dim_R)`

— is proved.

* `brownian_heat_finite_born`, `brownian_heat_infinite_born` : **Corollary 3.27**.
* `brownian_spectral_eq_diffusion`, `brownian_spectral_finite_born`,
  `brownian_spectral_infinite_born`, `spectral_infinite_eq_resistance_ratio` :
  **Theorem 3.28**.
-/

namespace IGS
namespace Sec33

open Real Filter Topology

namespace Params

variable (P : Params)

/-- `dim_R(Ξ) > 0` is exactly the Brownian regime `ρ(Ψ) > 1` (Remark 3.29). -/
lemma dR_pos_iff_one_lt_rPsi : 0 < P.dR ↔ 1 < P.rPsi := by
  unfold dR
  rw [div_pos_iff_of_pos_right P.log_rD_pos]
  exact Real.log_pos_iff P.hrPsi.le

/-- In the Brownian regime the walk dimension exceeds the box dimension. -/
lemma dbox_lt_dwalk_of_dR_pos (h : 0 < P.dR) : P.dbox < P.dwalk := by
  rw [P.dwalk_eq_dbox_add_dR]; linarith

/-!
## Corollary 3.27

The on-diagonal estimates for `q_t`, at a finite-born point and at
`μ`-almost every infinite-born point.
-/

/--
**Corollary 3.27, finite-born case.**
Under `dim_R(Ξ) > 0`, the two-sided bound of Theorem 3.23 for the diffusion heat
kernel `p` transfers verbatim to the Brownian heat kernel `q`:
`c_x t^{-dim_B(1-1/dim_D)/dim_W} ≤ q_t(x,x) ≤ C_x t^{-dim_B(1-1/dim_D)/dim_W}`.
-/
theorem brownian_heat_finite_born (p q : ℝ → ℝ) {c C t₀ : ℝ}
    (hdR : 0 < P.dR)
    (hqp : 0 < P.dR → ∀ t, 0 < t → q t = p t)
    (hlow : ∀ t ∈ Set.Ioo (0:ℝ) t₀, c * t ^ (-(P.alphaFin / P.dwalk)) ≤ p t)
    (hup : ∀ t ∈ Set.Ioo (0:ℝ) t₀, p t ≤ C * t ^ (-(P.alphaFin / P.dwalk))) :
    ∀ t ∈ Set.Ioo (0:ℝ) t₀,
      c * t ^ (-(P.alphaFin / P.dwalk)) ≤ q t ∧
        q t ≤ C * t ^ (-(P.alphaFin / P.dwalk)) := by
  intro t ht
  rw [hqp hdR t ht.1]
  exact ⟨hlow t ht, hup t ht⟩

/--
**Corollary 3.27, almost-every infinite-born case.**
Under `dim_R(Ξ) > 0`, the logarithmically corrected lower bound and the
polynomial upper bound of Theorem 3.23 transfer to `q`:
`c |log t|^{-1/(dim_D-1)-ε} t^{-dim_B/dim_W} ≤ q_t(x,x) ≤ C t^{-dim_B/dim_W}`.
-/
theorem brownian_heat_infinite_born (p q : ℝ → ℝ) {c C t₀ eps : ℝ}
    (hdR : 0 < P.dR)
    (hqp : 0 < P.dR → ∀ t, 0 < t → q t = p t)
    (hlow : ∀ t ∈ Set.Ioo (0:ℝ) t₀,
      c * |Real.log t| ^ (-(P.logExp + eps)) * t ^ (-(P.dbox / P.dwalk)) ≤ p t)
    (hup : ∀ t ∈ Set.Ioo (0:ℝ) t₀, p t ≤ C * t ^ (-(P.dbox / P.dwalk))) :
    ∀ t ∈ Set.Ioo (0:ℝ) t₀,
      c * |Real.log t| ^ (-(P.logExp + eps)) * t ^ (-(P.dbox / P.dwalk)) ≤ q t ∧
        q t ≤ C * t ^ (-(P.dbox / P.dwalk)) := by
  intro t ht
  rw [hqp hdR t ht.1]
  exact ⟨hlow t ht, hup t ht⟩

end Params

/-!
## Theorem 3.28

The Brownian spectral dimension equals the diffusion spectral dimension, and
both are given by the formulas of Theorem 3.24.
-/

/--
Two heat kernels which agree at all positive times have the same local spectral
dimension, whenever one of the two limits exists.  This is the whole content of
the first sentence of the proof of Theorem 3.28.
-/
theorem tendsto_spectral_congr (p q : ℝ → ℝ) {L : ℝ}
    (hqp : ∀ t, 0 < t → q t = p t)
    (h : Tendsto (fun t => -2 * Real.log (p t) / Real.log t) (𝓝[>] (0:ℝ)) (𝓝 L)) :
    Tendsto (fun t => -2 * Real.log (q t) / Real.log t) (𝓝[>] (0:ℝ)) (𝓝 L) := by
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [hqp t ht]

namespace Params

variable (P : Params)

/--
**Theorem 3.28, equality of the two spectral dimensions.**
Under `dim_R(Ξ) > 0` the identification `q_t = p_t` of Theorem 3.18 gives
`dim_S^{(R)}(Ξ_M : x) = dim_S^{(N)}(Ξ_M : x)` wherever the limit exists.
-/
theorem brownian_spectral_eq_diffusion (p q : ℝ → ℝ) {L : ℝ}
    (hdR : 0 < P.dR)
    (hqp : 0 < P.dR → ∀ t, 0 < t → q t = p t)
    (h : Tendsto (fun t => -2 * Real.log (p t) / Real.log t) (𝓝[>] (0:ℝ)) (𝓝 L)) :
    Tendsto (fun t => -2 * Real.log (q t) / Real.log t) (𝓝[>] (0:ℝ)) (𝓝 L) :=
  tendsto_spectral_congr p q (hqp hdR) h

/--
**Theorem 3.28, finite-born case.**
For every `x ∈ 𝒱`, `dim_S^{(R)}(Ξ_M : x) = dim_S^{(N)}(Ξ_M : x)
= 2 dim_B(1 - 1/dim_D)/dim_W`.
-/
theorem brownian_spectral_finite_born (p q : ℝ → ℝ) {c C t₀ : ℝ}
    (hdR : 0 < P.dR)
    (hqp : 0 < P.dR → ∀ t, 0 < t → q t = p t)
    (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 < t₀)
    (hlow : ∀ t ∈ Set.Ioo (0:ℝ) t₀, c * t ^ (-(P.alphaFin / P.dwalk)) ≤ p t)
    (hup : ∀ t ∈ Set.Ioo (0:ℝ) t₀, p t ≤ C * t ^ (-(P.alphaFin / P.dwalk))) :
    Tendsto (fun t => -2 * Real.log (q t) / Real.log t) (𝓝[>] (0:ℝ))
      (𝓝 (2 * (P.dbox * (1 - 1 / P.ddeg) / P.dwalk))) ∧
    Tendsto (fun t => -2 * Real.log (p t) / Real.log t) (𝓝[>] (0:ℝ))
      (𝓝 (2 * (P.dbox * (1 - 1 / P.ddeg) / P.dwalk))) := by
  have hp := P.spectral_dim_finite_born p hc hC ht₀ hlow hup
  exact ⟨P.brownian_spectral_eq_diffusion p q hdR hqp hp, hp⟩

/--
**Theorem 3.28, almost-every infinite-born case.**
For `μ`-almost every `x ∈ V^∞`, `dim_S^{(R)}(Ξ_M : x) = dim_S^{(N)}(Ξ_M : x)
= 2 dim_B/dim_W`.
-/
theorem brownian_spectral_infinite_born (p q : ℝ → ℝ) {c C t₀ theta : ℝ}
    (hdR : 0 < P.dR)
    (hqp : 0 < P.dR → ∀ t, 0 < t → q t = p t)
    (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 < t₀)
    (hlow : ∀ t ∈ Set.Ioo (0:ℝ) t₀,
      c * |Real.log t| ^ (-theta) * t ^ (-(P.dbox / P.dwalk)) ≤ p t)
    (hup : ∀ t ∈ Set.Ioo (0:ℝ) t₀, p t ≤ C * t ^ (-(P.dbox / P.dwalk))) :
    Tendsto (fun t => -2 * Real.log (q t) / Real.log t) (𝓝[>] (0:ℝ))
      (𝓝 (2 * (P.dbox / P.dwalk))) ∧
    Tendsto (fun t => -2 * Real.log (p t) / Real.log t) (𝓝[>] (0:ℝ))
      (𝓝 (2 * (P.dbox / P.dwalk))) := by
  have hp := P.spectral_dim_infinite_born p hc hC ht₀ hlow hup
  exact ⟨P.brownian_spectral_eq_diffusion p q hdR hqp hp, hp⟩

/--
**Theorem 3.28, the final identity.**
By the Einstein relation `dim_W = dim_B + dim_R`, the infinite-born spectral
dimension can be rewritten in terms of the single ratio `dim_B/dim_R`:
`2 dim_B/dim_W = 2 (dim_B/dim_R)/(1 + dim_B/dim_R)`.
-/
theorem spectral_infinite_eq_resistance_ratio (hdR : 0 < P.dR) :
    2 * P.dbox / P.dwalk = 2 * (P.dbox / P.dR) / (1 + P.dbox / P.dR) := by
  have hbox : 0 < P.dbox := P.dbox_pos
  have hne : P.dR ≠ 0 := ne_of_gt hdR
  have hsum : (0:ℝ) < 1 + P.dbox / P.dR := by positivity
  rw [P.dwalk_eq_dbox_add_dR]
  field_simp
  ring

/--
The same identity, read as a strict upper bound: in the Brownian regime the
infinite-born spectral dimension is `< 2` (Proposition 3.25 revisited).
-/
theorem spectral_infinite_lt_two (hdR : 0 < P.dR) : 2 * P.dbox / P.dwalk < 2 :=
  P.spectral_lt_two_iff.2 hdR

end Params

end Sec33
end IGS
