import Mathlib

/-!
# Section 3, step 2: the two elementary recursions used in §3

Two scalar recursions carry a real part of the work in Section 3 of
*Iterated Graph Systems (I)* (arXiv:2603.13798).  Both are stated here in a
self-contained way, with no graph-theoretic input.

* `bounded_of_affine_contraction` is the induction behind the uniform bound
  `R_*(z, a_Λ) ≤ C_∂ ρ(Ψ)^{-m}` (Lemma "sec32_point_boundary"): the normalised
  quantities `A_L` obey `A_{L+1} ≤ ρ^{-1} A_L + B` with `ρ = ρ(Ψ) > 1`, and this
  alone forces `sup_L A_L < ∞`.

* `affine_recursion_closed_form` / `vertex_ratio_tendsto` are the one-colour
  (scalar) form of the Perron–Frobenius computation in Lemma "GHP_convergence":
  the vertex counts satisfy `u(ℓ+1) = ρ u(ℓ) + b`, hence `u(ℓ) ∼ κ ρ^ℓ`, and the
  relative mass of a level-`m` cell inside `Ξ^n` converges to `ρ^{-m}` as
  `n → ∞`.  This is exactly the statement `μ(Λ) ≍ ρ(M)^{-m}` in the scalar case.
-/

namespace IGS

open Filter Topology

/--
**Uniform bound from an affine contraction.**
If `ρ > 1` and `A (L+1) ≤ ρ⁻¹ * A L + B` for all `L`, then the whole sequence is
bounded by `max (A 0) (B * ρ / (ρ - 1))`.
-/
theorem bounded_of_affine_contraction (A : ℕ → ℝ) (rho B : ℝ) (hrho : 1 < rho)
    (hrec : ∀ L, A (L + 1) ≤ rho⁻¹ * A L + B) :
    ∀ L, A L ≤ max (A 0) (B * rho / (rho - 1)) := by
  have hrho0 : 0 < rho := lt_trans zero_lt_one hrho
  have hsub : 0 < rho - 1 := by linarith
  set K := max (A 0) (B * rho / (rho - 1)) with hK
  have hKB : B * rho / (rho - 1) ≤ K := le_max_right _ _
  have hstep : rho⁻¹ * K + B ≤ K := by
    have h1 : B * rho ≤ K * (rho - 1) := by
      rw [div_le_iff₀ hsub] at hKB
      linarith
    have h2 : rho⁻¹ * K + B - K = (B * rho - K * (rho - 1)) / rho := by
      field_simp
      ring
    have : rho⁻¹ * K + B - K ≤ 0 := by
      rw [h2]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hrho0.le
    linarith
  intro L
  induction L with
  | zero => exact le_max_left _ _
  | succ n ih =>
      have hinv : (0 : ℝ) ≤ rho⁻¹ := by positivity
      calc A (n + 1) ≤ rho⁻¹ * A n + B := hrec n
        _ ≤ rho⁻¹ * K + B := by nlinarith
        _ ≤ K := hstep

/--
**Closed form of the affine vertex-count recursion.**
`u (ℓ+1) = ρ u ℓ + b` with `ρ > 1` gives `u ℓ = (u 0 + β) ρ^ℓ - β`,
where `β = b / (ρ - 1)`.
-/
theorem affine_recursion_closed_form (u : ℕ → ℝ) (rho b : ℝ) (hrho : 1 < rho)
    (hrec : ∀ l, u (l + 1) = rho * u l + b) :
    ∀ l, u l = (u 0 + b / (rho - 1)) * rho ^ l - b / (rho - 1) := by
  have hsub : (0 : ℝ) < rho - 1 := by linarith
  intro l
  induction l with
  | zero => simp
  | succ n ih =>
      rw [hrec n, ih]
      field_simp
      ring

/--
**Relative mass of a level-`m` cell.**
With `u` as above and `κ := u 0 + b/(ρ-1) > 0`, the proportion of the vertices of
`Ξ^{k+m}` that lie in a fixed level-`m` cell tends to `ρ^{-m}` as `k → ∞`.
-/
theorem vertex_ratio_tendsto (u : ℕ → ℝ) (rho b : ℝ) (hrho : 1 < rho)
    (hrec : ∀ l, u (l + 1) = rho * u l + b)
    (hkappa : 0 < u 0 + b / (rho - 1)) (m : ℕ) :
    Tendsto (fun k => u k / u (k + m)) atTop (𝓝 ((rho ^ m)⁻¹)) := by
  have hrho0 : (0 : ℝ) < rho := lt_trans zero_lt_one hrho
  set kappa := u 0 + b / (rho - 1) with hkap
  set beta := b / (rho - 1) with hbeta
  have hclosed := affine_recursion_closed_form u rho b hrho hrec
  have hpowpos : ∀ k : ℕ, (0 : ℝ) < rho ^ k := fun k => pow_pos hrho0 k
  -- limit of the rewritten quotient
  have hinvpow : Tendsto (fun k : ℕ => ((rho ^ k)⁻¹ : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (rho ^ k : ℝ)) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hrho
    exact tendsto_inv_atTop_zero.comp h1
  have hden : (kappa * rho ^ m - beta * 0) ≠ 0 := by
    have : (0 : ℝ) < kappa * rho ^ m := by positivity
    simpa using ne_of_gt this
  have hlim : Tendsto
      (fun k : ℕ => (kappa - beta * (rho ^ k)⁻¹) / (kappa * rho ^ m - beta * (rho ^ k)⁻¹))
      atTop (𝓝 ((kappa - beta * 0) / (kappa * rho ^ m - beta * 0))) := by
    exact (tendsto_const_nhds.sub (hinvpow.const_mul beta)).div
      (tendsto_const_nhds.sub (hinvpow.const_mul beta)) hden
  have hval : (kappa - beta * 0) / (kappa * rho ^ m - beta * 0) = (rho ^ m)⁻¹ := by
    have hk : kappa ≠ 0 := ne_of_gt hkappa
    simp only [mul_zero, sub_zero]
    field_simp
  rw [hval] at hlim
  refine hlim.congr ?_
  intro k
  have hk : (rho ^ k : ℝ) ≠ 0 := ne_of_gt (hpowpos k)
  have h1 : u k = kappa * rho ^ k - beta := hclosed k
  have h2 : u (k + m) = kappa * rho ^ (k + m) - beta := hclosed (k + m)
  rw [h1, h2, pow_add]
  have hEq : kappa * rho ^ m - beta * (rho ^ k)⁻¹
      = (kappa * (rho ^ k * rho ^ m) - beta) * (rho ^ k)⁻¹ := by
    field_simp
  rcases eq_or_ne (kappa * (rho ^ k * rho ^ m) - beta) 0 with h | h
  · simp only [hEq, h, zero_mul, div_zero]
  · field_simp

/--
**Recurrence criterion (algebraic part of Proposition "final_recurrent").**
Given the Einstein relation `d_s = 2 d_f / (d_f + d_R)` with `d_f > 0` and
`d_f + d_R > 0`, one has `d_s < 2` if and only if the resistance dimension `d_R`
is strictly positive.
-/
theorem spectral_lt_two_iff_resistance_pos (df dR : ℝ) (hsum : 0 < df + dR) :
    2 * df / (df + dR) < 2 ↔ 0 < dR := by
  rw [div_lt_iff₀ hsum]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

end IGS
