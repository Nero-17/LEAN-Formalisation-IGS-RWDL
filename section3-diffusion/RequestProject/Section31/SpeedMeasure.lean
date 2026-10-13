import Mathlib

/-!
# §3.1, step 4: the speed measure (Lemma `sec31_speed_measure`)

Reference: arXiv:2603.13798, §3.1, Lemma `sec31_speed_measure`.

The lemma has two assertions.

**(a) Uniform cell bound.**  For every `m` there is `C_m` with
`π_n(V(Λ)) ≤ C_m ρ(M)^{-m}` for every level-`m` cell `Λ` and every `n ≥ m`,
where `π_n(x) = deg_{Ξⁿ}(x) / (2|E(Ξⁿ)|)`.  The proof is the degree count
`∑_{x ∈ V(Λ)} deg_{Ξⁿ}(x) = 2|E(Λ)| + O(deg(u₁) + deg(u₂))`
together with the three estimates of `basic_prop`:
`|E(Λ)| ≍ ρ(M)^{n-m}`, `|E(Ξⁿ)| ≍ ρ(M)^n`, `deg_{Ξⁿ}(u_i) ≲ ρ(N)^{n-m}`,
and `ρ(N) ≤ ρ(M)`.  This is `stationary_measure_cell_le`, proved here with an
explicit constant `C_m = (c₂ + D c₃)/c₁` which, notably, does not depend on `m`.

**(b) Weak convergence `π_n ⇒ μ_{Ξ_M}`.**  The same decomposition shows that on
each fixed level-`m` cell `π_n` and `μ_{Ξⁿ}` differ by `O((ρ(N)/ρ(M))^{n-m})`,
and `μ_{Ξⁿ} ⇒ μ_{Ξ_M}` is Lemma `GHP_convergence`.  The transfer step is
`weak_limit_transfer`: weak convergence is stable under perturbations whose
effect on every bounded continuous test function vanishes.  The input
`μ_{Ξⁿ} ⇒ μ_{Ξ_M}` and the cellwise comparison are hypotheses (the first is
Lemma `GHP_convergence`, the second the degree count above).
-/

namespace IGS.Sec31

open Filter Topology

/--
**Lemma `sec31_speed_measure` (a).**

`degSum` is `∑_{x ∈ V(Λ)} deg_{Ξⁿ}(x)` for a level-`m` cell `Λ` inside `Ξⁿ`
with `n = m + k`, `EL = |E(Λ)|`, `EXi = |E(Ξⁿ)|`, and `d₁, d₂` the degrees of the
two planting vertices.  Under the estimates of the paper,
`π_n(V(Λ)) = degSum / (2 |E(Ξⁿ)|) ≤ ((c₂ + D c₃)/c₁) ρ(M)^{-m}`.
-/
theorem stationary_measure_cell_le
    (rhoM rhoN : ℝ) (hM : 1 < rhoM) (hN0 : 0 ≤ rhoN) (hNM : rhoN ≤ rhoM)
    (m k : ℕ) (EL EXi d1 d2 degSum c1 c2 c3 D : ℝ)
    (hc1 : 0 < c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3) (hD : 0 ≤ D)
    (hEL : EL ≤ c2 * rhoM ^ k) (hEXi : c1 * rhoM ^ (m + k) ≤ EXi)
    (hd1 : d1 ≤ c3 * rhoN ^ k) (hd2 : d2 ≤ c3 * rhoN ^ k)
    (hdeg : degSum ≤ 2 * EL + D * (d1 + d2)) :
    degSum / (2 * EXi) ≤ (c2 + D * c3) / c1 * (rhoM ^ m)⁻¹ := by
  have hM0 : (0 : ℝ) < rhoM := by linarith
  have hA : (0 : ℝ) < rhoM ^ m := by positivity
  have hB : (0 : ℝ) < rhoM ^ k := by positivity
  have hCB : rhoN ^ k ≤ rhoM ^ k := pow_le_pow_left₀ hN0 hNM k
  have hEXipos : 0 < EXi := lt_of_lt_of_le (by positivity) hEXi
  have hstep1 : D * (d1 + d2) ≤ D * (2 * (c3 * rhoN ^ k)) := by
    have h : d1 + d2 ≤ 2 * (c3 * rhoN ^ k) := by linarith
    exact mul_le_mul_of_nonneg_left h hD
  have hstep2 : D * (2 * (c3 * rhoN ^ k)) ≤ D * (2 * (c3 * rhoM ^ k)) := by
    have h : c3 * rhoN ^ k ≤ c3 * rhoM ^ k := mul_le_mul_of_nonneg_left hCB hc3
    nlinarith
  have hnum : degSum ≤ 2 * (c2 + D * c3) * rhoM ^ k := by nlinarith
  rw [div_le_iff₀ (by positivity)]
  have hkey : (c2 + D * c3) / c1 * (rhoM ^ m)⁻¹ * (2 * (c1 * rhoM ^ (m + k)))
      = 2 * (c2 + D * c3) * rhoM ^ k := by
    rw [pow_add]; field_simp
  have hmono : (c2 + D * c3) / c1 * (rhoM ^ m)⁻¹ * (2 * (c1 * rhoM ^ (m + k)))
      ≤ (c2 + D * c3) / c1 * (rhoM ^ m)⁻¹ * (2 * EXi) := by
    have hpos : 0 ≤ (c2 + D * c3) / c1 * (rhoM ^ m)⁻¹ := by positivity
    nlinarith
  linarith [hkey ▸ hmono]

/--
The relative error between `π_n` and `μ_{Ξⁿ}` on a fixed cell is
`O((ρ(N)/ρ(M))^{n-m})`, which tends to `0` because `ρ(N) < ρ(M)`.
-/
theorem cell_error_tendsto_zero (rhoM rhoN : ℝ) (hN0 : 0 ≤ rhoN) (hNM : rhoN < rhoM)
    (hM0 : 0 < rhoM) :
    Tendsto (fun k : ℕ => (rhoN / rhoM) ^ k) atTop (𝓝 0) := by
  refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
  rw [div_lt_one hM0]
  exact hNM

/--
A difference which is dominated by a null sequence tends to `0`.
-/
theorem tendsto_sub_zero_of_bound (a b eps : ℕ → ℝ) (K : ℝ)
    (h : ∀ n, |a n - b n| ≤ K * eps n) (heps : Tendsto (fun n => K * eps n) atTop (𝓝 0)) :
    Tendsto (fun n => a n - b n) atTop (𝓝 0) :=
  squeeze_zero_norm (fun n => by simpa [Real.norm_eq_abs] using h n) heps

/--
**Lemma `sec31_speed_measure` (b): transfer of weak convergence.**

`I n f = ∫ f dμ_{Ξⁿ}`, `J n f = ∫ f dπ_n` and `L f = ∫ f dμ_{Ξ_M}`.  If
`μ_{Ξⁿ} ⇒ μ_{Ξ_M}` (Lemma `GHP_convergence`) and the two discrete measures give
asymptotically the same value to every bounded continuous test function, then
`π_n ⇒ μ_{Ξ_M}`.
-/
theorem weak_limit_transfer {X : Type*} [TopologicalSpace X]
    (I J : ℕ → C(X, ℝ) → ℝ) (L : C(X, ℝ) → ℝ)
    (hmu : ∀ f, Tendsto (fun n => I n f) atTop (𝓝 (L f)))
    (hdiff : ∀ f, Tendsto (fun n => J n f - I n f) atTop (𝓝 0)) :
    ∀ f, Tendsto (fun n => J n f) atTop (𝓝 (L f)) := by
  intro f
  have h := (hdiff f).add (hmu f)
  simpa using h

end IGS.Sec31
