import Mathlib

/-!
# §3, preamble to §3.1: cell masses and finite-born points
(Lemma `GHP_convergence`)

Reference: arXiv:2603.13798, §3, Lemma `GHP_convergence`.

Lemma `GHP_convergence` states that the normalised counting measures
`μ_{Ξⁿ}` converge weakly to a Borel probability measure `μ_{Ξ_M}`, that every
level-`m` cell has mass `≍ ρ(M)^{-m}`, and that *every finite-born point is a
null set*.  The last assertion is the one §3.1 (and, later, the dichotomy of
§3.3) really uses, and it is proved as follows: a point `x ∈ 𝒱` of birth level
`k` has a level-`m` star neighbourhood made of at most `C ρ(N)^{m-k}` level-`m`
cells, each of mass `≤ C' ρ(M)^{-m}`; since `ρ(N) < ρ(M)`, the mass of the star
tends to `0`, and `μ({x})` is below all of these bounds, hence `0`.

Both steps are proved here (`star_mass_tendsto_zero`,
`eq_zero_of_le_geometric`).  The scalar Perron recursion behind
`μ(Λ) ≍ ρ(M)^{-m}` is in `RequestProject.Section3.Recursions`.
-/

namespace IGS.Sec31

open Filter Topology

/--
**Strictness of `ρ(N) < ρ(M)` (the counting argument of Lemma `GHP_convergence`).**

The degree of a vertex of birth level `k` in `Ξⁿ` grows like `ρ(N)^{n-k}`, and
the number of `k`-born vertices grows like `ρ(M)^k`; summing over birth levels
bounds `2|E(Ξⁿ)| ≍ ρ(M)^n` from below by `c Σ_{k ≤ n} ρ(M)^k ρ(N)^{n-k}`.  If
`ρ(N)` were equal to `ρ(M)`, that sum would be `(n+1)ρ(M)^n`, which is not
`O(ρ(M)^n)`.  Hence the inequality `ρ(N) ≤ ρ(M)` is automatically strict.
-/
theorem rN_lt_rM_of_edge_bound {rM rN c C : ℝ} (hM : 0 < rM) (hNM : rN ≤ rM) (hc : 0 < c)
    (hbound : ∀ n : ℕ,
      c * ∑ k ∈ Finset.range (n + 1), rM ^ k * rN ^ (n - k) ≤ C * rM ^ n) :
    rN < rM := by
  rcases lt_or_eq_of_le hNM with h | h
  · exact h
  · exfalso
    -- with `ρ(N) = ρ(M)` each of the `n+1` terms equals `ρ(M)^n`
    have hsum : ∀ n : ℕ,
        ∑ k ∈ Finset.range (n + 1), rM ^ k * rN ^ (n - k) = (n + 1 : ℕ) * rM ^ n := by
      intro n
      have : ∀ k ∈ Finset.range (n + 1), rM ^ k * rN ^ (n - k) = rM ^ n := by
        intro k hk
        simp only [Finset.mem_range] at hk
        rw [← h, ← pow_add]
        congr 1
        omega
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range]
      simp [mul_comm]
    have hMn : ∀ n : ℕ, (0:ℝ) < rM ^ n := fun n => pow_pos hM n
    have hlin : ∀ n : ℕ, c * (n + 1 : ℕ) ≤ C := by
      intro n
      have h1 := hbound n
      rw [hsum n] at h1
      have h2 : c * ((n + 1 : ℕ) : ℝ) * rM ^ n ≤ C * rM ^ n := by
        calc c * ((n + 1 : ℕ) : ℝ) * rM ^ n = c * (((n + 1 : ℕ) : ℝ) * rM ^ n) := by ring
          _ ≤ C * rM ^ n := h1
      exact le_of_mul_le_mul_right (by linarith [h2]) (hMn n)
    obtain ⟨n, hn⟩ := exists_nat_gt (C / c)
    have := hlin n
    have hcn : C / c < ((n : ℝ) + 1) := by linarith
    rw [div_lt_iff₀ hc] at hcn
    push_cast at this
    linarith

/--
**The mass of the level-`m` star of a finite-born point of birth level `k`.**
It is at most `C ρ(N)^{m-k} · C' ρ(M)^{-m}`, which for `m = k + j` equals
`(C C' ρ(M)^{-k}) (ρ(N)/ρ(M))^j` and tends to `0` because `ρ(N) < ρ(M)`.
-/
theorem star_mass_tendsto_zero (rhoM rhoN C C' : ℝ) (k : ℕ)
    (hN0 : 0 ≤ rhoN) (hM0 : 0 < rhoM) (hNM : rhoN < rhoM) :
    Tendsto (fun j : ℕ => C * rhoN ^ j * (C' * (rhoM ^ (k + j))⁻¹)) atTop (𝓝 0) := by
  have hq : (0 : ℝ) ≤ rhoN / rhoM := by positivity
  have hq1 : rhoN / rhoM < 1 := by rw [div_lt_one hM0]; exact hNM
  have hgeo : Tendsto (fun j : ℕ => (rhoN / rhoM) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1
  have h := hgeo.const_mul (C * C' * (rhoM ^ k)⁻¹)
  rw [mul_zero] at h
  refine h.congr fun j => ?_
  have hMk : (rhoM ^ k : ℝ) ≠ 0 := by positivity
  have hMj : (rhoM ^ j : ℝ) ≠ 0 := by positivity
  rw [div_pow, pow_add]
  field_simp

/--
**A nonnegative number below a null geometric sequence is `0`.**
Applied to `μ({x})`, which is bounded by the mass of every level-`m` star, this
gives `μ_{Ξ_M}({x}) = 0` for every finite-born point `x`.
-/
theorem eq_zero_of_le_geometric (mass K q : ℝ) (hmass : 0 ≤ mass) (hq0 : 0 ≤ q) (hq : q < 1)
    (hbound : ∀ j : ℕ, mass ≤ K * q ^ j) : mass = 0 := by
  have hlim : Tendsto (fun j : ℕ => K * q ^ j) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).const_mul K
    simpa using h
  have hle : mass ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hbound)
  linarith

end IGS.Sec31
