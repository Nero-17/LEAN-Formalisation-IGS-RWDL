import Mathlib

/-!
# §3.1, step 3: the harmonic projection tail
(Lemmas `sec31_projection_tail_continuous` and `sec31_projection_tail_discrete`)

Reference: arXiv:2603.13798, §3.1.

Both lemmas say the same thing on the two sides of the approximation (the limit
space with `μ_{Ξ_M}`, and the level-`n` graph with `π_n`):

* the harmonic projection is *orthogonal* for the energy form, so
  `ℰ(u,u) = ℰ(u_m,u_m) + ℰ(u - u_m, u - u_m)` (Euler–Lagrange);
* the projection error decays in `L²`:
  `‖u - u_m‖₂² ≤ C (ρ(M) ρ(Ψ))^{-m} ℰ(u,u)`.

The second point is proved by writing `u - u_m = ∑_{ℓ ≥ m} d_ℓ`, where `d_ℓ` is
the increment between two consecutive coarse levels.  On a level-`ℓ` cell the
increment vanishes at the two terminals and lies in a fixed finite-dimensional
prototype space, so its cellwise supremum is bounded by the cellwise energy
divided by the level-`ℓ` conductance scale `ρ(Ψ)^{ℓ}`; each cell has mass
`≍ ρ(M)^{-ℓ}` (Lemma `GHP_convergence` / Lemma `sec31_speed_measure`), whence
`‖d_ℓ‖₂² ≤ C q^ℓ ℰ(u,u)` with `q := (ρ(M) ρ(Ψ))^{-1} < 1`.  Summing the
geometric series in `ℓ ≥ m` gives the claim.

Here the *cellwise* estimate `‖d_ℓ‖₂² ≤ C q^ℓ ℰ` is the hypothesis (it is the
finite-dimensional norm equivalence over the compact family of traced
conductance vectors, which the paper also only sketches), and the summation —
the part that produces the exponent `m` — is proved.
-/

namespace IGS.Sec31

open Filter Topology

/--
`√(q^l) = (√q)^l`, an auxiliary step for the geometric summation.
-/
theorem sqrt_pow_nat (q : ℝ) (hq : 0 ≤ q) (l : ℕ) : Real.sqrt (q ^ l) = Real.sqrt q ^ l := by
  induction l with
  | zero => simp
  | succ k ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

/--
**Energy orthogonality (Euler–Lagrange for the harmonic projection).**
If the harmonic projection `p` of `u` is energy-orthogonal to the error `u - p`,
then `ℰ(u,u) = ℰ(p,p) + ℰ(u-p, u-p)`.  Here `ℰ` is realised as the squared norm
of a real inner-product space.
-/
theorem energy_pythagoras {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u p : H) (h : inner ℝ p (u - p) = (0 : ℝ)) :
    ‖u‖ ^ 2 = ‖p‖ ^ 2 + ‖u - p‖ ^ 2 := by
  have hu : u = p + (u - p) := by abel
  nth_rewrite 1 [hu]
  rw [norm_add_sq_real, h]
  ring

/--
**Geometric summation of the level increments.**
If the increments satisfy `d ℓ ≤ √(C q^ℓ E)` then their tail sum from level `m`
is at most `√(C E) (√q)^m / (1 - √q)`.
-/
theorem tsum_increments_le (C E q : ℝ) (hC : 0 ≤ C) (hE : 0 ≤ E) (hq0 : 0 ≤ q) (hq : q < 1)
    (d : ℕ → ℝ) (hd0 : ∀ l, 0 ≤ d l) (hd : ∀ l, d l ≤ Real.sqrt (C * q ^ l * E)) (m : ℕ) :
    ∑' l : ℕ, d (m + l) ≤ Real.sqrt (C * E) * Real.sqrt q ^ m / (1 - Real.sqrt q) := by
  have hsq : Real.sqrt q < 1 := by simpa using Real.sqrt_lt_sqrt hq0 hq
  have hsq0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have key : ∀ l : ℕ, d (m + l) ≤ Real.sqrt (C * E) * Real.sqrt q ^ m * Real.sqrt q ^ l := by
    intro l
    refine (hd (m + l)).trans_eq ?_
    rw [show C * q ^ (m + l) * E = (C * E) * q ^ (m + l) by ring, Real.sqrt_mul (by positivity),
      sqrt_pow_nat q hq0, pow_add]
    ring
  have hsummable : Summable fun l : ℕ => Real.sqrt (C * E) * Real.sqrt q ^ m * Real.sqrt q ^ l :=
    (summable_geometric_of_lt_one hsq0 hsq).mul_left _
  have hd_summable : Summable fun l : ℕ => d (m + l) :=
    hsummable.of_nonneg_of_le (fun l => hd0 _) key
  calc ∑' l : ℕ, d (m + l)
      ≤ ∑' l : ℕ, Real.sqrt (C * E) * Real.sqrt q ^ m * Real.sqrt q ^ l :=
        Summable.tsum_mono hd_summable hsummable key
    _ = Real.sqrt (C * E) * Real.sqrt q ^ m * (1 - Real.sqrt q)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hsq0 hsq]
    _ = Real.sqrt (C * E) * Real.sqrt q ^ m / (1 - Real.sqrt q) := by ring

/--
**Lemma `sec31_projection_tail_continuous` / `sec31_projection_tail_discrete`.**

Let `N m := ‖u - u_m‖₂` be the `L²` error of the level-`m` harmonic projection,
let `d ℓ` be the `L²` norm of the level-`ℓ` increment, and suppose

* `N m ≤ ∑_{l} d (m + l)` (triangle inequality for the telescoping series),
* `d ℓ ≤ √(C q^ℓ E)` with `q = (ρ(M) ρ(Ψ))⁻¹ < 1` and `E = ℰ(u,u)`.

Then `N m ² ≤ C' q^m E` with the explicit constant
`C' = C / (1 - √q)²`, i.e. `‖u - u_m‖₂² ≤ C' (ρ(M) ρ(Ψ))^{-m} ℰ(u,u)`.
-/
theorem projection_tail_sq_bound (C E q : ℝ) (hC : 0 ≤ C) (hE : 0 ≤ E) (hq0 : 0 ≤ q) (hq : q < 1)
    (d : ℕ → ℝ) (hd0 : ∀ l, 0 ≤ d l) (hd : ∀ l, d l ≤ Real.sqrt (C * q ^ l * E))
    (N : ℕ → ℝ) (hN0 : ∀ m, 0 ≤ N m) (hN : ∀ m, N m ≤ ∑' l : ℕ, d (m + l)) (m : ℕ) :
    N m ^ 2 ≤ C / (1 - Real.sqrt q) ^ 2 * q ^ m * E := by
  have hsq : Real.sqrt q < 1 := by simpa using Real.sqrt_lt_sqrt hq0 hq
  have h1 : (0 : ℝ) < 1 - Real.sqrt q := by linarith
  have hbound := (hN m).trans (tsum_increments_le C E q hC hE hq0 hq d hd0 hd m)
  have hs2 : Real.sqrt (C * E) ^ 2 = C * E := Real.sq_sqrt (by positivity)
  have hq2 : (Real.sqrt q ^ m) ^ 2 = q ^ m := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hq0]
  calc N m ^ 2 ≤ (Real.sqrt (C * E) * Real.sqrt q ^ m / (1 - Real.sqrt q)) ^ 2 :=
        pow_le_pow_left₀ (hN0 m) hbound 2
    _ = C / (1 - Real.sqrt q) ^ 2 * q ^ m * E := by
        rw [div_pow, mul_pow, hs2, hq2]; ring

/--
The ratio `q = (ρ(M) ρ(Ψ))⁻¹` really is `< 1` in the situation of the paper,
where `ρ(M) > 1` is the growth rate of the graphs and `ρ(Ψ) > 0`,
`ρ(M) ρ(Ψ) > 1` (which holds as soon as the resistance dimension is
non-negative).
-/
theorem ratio_lt_one (rhoM rhoPsi : ℝ) (h : 1 < rhoM * rhoPsi) : (rhoM * rhoPsi)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ h

end IGS.Sec31
