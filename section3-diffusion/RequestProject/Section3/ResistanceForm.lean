import Mathlib

/-!
# Section 3, step 6: two elementary steps of the resistance-form subsection

Subsection 3.2 of *Iterated Graph Systems (I)* (arXiv:2603.13798) builds a
resistance form on `Ξ_M` out of the compatible finite traces `ℰ_m^W`.  Two steps
of that construction are pure real analysis and are proved here.

* `tendsto_traced_energy` : trace compatibility makes `m ↦ ℰ_m^W(f|_{V(Ξ^m)})`
  non-decreasing, so on the domain `ℱ_𝒱` (where it is bounded) the limit
  `ℰ_𝒱(f,f) := lim_m ℰ_m^W(f,f)` exists and equals the supremum.  This is the
  first sentence of the proof of Theorem "sec32_resistance_metric".

* `harmonic_spline_error_tendsto_zero` : the estimate
  `|u(x) - P_m^R u(x)|² ≤ C ρ(Ψ)^{-m} ℰ_R(u,u)` of Lemma "sec32_common_core"
  forces `u - P_m^R u → 0` uniformly, because `ρ(Ψ) > 1`.

Everything specific to graphs, forms or measures is again outside the file: the
input is a real sequence with the stated monotonicity / decay.
-/

namespace IGS

open Filter Topology

/--
**Compatible traces have a limit.**
If `E : ℕ → ℝ` is non-decreasing (trace compatibility) and bounded above
(membership in the domain `ℱ_𝒱`), then `E m` converges to `⨆ m, E m`.
-/
theorem tendsto_traced_energy (E : ℕ → ℝ) (hmono : Monotone E) (hbdd : BddAbove (Set.range E)) :
    Tendsto E atTop (𝓝 (⨆ m, E m)) :=
  tendsto_atTop_ciSup hmono hbdd

/--
**Uniform decay of the harmonic-spline error.**
If `err m ≥ 0` and `err m ^ 2 ≤ C * (ρ ^ m)⁻¹ * E` with `ρ > 1`, then `err m → 0`.
-/
theorem harmonic_spline_error_tendsto_zero (err : ℕ → ℝ) (rho C E : ℝ) (hrho : 1 < rho)
    (herr0 : ∀ m, 0 ≤ err m)
    (hbound : ∀ m, err m ^ 2 ≤ C * (rho ^ m)⁻¹ * E) :
    Tendsto err atTop (𝓝 0) := by
  have hpow : Tendsto (fun m : ℕ => ((rho ^ m)⁻¹ : ℝ)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hrho)
  have hmaj : Tendsto (fun m : ℕ => Real.sqrt (C * (rho ^ m)⁻¹ * E)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => C * (rho ^ m)⁻¹ * E) atTop (𝓝 0) := by
      have := (hpow.const_mul C).mul_const E
      simpa using this
    have := (Real.continuous_sqrt.tendsto 0).comp h1
    simpa using this
  refine squeeze_zero herr0 (fun m => ?_) hmaj
  have h := hbound m
  have hsq : Real.sqrt (err m ^ 2) ≤ Real.sqrt (C * (rho ^ m)⁻¹ * E) :=
    Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (herr0 m)] at hsq

end IGS
