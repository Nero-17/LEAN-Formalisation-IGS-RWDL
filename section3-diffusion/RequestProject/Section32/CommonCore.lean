import Mathlib
import RequestProject.Section3.ResistanceForm

/-!
# §3.2, step 4: Lemma `sec32_common_core`

*Iterated Graph Systems (I)* (arXiv:2603.13798), Lemma `sec32_common_core`:
the union over all levels of the continuous harmonic splines is a form core for
the `L²(Ξ_M, μ)` realisation of the resistance form `(ℰ_R, ℱ_R)`.

The paper's proof has two halves, and both are formalised here.

1. *Density in the form norm.*  Trace theory identifies the `ℰ_R`-orthogonal
   complement of the level-`m` spline subspace with the functions whose trace on
   `V(Ξ^m)` vanishes.  A function orthogonal to every level therefore vanishes
   on `𝒱`; being of finite energy it is continuous in the resistance topology,
   which by Theorem `sec32_resistance_metric` is the natural topology, and `𝒱`
   is dense, so the function is `0`.  A subspace of a Hilbert space with trivial
   orthogonal complement is dense.  This is `spline_core_dense`, whose two
   inputs (the trace identification, and continuity/injectivity of the
   evaluation map) are hypotheses, exactly as in the paper.

2. *Density in `L²`.*  The pointwise estimate
   `|u(x) - P_m^R u(x)|² ≤ ℰ_R(u-P_m^Ru) R_{ℰ_R}(x, a_Λ) ≤ C_∂ρ(Ψ)^{-m}ℰ_R(u,u)`
   (Lemma `sec32_point_boundary`, plus the Pythagoras inequality for the
   harmonic projection) forces `‖u - P_m^R u‖_{L²(μ)} → 0` for a probability
   measure `μ`.  This is `spline_error_pointwise`, `spline_error_L2_le` and
   `spline_error_L2_tendsto`.
-/

namespace IGS.Sec32

open Filter Topology MeasureTheory

section Pointwise

variable {X : Type*}

/--
**The pointwise estimate of Lemma `sec32_common_core`.**
If `(u x - v x)² ≤ Q * R x` pointwise (continuity of a finite-energy function in
the resistance metric), `Q ≤ E` (Pythagoras for the harmonic projection) and
`R x ≤ C` (Lemma `sec32_point_boundary`), then `(u x - v x)² ≤ E * C`.
-/
theorem spline_error_pointwise {u v : X → ℝ} {R : X → ℝ} {Q E C : ℝ}
    (hQ0 : 0 ≤ Q) (hQE : Q ≤ E) (hR0 : ∀ x, 0 ≤ R x) (hRC : ∀ x, R x ≤ C)
    (hpt : ∀ x, (u x - v x) ^ 2 ≤ Q * R x) (x : X) :
    (u x - v x) ^ 2 ≤ E * C :=
  le_trans (hpt x) (mul_le_mul hQE (hRC x) (hR0 x) (le_trans hQ0 hQE))

end Pointwise

section L2

variable {X : Type*} [MeasurableSpace X] {mu : Measure X} [IsProbabilityMeasure mu]

/-- A uniform pointwise bound gives the same bound for the `L²(μ)`-norm squared,
`μ` being a probability measure. -/
theorem spline_error_L2_le {f : X → ℝ} {K : ℝ} (hK : ∀ x, f x ^ 2 ≤ K) :
    ∫ x, f x ^ 2 ∂mu ≤ K := by
  have hint : ∫ x, f x ^ 2 ∂mu ≤ ∫ _x, K ∂mu := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (integrable_const K) (Filter.Eventually.of_forall hK)
  simpa using hint

/--
**`‖u - P_m^R u‖_{L²} → 0`.**
With the level-`m` bound `C_∂ρ(Ψ)^{-m}ℰ_R(u,u)` of the previous step and
`ρ(Ψ) > 1`, the harmonic-spline errors converge to `0` in `L²(μ)`.
-/
theorem spline_error_L2_tendsto {err : ℕ → X → ℝ} {rho C E : ℝ} (hrho : 1 < rho)
    (hb : ∀ m x, err m x ^ 2 ≤ C * (rho ^ m)⁻¹ * E) :
    Tendsto (fun m => ∫ x, err m x ^ 2 ∂mu) atTop (𝓝 0) := by
  have hpow : Tendsto (fun m : ℕ => C * (rho ^ m)⁻¹ * E) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => ((rho ^ m)⁻¹ : ℝ)) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hrho)
    simpa using (h1.const_mul C).mul_const E
  refine squeeze_zero (fun m => integral_nonneg fun x => sq_nonneg _) (fun m => ?_) hpow
  exact spline_error_L2_le (hb m)

end L2

section Density

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A subspace of a Hilbert space whose orthogonal complement is trivial is dense. -/
theorem dense_of_orthogonal_trivial (K : Submodule ℝ H)
    (h : ∀ u : H, (∀ v ∈ K, inner ℝ v u = (0 : ℝ)) → u = 0) :
    Dense (K : Set H) := by
  refine Submodule.dense_iff_topologicalClosure_eq_top.mpr ?_
  refine Submodule.topologicalClosure_eq_top_iff.mpr ?_
  refine Submodule.eq_bot_iff _ |>.mpr ?_
  intro u hu
  exact h u fun v hv => hu v hv

variable {X : Type*} [TopologicalSpace X] {s : Set X}

/-- A continuous function vanishing on a dense set vanishes identically. -/
theorem eq_zero_of_vanishing_on_dense [T2Space X] (hs : Dense s) {f : X → ℝ}
    (hf : Continuous f) (h0 : ∀ x ∈ s, f x = 0) : ∀ x, f x = 0 := by
  intro x
  have : f = fun _ => (0 : ℝ) :=
    Continuous.ext_on hs hf continuous_const (by simpa using h0)
  simp [this]

/--
**Lemma `sec32_common_core`, density in the form norm.**

`H` is the form space `ℱ_R⁰ = {u ∈ ℱ_R : u(q) = 0}` with the energy inner
product, `K` the subspace spanned by all the harmonic splines, and
`ev u` the function `u` regarded on `Ξ_M`.  The hypotheses are the paper's:

* `hvanish` — trace theory: a function `ℰ_R`-orthogonal to every spline has zero
  trace on every `V(Ξ^m)`, hence vanishes on the dense set `𝒱`;
* `hcont` — a finite-energy function is continuous (in the resistance topology,
  identified with the natural one by Theorem `sec32_resistance_metric`);
* `hinj` — a function of `ℱ_R⁰` vanishing identically is the zero element.

The conclusion is that the splines are dense in `ℱ_R⁰` for the form norm.
-/
theorem spline_core_dense [T2Space X] (hs : Dense s) (K : Submodule ℝ H) (ev : H → X → ℝ)
    (hcont : ∀ u : H, Continuous (ev u))
    (hvanish : ∀ u : H, (∀ v ∈ K, inner ℝ v u = (0 : ℝ)) → ∀ x ∈ s, ev u x = 0)
    (hinj : ∀ u : H, (∀ x, ev u x = 0) → u = 0) :
    Dense (K : Set H) := by
  refine dense_of_orthogonal_trivial K fun u hu => ?_
  exact hinj u (eq_zero_of_vanishing_on_dense hs (hcont u) (hvanish u hu))

end Density

end IGS.Sec32
