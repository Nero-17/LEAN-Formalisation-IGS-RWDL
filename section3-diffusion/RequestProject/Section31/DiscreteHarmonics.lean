import Mathlib

/-!
# §3.1, step 5: discrete harmonic functions converge
(Lemma `sec31_discrete_harmonics`)

Reference: arXiv:2603.13798, §3.1, Lemma `sec31_discrete_harmonics`.

The lemma says that the *unit-resistance* discrete harmonic extension
`P_m^{(n)} h` (the minimiser of the rescaled walk form `ℰ̃_n^X` with boundary
values `h` on `V(Ξ^m)`) converges, as `n → ∞`, to the *weighted* harmonic spline
`P_m h` of Lemma `sec31_continuous_harmonics`, uniformly; and consequently the
energy and `L²` Gram matrices converge.

The proof of the paper has three steps, and all three are proved here.

1. **Perron asymptotics of the traced conductances.**  Tracing the
   unit-resistance network of `Ξⁿ` down to `V(Ξ^{m+r})` produces the
   conductances `c_Ψ^* ρ(Ψ)^n [Ψ^{n-m-r}(1)]_j^{-1}` on colour-`j` edges;
   since `[Ψ^q(1)]_j / ρ(Ψ)^q → κ_j` (primitivity of `Ψ`, Perron–Frobenius),
   these converge to `ρ(Ψ)^{m+r} [v]_j^{-1}`, the weighted conductances of
   §3.1.  This is `traced_conductance_tendsto`; the Perron limit itself is the
   hypothesis `ha` (it is Lemma `thm:sdprimitive_eigenpair` of the paper).

2. **Continuity of the minimiser.**  On the *fixed finite* graph `V(Ξ^{m+r})`
   the harmonic extension is the minimiser of a quadratic form whose
   coefficients converge, and the limiting minimiser is unique.  Hence the
   discrete minimisers converge to it.  This is `tendsto_minimiser`, proved by
   the standard compactness argument (every subsequential limit is a minimiser
   of the limit form, and that minimiser is unique).  The oscillation
   contraction of Lemma `sec31_continuous_harmonics` then upgrades convergence
   on `V(Ξ^{m+r})` to uniform convergence on all deeper levels.

3. **Convergence of the Gram matrices.**  Energies and `L²` inner products over
   a fixed finite vertex/edge set are finite sums of products, so they converge
   as soon as the conductances (resp. the weights `π_n`) and the functions do.
   This is `tendsto_energy_of_tendsto` and `tendsto_gram_of_tendsto`.
-/

namespace IGS.Sec31

open Filter Topology

/--
**Perron asymptotics for the traced conductances.**
If `a q / ρ^q → κ > 0` — the Perron–Frobenius asymptotics
`[Ψ^q(1)]_j ∼ κ_j ρ(Ψ)^q` — then the traced conductance
`c_Ψ^* ρ^{q+s} (a q)⁻¹` converges to `c_Ψ^* ρ^s / κ`, which with
`κ_j = [v]_j / c_Ψ^*` is exactly `ρ(Ψ)^{s}[v]_j^{-1}`.
-/
theorem traced_conductance_tendsto (rho cstar kappa : ℝ) (hrho : 0 < rho) (hkappa : 0 < kappa)
    (s : ℕ) (a : ℕ → ℝ) (ha : Tendsto (fun q => a q / rho ^ q) atTop (𝓝 kappa)) :
    Tendsto (fun q => cstar * rho ^ (q + s) * (a q)⁻¹) atTop (𝓝 (cstar * rho ^ s / kappa)) := by
  have hinv : Tendsto (fun q => (a q / rho ^ q)⁻¹) atTop (𝓝 kappa⁻¹) := ha.inv₀ hkappa.ne'
  have h2 := hinv.const_mul (cstar * rho ^ s)
  rw [show cstar * rho ^ s / kappa = cstar * rho ^ s * kappa⁻¹ by ring]
  refine h2.congr fun q => ?_
  have hp : (rho ^ q : ℝ) ≠ 0 := by positivity
  rcases eq_or_ne (a q) 0 with h | h
  · simp [h, pow_add]
  · field_simp [pow_add]
    ring

/--
**Continuity of the minimiser of a converging family of forms.**

If the forms `Q n` converge uniformly on a compact space to `Q∞`, if `x n`
minimises `Q n`, and if `Q∞` has a *unique* minimiser `x⋆`, then `x n → x⋆`.

Applied on the finite-dimensional (hence, after restricting to a compact set of
admissible boundary-value-preserving configurations, compact) space of functions
on the fixed finite graph `V(Ξ^{m+r})`, this is the convergence
`P_m^{(n)} h → P_m h` of Lemma `sec31_discrete_harmonics`.
-/
theorem tendsto_minimiser {X : Type*} [MetricSpace X] [CompactSpace X]
    (Q : ℕ → X → ℝ) (Qinf : X → ℝ) (hQcont : Continuous Qinf)
    (hunif : TendstoUniformly Q Qinf atTop)
    (x : ℕ → X) (hx : ∀ n, ∀ y, Q n (x n) ≤ Q n y)
    (xstar : X) (hstar : ∀ y, y ≠ xstar → Qinf xstar < Qinf y) :
    Tendsto x atTop (𝓝 xstar) := by
  refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
  obtain ⟨a, -, φ, hφ, hconv⟩ :=
    (isCompact_univ (X := X)).tendsto_subseq (x := fun k => x (ns k)) (fun k => Set.mem_univ _)
  refine ⟨φ, ?_⟩
  have hidx : Tendsto (fun k => ns (φ k)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hunif' : TendstoUniformly (fun k => Q (ns (φ k))) Qinf atTop := fun u hu =>
    hidx.eventually (hunif u hu)
  have h1 : Tendsto (fun k => Q (ns (φ k)) (x (ns (φ k)))) atTop (𝓝 (Qinf a)) :=
    hunif'.tendsto_comp hQcont.continuousAt hconv
  have h2 : Tendsto (fun k => Q (ns (φ k)) xstar) atTop (𝓝 (Qinf xstar)) :=
    hunif'.tendsto_comp hQcont.continuousAt tendsto_const_nhds
  have hle : Qinf a ≤ Qinf xstar :=
    le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun k => hx _ _)
  have hax : a = xstar := by
    by_contra hne
    exact absurd hle (not_le.mpr (hstar a hne))
  rw [← hax]
  exact hconv

/--
Finite sums of products of convergent sequences converge.
-/
theorem tendsto_finset_sum_mul {ι : Type*} [Fintype ι] (a b : ℕ → ι → ℝ) (ainf binf : ι → ℝ)
    (ha : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (ainf i)))
    (hb : ∀ i, Tendsto (fun n => b n i) atTop (𝓝 (binf i))) :
    Tendsto (fun n => ∑ i, a n i * b n i) atTop (𝓝 (∑ i, ainf i * binf i)) :=
  tendsto_finset_sum _ fun i _ => (ha i).mul (hb i)

/--
**Convergence of the energy Gram matrix.**
`E` indexes the edges of a fixed finite graph, `c n e` are the traced
conductances at level `n` and `u n`, `w n` the discrete harmonic extensions
evaluated at the endpoints of `e`.  If both converge, so do the energies
`ℰ̃_n^X(u_n, w_n) → ℰ_W(u, w)`.
-/
theorem tendsto_energy_of_tendsto {E : Type*} [Fintype E]
    (c : ℕ → E → ℝ) (cinf : E → ℝ) (hc : ∀ e, Tendsto (fun n => c n e) atTop (𝓝 (cinf e)))
    (du dw : ℕ → E → ℝ) (duinf dwinf : E → ℝ)
    (hdu : ∀ e, Tendsto (fun n => du n e) atTop (𝓝 (duinf e)))
    (hdw : ∀ e, Tendsto (fun n => dw n e) atTop (𝓝 (dwinf e))) :
    Tendsto (fun n => ∑ e, c n e * (du n e * dw n e)) atTop
      (𝓝 (∑ e, cinf e * (duinf e * dwinf e))) :=
  tendsto_finset_sum_mul c (fun n e => du n e * dw n e) cinf (fun e => duinf e * dwinf e) hc
    fun e => (hdu e).mul (hdw e)

/--
**Convergence of the `L²` Gram matrix.**
Same statement for the inner products `⟨·,·⟩_{L²(π_n)} → ⟨·,·⟩_{L²(μ_{Ξ_M})}`
over a fixed finite vertex set, given `π_n → μ` on the (finitely many) atoms
involved and the convergence of the functions.
-/
theorem tendsto_gram_of_tendsto {V : Type*} [Fintype V]
    (pi : ℕ → V → ℝ) (mu : V → ℝ) (hpi : ∀ x, Tendsto (fun n => pi n x) atTop (𝓝 (mu x)))
    (f g : ℕ → V → ℝ) (finf ginf : V → ℝ)
    (hf : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (finf x)))
    (hg : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (ginf x))) :
    Tendsto (fun n => ∑ x, pi n x * (f n x * g n x)) atTop
      (𝓝 (∑ x, mu x * (finf x * ginf x))) :=
  tendsto_finset_sum_mul pi (fun n x => f n x * g n x) mu (fun x => finf x * ginf x) hpi
    fun x => (hf x).mul (hg x)

end IGS.Sec31
