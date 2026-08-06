import Mathlib

/-!
# §3.2, step 5: Theorem `sec32_brownian_motion`

*Iterated Graph Systems (I)* (arXiv:2603.13798), Theorem `sec32_brownian_motion`:
the `L²(Ξ_M, μ)` realisation of the resistance form `(ℰ_R, ℱ_R)` coincides with
the limiting Dirichlet form `(ℰ_W, ℱ_W)` of §3.1; hence the diffusion `W` is the
Brownian motion of the resistance form.

The paper's argument is: the continuous harmonic splines are a core for both
forms (Lemma `sec32_common_core` and Theorem `sec31_limit_dirichlet_form`), and
on a level-`m` spline `u = P_m h` both forms give `ℰ_m^W(h,h)`; two closed forms
agreeing on a common core agree everywhere.

That last step is the content of `closed_forms_agree` below, proved from the
usual two properties of a closed form:

* the *core approximation*: every `u` in the domain is the limit of core
  elements, both in `L²` and in the form norm;
* *closedness* (Fatou): if core elements converge to `u` in `L²` and their
  energies converge, the energy of `u` is at most the limit.

Energies enter through their square roots `p_i = √ℰ_i`, which are seminorms; the
reverse triangle inequality `|p u - p v| ≤ p (u - v)` is what turns form-norm
convergence into convergence of energies.

The identification "same Dirichlet form ⟹ same semigroup, same Hunt process,
same heat kernel" is the citation to Fukushima et al. / Kigami; it appears here
as the explicit hypothesis `hdet` of `process_eq_of_forms_agree`.
-/

namespace IGS.Sec32

open Filter Topology

variable {F : Type*} [AddCommGroup F]

/-- The square root of a (Dirichlet) energy: a seminorm-like functional. -/
structure EnergyNorm (p : F → ℝ) : Prop where
  /-- non-negativity -/
  nonneg : ∀ u, 0 ≤ p u
  /-- subadditivity -/
  subadd : ∀ u v, p (u + v) ≤ p u + p v
  /-- evenness -/
  neg : ∀ u, p (-u) = p u

/-- The reverse triangle inequality for an energy norm. -/
theorem EnergyNorm.dist_le {p : F → ℝ} (hp : EnergyNorm p) (u v : F) :
    |p u - p v| ≤ p (u - v) := by
  have h1 : p u ≤ p (u - v) + p v := by
    have := hp.subadd (u - v) v
    simpa using this
  have h2 : p v ≤ p (u - v) + p u := by
    have hvu : p (v - u) = p (u - v) := by
      have : v - u = -(u - v) := by abel
      rw [this, hp.neg]
    have := hp.subadd (v - u) u
    simp only [sub_add_cancel] at this
    linarith [this, hvu]
  rw [abs_le]
  constructor <;> linarith

/-- If `p (u - v n) → 0` then `p (v n) → p u`. -/
theorem EnergyNorm.tendsto_of_tendsto_diff {p : F → ℝ} (hp : EnergyNorm p) {u : F} {v : ℕ → F}
    (h : Tendsto (fun n => p (u - v n)) atTop (𝓝 0)) :
    Tendsto (fun n => p (v n)) atTop (𝓝 (p u)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) h
  have : dist (p (v n)) (p u) = |p (v n) - p u| := rfl
  rw [this, abs_sub_comm]
  exact hp.dist_le u (v n)

/--
**Two closed forms with a common core agree.**

`p₁, p₂` are the energy norms `√ℰ_R`, `√ℰ_W`; `N` measures `L²`-convergence;
`D` is the common core (the continuous harmonic splines).

* `hagree` : the two forms agree on the core (`ℰ_R(u,u) = ℰ_m^W(h,h) = ℰ_W(u,u)`);
* `hcore₁`, `hcore₂` : the core approximates every element of the domain in the
  respective form norm and in `L²`;
* `hclosed₁`, `hclosed₂` : closedness (Fatou) of each form.

Conclusion: `ℰ_R = ℰ_W` on the whole domain.
-/
theorem closed_forms_agree {p₁ p₂ N : F → ℝ} {D : Set F}
    (hp₁ : EnergyNorm p₁) (hp₂ : EnergyNorm p₂)
    (hagree : ∀ v ∈ D, p₁ v = p₂ v)
    (hcore₁ : ∀ u : F, ∃ v : ℕ → F, (∀ n, v n ∈ D) ∧
      Tendsto (fun n => p₁ (u - v n)) atTop (𝓝 0) ∧ Tendsto (fun n => N (u - v n)) atTop (𝓝 0))
    (hcore₂ : ∀ u : F, ∃ v : ℕ → F, (∀ n, v n ∈ D) ∧
      Tendsto (fun n => p₂ (u - v n)) atTop (𝓝 0) ∧ Tendsto (fun n => N (u - v n)) atTop (𝓝 0))
    (hclosed₁ : ∀ (u : F) (v : ℕ → F) (c : ℝ), (∀ n, v n ∈ D) →
      Tendsto (fun n => N (u - v n)) atTop (𝓝 0) →
      Tendsto (fun n => p₁ (v n)) atTop (𝓝 c) → p₁ u ≤ c)
    (hclosed₂ : ∀ (u : F) (v : ℕ → F) (c : ℝ), (∀ n, v n ∈ D) →
      Tendsto (fun n => N (u - v n)) atTop (𝓝 0) →
      Tendsto (fun n => p₂ (v n)) atTop (𝓝 c) → p₂ u ≤ c) :
    ∀ u : F, p₁ u = p₂ u := by
  have key : ∀ (q₁ q₂ : F → ℝ), EnergyNorm q₁ → EnergyNorm q₂ → (∀ v ∈ D, q₁ v = q₂ v) →
      (∀ u : F, ∃ v : ℕ → F, (∀ n, v n ∈ D) ∧
        Tendsto (fun n => q₁ (u - v n)) atTop (𝓝 0) ∧
        Tendsto (fun n => N (u - v n)) atTop (𝓝 0)) →
      (∀ (u : F) (v : ℕ → F) (c : ℝ), (∀ n, v n ∈ D) →
        Tendsto (fun n => N (u - v n)) atTop (𝓝 0) →
        Tendsto (fun n => q₂ (v n)) atTop (𝓝 c) → q₂ u ≤ c) →
      ∀ u : F, q₂ u ≤ q₁ u := by
    intro q₁ q₂ hq₁ hq₂ hag hcore hclosed u
    obtain ⟨v, hvD, hform, hL2⟩ := hcore u
    have h1 : Tendsto (fun n => q₁ (v n)) atTop (𝓝 (q₁ u)) :=
      hq₁.tendsto_of_tendsto_diff hform
    have h2 : Tendsto (fun n => q₂ (v n)) atTop (𝓝 (q₁ u)) := by
      refine h1.congr fun n => hag (v n) (hvD n)
    exact hclosed u v (q₁ u) hvD hL2 h2
  intro u
  exact le_antisymm
    (key p₂ p₁ hp₂ hp₁ (fun v hv => (hagree v hv).symm) hcore₂ hclosed₁ u)
    (key p₁ p₂ hp₁ hp₂ hagree hcore₁ hclosed₂ u)

omit [AddCommGroup F] in
/--
**Theorem `sec32_brownian_motion`, final sentence.**
Once the two forms coincide, the associated semigroups, Hunt processes and heat
kernels coincide.  That a Dirichlet form determines its process is the cited
black box, here the hypothesis `hdet`.
-/
theorem process_eq_of_forms_agree {Proc : Type*} {p₁ p₂ : F → ℝ} (Sem : (F → ℝ) → Proc)
    (hdet : ∀ q₁ q₂ : F → ℝ, (∀ u, q₁ u = q₂ u) → Sem q₁ = Sem q₂)
    (hforms : ∀ u, p₁ u = p₂ u) :
    Sem p₁ = Sem p₂ :=
  hdet p₁ p₂ hforms

end IGS.Sec32
