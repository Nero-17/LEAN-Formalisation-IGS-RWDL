import Mathlib

/-!
# §3.1, step 8: Mosco convergence (Theorem `sec31_mosco`)

Reference: arXiv:2603.13798, §3.1, Theorem `sec31_mosco`.

The paper works in the varying-space framework of Kuwae–Shioya, with the
asymptotic relation induced by the restriction maps `J_n φ := φ|_{V(Ξⁿ)}`.
Strong and weak convergence are therefore *not* the convergences of a single
fixed Hilbert space; they are the convergences of that asymptotic relation.  We
model this faithfully by taking the two convergence notions as parameters, and
define Mosco convergence relative to them (`MoscoConverges`).  This is the
definition the paper uses, and the one for which the process-convergence
theorem it cites is stated.

The proof of Theorem `sec31_mosco` has two halves.

* **limsup.**  A recovery sequence for a harmonic spline `u = P_m h` is
  `u_n := P_m^{(n)} h`; Lemma `sec31_discrete_harmonics` gives `u_n → u`
  strongly with `ℰ̃_n^X(u_n,u_n) → ℰ_W(u,u)`, and harmonic splines form a core.
  Passing from the core to the whole domain is a diagonal argument which we do
  not formalise; here `mosco_of_recovery_on_core` records that if recovery
  sequences exist for *every* element of the domain (the outcome of that
  diagonal argument) and the liminf inequality holds, then Mosco convergence
  holds.

* **liminf.**  Given `f_n ⇀ f` with `sup_n ℰ̃_n^X(f_n,f_n) < ∞`, the discrete
  harmonic projections produce, for each `m`, a spline `u_m ∈ ℋ_m` with
  `ℰ_W(u_m,u_m) ≤ liminf_n ℰ̃_n^X(f_n,f_n)`, and Lemma
  `sec31_projection_tail_continuous` shows `u_m → f` in `L²`.  Closedness
  (lower semicontinuity) of `ℰ_W` then gives
  `ℰ_W(f,f) ≤ liminf_n ℰ̃_n^X(f_n,f_n)`.  That final step is
  `energy_le_of_spline_bound`, proved here.
-/

namespace IGS.Sec31

open Filter Topology

variable {H : Type*}

/--
**Mosco convergence** of the forms `En` to `E`, relative to the strong and weak
convergence notions of a given asymptotic relation (Kuwae–Shioya).

* `liminf`: for every weakly convergent `f n ⇀ u`, `E u ≤ liminf_n En n (f n)`;
* `limsup`: every `u` admits a strongly convergent recovery sequence along which
  the energies converge to `E u`.
-/
structure MoscoConverges (Strong Weak : (ℕ → H) → H → Prop) (En : ℕ → H → ℝ) (E : H → ℝ) :
    Prop where
  liminf_le : ∀ f u, Weak f u → E u ≤ liminf (fun n => En n (f n)) atTop
  exists_recovery : ∀ u, ∃ f, Strong f u ∧ Tendsto (fun n => En n (f n)) atTop (𝓝 (E u))

/--
Assembling the two halves of Theorem `sec31_mosco`.
-/
theorem mosco_of_recovery_on_core {Strong Weak : (ℕ → H) → H → Prop} {En : ℕ → H → ℝ} {E : H → ℝ}
    (hliminf : ∀ f u, Weak f u → E u ≤ liminf (fun n => En n (f n)) atTop)
    (hlimsup : ∀ u, ∃ f, Strong f u ∧ Tendsto (fun n => En n (f n)) atTop (𝓝 (E u))) :
    MoscoConverges Strong Weak En E :=
  ⟨hliminf, hlimsup⟩

/--
**The final step of the liminf inequality.**

`u m` are the harmonic splines produced from `f_n` at coarse level `m`, `A` is
`liminf_n ℰ̃_n^X(f_n,f_n)`, and `E` is the limit form, which is closed, i.e.
sequentially lower semicontinuous along `L²`-convergent sequences.  If every
spline has energy at most `A` and the splines converge to `f`, then
`E f ≤ A`.
-/
theorem energy_le_of_spline_bound [TopologicalSpace H] (E : H → ℝ) (u : ℕ → H) (f : H) (A : ℝ)
    (hE0 : ∀ v, 0 ≤ E v)
    (hlsc : ∀ (v : ℕ → H) (w : H), Tendsto v atTop (𝓝 w) →
      E w ≤ liminf (fun m => E (v m)) atTop)
    (hconv : Tendsto u atTop (𝓝 f)) (hbound : ∀ m, E (u m) ≤ A) :
    E f ≤ A := by
  refine (hlsc u f hconv).trans ?_
  have hb : IsBoundedUnder (· ≥ ·) atTop fun m => E (u m) :=
    ⟨0, eventually_map.2 (Eventually.of_forall fun m => hE0 (u m))⟩
  exact liminf_le_of_frequently_le (Frequently.of_forall hbound) hb

end IGS.Sec31
