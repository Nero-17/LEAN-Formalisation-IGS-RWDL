import Mathlib.Order.LiminfLimsup
import RequestProject.Section31.CoreRecovery

/-!
# §3.1, step 8: Mosco convergence (Theorem `sec31_mosco`)

Reference: arXiv:2603.13798, §3.1, Theorem `sec31_mosco`.

The paper works in the varying-space framework of Kuwae–Shioya, with the
asymptotic relation induced by the restriction maps `J_n φ := φ|_{V(Ξⁿ)}`.
Strong and weak convergence are therefore *not* the convergences of a single
fixed Hilbert space; they are the convergences of that asymptotic relation.  We
retain an abstract interface with the two convergence notions as parameters
(`MoscoConverges`).  This interface uses a single ambient type and real-valued
energies.  It does not construct the paper's varying Hilbert spaces, their
asymptotic relation, or an extended-valued form outside its domain.

The proof of Theorem `sec31_mosco` has two halves.

* **limsup.**  A recovery sequence for a harmonic spline `u = P_m h` is
  `u_n := P_m^{(n)} h`; Lemma `sec31_discrete_harmonics` gives `u_n → u`
  strongly with `ℰ̃_n^X(u_n,u_n) → ℰ_W(u,u)`, and harmonic splines form a core.
  `CoreRecovery.lean` proves the diagonal passage in a fixed pseudometric
  ambient space, with both the state and the energy converging.
  `mosco_of_sequential_core` assembles this result from core-only recovery
  sequences and sequential density in the joint state/energy topology.
  Connecting those hypotheses to the paper's varying-space construction
  remains separate.  The older `mosco_of_recovery_on_core` is only an
  assembly lemma: despite its historical name it assumes full recovery.

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
This historical lemma assumes recovery for every element; it does not prove
the passage from a core.  See `mosco_of_sequential_core` for that passage in
a fixed pseudometric ambient space.
-/
theorem mosco_of_recovery_on_core {Strong Weak : (ℕ → H) → H → Prop} {En : ℕ → H → ℝ} {E : H → ℝ}
    (hliminf : ∀ f u, Weak f u → E u ≤ liminf (fun n => En n (f n)) atTop)
    (hlimsup : ∀ u, ∃ f, Strong f u ∧ Tendsto (fun n => En n (f n)) atTop (𝓝 (E u))) :
    MoscoConverges Strong Weak En E :=
  ⟨hliminf, hlimsup⟩

/-- Mosco convergence in a fixed pseudometric ambient space follows from
the liminf inequality, sequential density of a core in the joint
state/energy topology, and recovery for core elements only.

The diagonal argument constructs recovery at every original index `n`.
The varying-space realisation, core density, core recovery, and liminf
inequality of a concrete EIGS must still be established separately. -/
theorem mosco_of_sequential_core [PseudoMetricSpace H]
    {Weak : (ℕ → H) → H → Prop} {En : ℕ → H → ℝ} {E : H → ℝ}
    (coreSet : Set H)
    (hliminf : ∀ f u, Weak f u → E u ≤ liminf (fun n => En n (f n)) atTop)
    (hcore : ∀ target : H, ∃ core : ℕ → H,
      (∀ k, core k ∈ coreSet) ∧ Tendsto core atTop (𝓝 target) ∧
        Tendsto (fun k => E (core k)) atTop (𝓝 (E target)))
    (hcoreRecovery : ∀ u ∈ coreSet, ∃ recovery : ℕ → H,
      Tendsto recovery atTop (𝓝 u) ∧
        Tendsto (fun n => En n (recovery n)) atTop (𝓝 (E u))) :
    MoscoConverges (fun f u => Tendsto f atTop (𝓝 u)) Weak En E := by
  classical
  refine ⟨hliminf, ?_⟩
  intro target
  obtain ⟨core, hmem, hstate, henergy⟩ := hcore target
  choose approximation happroximation happroximationEnergy using
    fun k => hcoreRecovery (core k) (hmem k)
  exact exists_recovery_of_core En E target core approximation hstate henergy
    happroximation happroximationEnergy

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
