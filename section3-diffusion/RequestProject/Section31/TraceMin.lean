import Mathlib

/-!
# §3.1, step 1: the weighted trace lemma (Lemma `sec31_trace_weighted`)

Reference: *Iterated Graph Systems (I): random walks and diffusion limits*,
arXiv:2603.13798, §3.1.

The paper's Lemma `sec31_trace_weighted` states: for every `n` and every
`f : V(Ξⁿ) → ℝ`, the weighted energy

  `ℰ_n^W(f,f) = ∑_{ {u,v} ∈ E(Ξⁿ) } c_n({u,v}) (f(u) - f(v))²`

is the *minimum* of `ℰ_{n+1}^W(g,g)` over all extensions `g` of `f` to
`V(Ξ^{n+1})`, and the minimiser is unique.

Its proof has exactly two ingredients.

1. A *one-cell* statement, which is the Dirichlet principle for a two-terminal
   finite network together with the resistance renormalisation of §2:
   on the copy of the rule graph `R_i` that replaces an edge `e = {a,b}` of
   colour `i`, the least energy compatible with the terminal values `f(a)`,
   `f(b)` equals `c_n(e) (f(a) - f(b))²`, because the effective resistance
   between the two terminals of that copy is
   `ρ(Ψ)^{-(n+1)} ψ_{R_i}(v) = ρ(Ψ)^{-n} [v]_i = r_n(e)`
   (this is the eigenvector equation `Ψ(v) = ρ(Ψ) v`).
   The paper cites `kigami2001analysis` for it.  The *qualitative* half — that a
   minimiser exists and is unique — is proved from scratch in
   `RequestProject.Section31.DirichletPrinciple`; what is left as a hypothesis
   below is only the *value* `c_n(e) (f(a)-f(b))²` of the one-cell minimum,
   i.e. the effective-resistance computation of §2.

2. A *decoupling* step: distinct level-`(n+1)` cells meet only in the terminals,
   which are already prescribed by `f`, so the total energy is a sum of
   independent one-cell energies and the minimisation can be performed cell by
   cell.  This step is the combinatorial content of the lemma and it *is* proved
   here, in the following abstract form: `Int e` is the space of possible values
   of `g` on the interior of the cell over `e`, `cellE e` is the energy of that
   cell (a function of the interior values only, the terminal values being
   frozen), and the total energy is `∑ e, cellE e (y e)`.

`isLeast_extension_energy` is the "minimum" half and `eq_of_minimises_energy`
the uniqueness half (uniqueness of the one-cell minimiser is again the
Dirichlet-principle input; it holds because the energy is strictly convex on the
interior variables, which requires each cell interior to be connected to the
terminals).
-/

namespace IGS.Sec31

open Finset

variable {E : Type*} [Fintype E] {Int : E → Type*}

/--
**Decoupled Dirichlet principle (Lemma `sec31_trace_weighted`, existence part).**

If the level-`(n+1)` energy of an extension `g` of `f` decomposes as
`∑ e, cellE e (y e)`, where `y e` are the interior values of `g` on the cell
over the edge `e`, and if on each cell the least energy compatible with the
frozen terminal values `f` is `m e` and is attained, then the least energy of an
extension of `f` is `∑ e, m e`.

Applied with `m e = c_n(e) (f(a_e) - f(b_e))²` this is precisely
`min { ℰ_{n+1}^W(g,g) : g|_{V(Ξⁿ)} = f } = ℰ_n^W(f,f)`.
-/
theorem isLeast_extension_energy
    (cellE : ∀ e, Int e → ℝ) (m : E → ℝ)
    (hlb : ∀ e, ∀ y : Int e, m e ≤ cellE e y)
    (hatt : ∀ e, ∃ y : Int e, cellE e y = m e) :
    IsLeast {v : ℝ | ∃ y : ∀ e, Int e, v = ∑ e, cellE e (y e)} (∑ e, m e) := by
  constructor
  · choose y hy using hatt
    exact ⟨y, by simp [hy]⟩
  · rintro v ⟨y, rfl⟩
    exact Finset.sum_le_sum fun e _ => hlb e (y e)

/--
**Decoupled Dirichlet principle (Lemma `sec31_trace_weighted`, uniqueness part).**

If on every cell the minimiser `y₀ e` of the cell energy is strict, then the
minimising extension is unique.
-/
theorem eq_of_minimises_energy
    (cellE : ∀ e, Int e → ℝ) (y₀ : ∀ e, Int e)
    (hstrict : ∀ e, ∀ y : Int e, y ≠ y₀ e → cellE e (y₀ e) < cellE e y)
    (y : ∀ e, Int e) (hy : ∑ e, cellE e (y e) = ∑ e, cellE e (y₀ e)) :
    y = y₀ := by
  funext e
  by_contra hne
  have hlt : cellE e (y₀ e) < cellE e (y e) := hstrict e (y e) hne
  have hle : ∀ e' ∈ Finset.univ, cellE e' (y₀ e') ≤ cellE e' (y e') := by
    intro e' _
    rcases eq_or_ne (y e') (y₀ e') with h | h
    · rw [h]
    · exact (hstrict e' (y e') h).le
  have hsum := Finset.sum_lt_sum hle ⟨e, Finset.mem_univ e, hlt⟩
  linarith [hy]

/--
**The scaling identity behind the one-cell input.**

The conductances of §3.1 are `c_n(e) = ρ(Ψ)^n [v]_i⁻¹` for an edge of colour `i`,
and the conductance obtained by tracing the level-`(n+1)` network on a single
cell back to its two terminals is `ρ(Ψ)^{n+1} ψ_i(v)⁻¹`, where
`ψ_i(v)` is the resistance functional of the rule graph `R_i`.  The eigenvector
equation `ψ_i(v) = ρ(Ψ) [v]_i` turns this into `ρ(Ψ)^n [v]_i⁻¹ = c_n(e)`, i.e.
the trace of the level-`(n+1)` network on `V(Ξⁿ)` has *exactly* the level-`n`
conductances.  That elementary computation is recorded here.
-/
theorem traced_conductance_eq (rhoPsi : ℝ) (hrho : 0 < rhoPsi) (n : ℕ) (vi psi_i : ℝ)
    (heig : psi_i = rhoPsi * vi) :
    rhoPsi ^ (n + 1) * psi_i⁻¹ = rhoPsi ^ n * vi⁻¹ := by
  subst heig
  rcases eq_or_ne vi 0 with h | h
  · simp [h]
  · field_simp
    ring

end IGS.Sec31
