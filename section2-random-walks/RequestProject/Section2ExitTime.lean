import Mathlib
import RequestProject.Section2Commute

/-!
# Exit times, local balls and the `E[τ] ≍ V·R` programme (Section 2)

This file sets up the **exit-time** layer that sits one level above the commute-time
identity `C = 2|E|·R` of `Section2Commute.lean`.  Following the roadmap, the
commute-time identity is *middleware* — it makes the formula `C = 2|E|R` precise —
but the genuine **exit-time scaling** `E[τ] ≍ V·R` (expected exit time from a ball
≍ volume × resistance) is a deeper, localised estimate.  Here we build its
backbone over a finite connected simple graph `G` with Laplacian `L`:

* **Exit-time linear system** (`ExitSystem G S τ`): the expected exit time `τ` of the
  simple random walk from a set `S` (i.e. the hitting time of the complement `Sᶜ`)
  is `0` off `S` and satisfies the Laplacian recurrence `(L ·ᵥ τ) x = deg x` on `S`
  (`deg(x) τ(x) = deg(x) + ∑_{y∼x} τ(y)`).
* **Well-posedness** (`ExitSystem.unique`): on a connected graph with nonempty
  complement, the exit-time system has at most one solution — the linear-system
  characterisation is unambiguous.
* **Dirichlet-energy identity** (`exit_time_dirichlet_identity`): the
  *volume-weighted total exit time* equals the Dirichlet energy of `τ`,
  `∑_{x∈S} deg(x) τ(x) = ½ ∑_{i∼j} (τ_i − τ_j)²`.
  This is the exact analytic bridge underlying `E[τ] ≍ V·R`: the left side is the
  volume-weighted exit time, the right side is the energy whose minimisation defines
  effective resistance.

## What remains (the frontier)

The full two-sided estimate `E_o[τ_{B(o,r)}] ≍ V(o,r) · R(o, ∂B(o,r))` (the
Barlow–Telcs / Kigami exit-time estimate), and the *local ball estimates* on `V`
and `R` that turn it into the walk-dimension scaling, require localised Green's
function comparisons that go beyond the identities proved here; they are the genuine
analytical core flagged as the remaining work and are *not* a corollary of the
commute-time identity alone.
-/

namespace EIGS

open scoped BigOperators
open SimpleGraph Matrix Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The linear system characterising the expected exit time `τ` of the simple random
walk from a set `S` (equivalently, the hitting time of the complement `Sᶜ`): `τ`
vanishes off `S`, and on `S` it solves the Laplacian recurrence `(L ·ᵥ τ) x = deg x`. -/
def ExitSystem (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (τ : V → ℝ) : Prop :=
  (∀ x, x ∉ S → τ x = 0) ∧ (∀ x, x ∈ S → (G.lapMatrix ℝ *ᵥ τ) x = (G.degree x : ℝ))

/-
**Dirichlet-energy identity for the exit time.**  The volume-weighted total exit
time `∑_{x∈S} deg(x) τ(x)` equals the Dirichlet energy `½ ∑_{i∼j} (τ_i − τ_j)²` of the
exit-time function — the exact bridge between exit time (volume side) and resistance
(energy side).
-/
theorem exit_time_dirichlet_identity (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {τ : V → ℝ} (hτ : ExitSystem G S τ) :
    (∑ x ∈ S, (G.degree x : ℝ) * τ x)
      = (∑ i : V, ∑ j : V, if G.Adj i j then (τ i - τ j) ^ 2 else 0) / 2 := by
  have h_dirichlet : ( ∑ x ∈ S, ( G.degree x : ℝ ) * τ x ) = ∑ x, τ x * ( G.lapMatrix ℝ *ᵥ τ ) x := by
    rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ];
    · exact Finset.sum_congr rfl fun x hx => by rw [ hτ.2 x hx, mul_comm ] ;
    · exact fun x _ hx => by rw [ hτ.1 x hx, MulZeroClass.zero_mul ] ;
  rw [ h_dirichlet ];
  convert SimpleGraph.lapMatrix_toLinearMap₂' ( R := ℝ ) G τ using 1;
  rw [ Matrix.toLinearMap₂'_apply' ];
  rfl

/-
**Well-posedness of the exit-time system.**  On a connected graph with nonempty
complement `Sᶜ`, the exit-time linear system has at most one solution: the
linear-system characterisation of the expected exit time is unambiguous.
-/
theorem ExitSystem.unique (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    {S : Finset V} (hScompl : Sᶜ.Nonempty) {τ₁ τ₂ : V → ℝ}
    (h₁ : ExitSystem G S τ₁) (h₂ : ExitSystem G S τ₂) : τ₁ = τ₂ := by
  apply funext; intro x; exact (by
  have h_eq : ∀ i j : V, G.Reachable i j → (τ₁ i - τ₂ i) = (τ₁ j - τ₂ j) := by
    have h_eq : Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) (fun x => τ₁ x - τ₂ x) (fun x => τ₁ x - τ₂ x) = 0 := by
      have h_quad_form : Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) (fun x => τ₁ x - τ₂ x) (fun x => τ₁ x - τ₂ x) = ∑ x, (τ₁ x - τ₂ x) * (G.lapMatrix ℝ *ᵥ (fun x => τ₁ x - τ₂ x)) x := by
        convert Matrix.toLinearMap₂'_apply' _ _ _ using 1;
      simp_all +decide [ ExitSystem, Matrix.mulVec, dotProduct ];
      refine' Finset.sum_eq_zero fun x hx => _ ; by_cases hx' : x ∈ S <;> simp_all +decide [ mul_sub ] ;
    grind +suggestions;
  obtain ⟨ z, hz ⟩ := hScompl; specialize h_eq x z ( hG x z ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
  linarith [ h₁.1 z hz, h₂.1 z hz ]);

end EIGS