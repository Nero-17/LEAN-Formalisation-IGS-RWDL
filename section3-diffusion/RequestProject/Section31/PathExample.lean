import RequestProject.Section31.Oscillation

/-!
# A concrete rule graph: the path of length two

This file checks that the hypotheses of
`IGS.Sec31.FiniteNetwork.edge_osc_lt_one_of_no_shortcut` are not vacuous, by
verifying every one of them on the simplest legitimate rule graph — the path
`a — m — b` of length `2`, which is exactly the shortest configuration allowed by
Assumption `ass:standing` (`d(β^+,β^-) ≥ 2`).  Its `0`–`1` harmonic profile is
`(0, 1/2, 1)`, whose edge oscillation is `1/2 < 1`: the contraction factor of
Lemma `sec31_continuous_harmonics` for this rule graph is `θ = 1/2`.
-/

namespace IGS.Sec31

open Finset

namespace PathExample

/-- The path `0 — 1 — 2` with unit conductances. -/
def net : FiniteNetwork (Fin 3) where
  Edge := Fin 2
  fintypeEdge := inferInstance
  decEqEdge := inferInstance
  ends := fun e => if e = 0 then (0, 1) else (1, 2)
  cond := fun _ => 1
  cond_pos := fun _ => one_pos

/-- The `0`–`1` boundary datum. -/
noncomputable def h : Fin 3 → ℝ := ![0, 0, 1]

/-- The harmonic profile. -/
noncomputable def g : Fin 3 → ℝ := ![0, 1/2, 1]

theorem energy_eq (f : Fin 3 → ℝ) :
    net.energy f = (f 0 - f 1) ^ 2 + (f 1 - f 2) ^ 2 := by
  simp [FiniteNetwork.energy, net, Fin.sum_univ_two]

theorem boundary : ∀ x ∈ ({0, 2} : Finset (Fin 3)), g x = h x := by
  intro x hx
  fin_cases hx <;> simp [g, h]

theorem energy_g : net.energy g = 1/2 := by
  rw [energy_eq]; simp [g]; norm_num

theorem is_min : ∀ f, (∀ x ∈ ({0, 2} : Finset (Fin 3)), f x = h x) →
    net.energy g ≤ net.energy f := by
  intro f hf
  have h0 : f 0 = 0 := by simpa [h] using hf 0 (by decide)
  have h2 : f 2 = 1 := by simpa [h] using hf 2 (by decide)
  rw [energy_g, energy_eq, h0, h2]
  nlinarith [sq_nonneg (f 1 - 1/2)]

/-- The discrete Poincaré inequality with constant `K = 2` (compare
`FiniteNetwork.poincare_of_path`: the path has length `2` and `c_min = 1`). -/
theorem poincare : ∀ f : Fin 3 → ℝ, (∀ x ∈ ({0, 2} : Finset (Fin 3)), f x = 0) →
    ∀ x, (f x) ^ 2 ≤ 2 * net.energy f := by
  intro f hf x
  have h0 : f 0 = 0 := hf 0 (by decide)
  have h2 : f 2 = 0 := hf 2 (by decide)
  have hE : net.energy f = 2 * (f 1) ^ 2 := by rw [energy_eq, h0, h2]; ring
  rw [hE]
  have hx : x = 0 ∨ x = 1 ∨ x = 2 := by omega
  rcases hx with rfl | rfl | rfl
  · rw [h0]; nlinarith [sq_nonneg (f 1)]
  · nlinarith [sq_nonneg (f 1)]
  · rw [h2]; nlinarith [sq_nonneg (f 1)]

/-- The path of length `2` has no shortcut edge. -/
theorem no_shortcut : ∀ e : net.Edge,
    ¬ (((net.ends e).1 = 0 ∧ (net.ends e).2 = 2) ∨ ((net.ends e).1 = 2 ∧ (net.ends e).2 = 0)) := by
  decide

/--
The conclusion of `edge_osc_lt_one_of_no_shortcut` on this rule graph: every edge
oscillation of the `0`–`1` profile is `< 1` (here, exactly `1/2`).
-/
theorem edge_osc_lt_one :
    ∀ e : net.Edge, |g (net.ends e).1 - g (net.ends e).2| < 1 :=
  net.edge_osc_lt_one_of_no_shortcut 0 2 2 h poincare (by simp [h]) (by simp [h]) g
    boundary is_min no_shortcut

/-- The contraction factor of this rule graph is `θ = 1/2`. -/
theorem edge_osc_eq_half :
    ∀ e : net.Edge, |g (net.ends e).1 - g (net.ends e).2| = 1/2 := by
  show ∀ e : Fin 2, |g (net.ends e).1 - g (net.ends e).2| = 1/2
  intro e
  fin_cases e
  · simp [net, g]
  · show |g (1 : Fin 3) - g (2 : Fin 3)| = 1/2
    have h1 : g (1 : Fin 3) = 1/2 := by simp [g]
    have h2 : g (2 : Fin 3) = 1 := by simp [g]
    rw [h1, h2]
    norm_num [abs_of_nonpos]

end PathExample

end IGS.Sec31
