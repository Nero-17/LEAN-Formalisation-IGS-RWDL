import Mathlib
import RequestProject.Oscillation
import RequestProject.Section2Green

/-!
# Harmonic measure on a finite graph and oscillation contraction for harmonic functions

This file supplies the *analytic* input of the oscillation-contraction machinery
used by the new proof of Lemma 2.22: it constructs the **discrete harmonic
measure** of a set `D` from the Dirichlet Green function, proves the
**mean-value (Poisson) representation** of functions harmonic on `D`, and
combines it with `Oscillation.oscOn_meanValue_contraction` to obtain the
one-step contraction

  `oscOn u A ≤ (1 - ε) * oscOn u B`

for `u` harmonic in the interior `D` of a cell whose boundary is `B`, where `A`
is a "child" subset of the cell meeting the boundary only in one distinguished
planting vertex `p`, and `ε` is a uniform lower bound for the harmonic measure.

Main results:

* `harmMeas` : the harmonic measure `ω_D(y, z) = ∑_{x ∈ D} g_D(y,x) 𝟙[x ∼ z]`;
* `harmMeas_nonneg`, `harmMeas_sum_one`, `harmonic_repr` : it is a probability
  measure on the boundary and reproduces harmonic functions;
* `greenFn_pos` : the **strong maximum principle** — the Dirichlet Green
  function is strictly positive between vertices joined by a path inside `D`;
* `harmMeas_pos_of_walk` : consequently the harmonic measure of a boundary
  vertex is strictly positive;
* `oscOn_contraction_of_harmonic` : the one-step oscillation contraction.
-/

namespace EIGS

open scoped BigOperators
open SimpleGraph Matrix Finset

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The **discrete harmonic measure** of the (Dirichlet) domain `D`:
`ω_D(y, z) = ∑_{x ∈ D} g_D(y, x) · 𝟙[x ∼ z]`, the probability that the walk
started at `y ∈ D` exits `D` at the boundary vertex `z ∉ D`. -/
noncomputable def harmMeas (D : Finset V) (y : D) (z : V) : ℝ :=
  ∑ x : D, greenFn G D y x * (if G.Adj (x : V) z then 1 else 0)

/-- The harmonic measure is nonnegative. -/
lemma harmMeas_nonneg (hG : G.Connected) {D : Finset V} (hDc : Dᶜ.Nonempty)
    (y : D) (z : V) : 0 ≤ harmMeas G D y z := by
  refine Finset.sum_nonneg fun x _ => mul_nonneg (greenFn_nonneg G hG hDc y x) ?_
  split_ifs <;> norm_num

/-- If no vertex of `D` is adjacent to `z`, the harmonic measure at `z` vanishes. -/
lemma harmMeas_eq_zero {D : Finset V} (y : D) {z : V}
    (hz : ∀ x ∈ D, ¬ G.Adj x z) : harmMeas G D y z = 0 := by
  refine Finset.sum_eq_zero fun x _ => ?_
  have : ¬ G.Adj (x : V) z := hz x x.2
  simp [this]

/-- **Poisson representation.**  A function harmonic on `D` is reproduced from
its boundary values by the harmonic measure. -/
theorem harmonic_repr (hG : G.Connected) {D : Finset V} (hDc : Dᶜ.Nonempty)
    {u : V → ℝ} (hu : ∀ x ∈ D, (G.lapMatrix ℝ *ᵥ u) x = 0) (y : D) :
    u (y : V) = ∑ z ∈ Dᶜ, harmMeas G D y z * u z := by
  classical
  set b : D → ℝ := fun x => ∑ z ∈ Dᶜ, (if G.Adj (x : V) z then (1 : ℝ) else 0) * u z with hb
  -- Step 1: the Dirichlet Laplacian of the restriction of `u` is the boundary flux `b`.
  have hLb : dirichletLap G D *ᵥ (fun x : D => u (x : V)) = b := by
    funext x
    have hlap : (G.lapMatrix ℝ *ᵥ u) (x : V) = 0 := hu x x.2
    have hD : (dirichletLap G D *ᵥ (fun x : D => u (x : V))) x
        = ∑ w ∈ D, (G.lapMatrix ℝ) (x : V) w * u w := by
      simp only [dirichletLap, Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
      rw [← Finset.sum_attach D (fun w => (G.lapMatrix ℝ) (x : V) w * u w)]
      rfl
    have hL : (G.lapMatrix ℝ *ᵥ u) (x : V) = ∑ w : V, (G.lapMatrix ℝ) (x : V) w * u w := rfl
    have hsplit' : ∑ w : V, (G.lapMatrix ℝ) (x : V) w * u w
        = ∑ w ∈ D, (G.lapMatrix ℝ) (x : V) w * u w
          + ∑ w ∈ Dᶜ, (G.lapMatrix ℝ) (x : V) w * u w := by
      rw [← Finset.sum_add_sum_compl D (fun w => (G.lapMatrix ℝ) (x : V) w * u w)]
    have hcompl : ∀ w ∈ Dᶜ, (G.lapMatrix ℝ) (x : V) w * u w
        = -((if G.Adj (x : V) w then (1 : ℝ) else 0) * u w) := by
      intro w hw
      have hne : (x : V) ≠ w := fun h => (Finset.mem_compl.mp hw) (h ▸ x.2)
      by_cases hadj : G.Adj (x : V) w <;>
        simp [SimpleGraph.lapMatrix, degMatrix, Matrix.diagonal, hne, hadj]
    rw [hL, hsplit', Finset.sum_congr rfl hcompl, Finset.sum_neg_distrib] at hlap
    rw [hD, hb]
    linarith [hlap]
  -- Step 2: invert.
  have hinv : (fun x : D => u (x : V)) = greenFn G D *ᵥ b := by
    have h1 : (dirichletLap G D) * (greenFn G D) = 1 := dirichletLap_mul_greenFn G hG hDc
    have h2 : (greenFn G D) * (dirichletLap G D) = 1 := mul_eq_one_comm.mp h1
    calc (fun x : D => u (x : V)) = (1 : Matrix D D ℝ) *ᵥ (fun x : D => u (x : V)) := by
          rw [Matrix.one_mulVec]
      _ = ((greenFn G D) * (dirichletLap G D)) *ᵥ (fun x : D => u (x : V)) := by rw [h2]
      _ = greenFn G D *ᵥ (dirichletLap G D *ᵥ (fun x : D => u (x : V))) := by
          rw [Matrix.mulVec_mulVec]
      _ = greenFn G D *ᵥ b := by rw [hLb]
  -- Step 3: unfold and exchange the two summations.
  have hy := congr_fun hinv y
  rw [hy]
  simp only [Matrix.mulVec, dotProduct, hb, harmMeas]
  have : ∀ x : D, greenFn G D y x * ∑ z ∈ Dᶜ, (if G.Adj (x : V) z then (1 : ℝ) else 0) * u z
      = ∑ z ∈ Dᶜ, greenFn G D y x * (if G.Adj (x : V) z then (1 : ℝ) else 0) * u z := by
    intro x
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [Finset.sum_congr rfl (fun x _ => this x), Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_mul]

/-- The harmonic measure is a probability measure on the boundary. -/
theorem harmMeas_sum_one (hG : G.Connected) {D : Finset V} (hDc : Dᶜ.Nonempty) (y : D) :
    ∑ z ∈ Dᶜ, harmMeas G D y z = 1 := by
  have h := harmonic_repr G hG hDc (u := fun _ => (1 : ℝ))
    (fun x _ => by
      have := SimpleGraph.lapMatrix_mulVec_const_eq_zero (R := ℝ) (G := G)
      simp [this]) y
  simpa using h.symm

/-! ### Strict positivity of the Green function (strong maximum principle) -/

/-- The diagonal of the Green function is positive. -/
lemma greenFn_diag_pos (hG : G.Connected) {D : Finset V} (hDc : Dᶜ.Nonempty) (y : D) :
    0 < greenFn G D y y := by
  have hpd : (dirichletLap G D).PosDef := dirichletLap_posDef G hG hDc
  simpa [greenFn] using hpd.inv.diag_pos (i := y)

omit [Fintype V] [DecidableRel G.Adj] in
/-- Zeros of a nonnegative function that is harmonic away from `y` propagate
along walks inside `D`. -/
lemma zero_propagates_along_walk {u : V → ℝ} {D : Finset V} :
    ∀ {a y : V} (p : G.Walk a y),
      (∀ b ∈ D, b ≠ y → u b = 0 → ∀ w, G.Adj b w → u w = 0) →
      (∀ z ∈ p.support, z ∈ D) → u a = 0 → u y = 0 := by
  intro a y p
  induction p with
  | nil => exact fun _ _ h => h
  | @cons a b c hadj q ih =>
      intro hprop hsupp ha0
      by_cases hay : a = c
      · subst hay; exact ha0
      · have haD : a ∈ D := hsupp a (by simp)
        have hb0 : u b = 0 := hprop a haD hay ha0 b hadj
        refine ih hprop (fun z hz => hsupp z ?_) hb0
        simp only [Walk.support_cons, List.mem_cons]
        exact Or.inr hz

/-- **Strong maximum principle.**  If `x` is joined to `y` by a walk staying
inside `D`, then `g_D(x, y) > 0`. -/
theorem greenFn_pos (hG : G.Connected) {D : Finset V} (hDc : Dᶜ.Nonempty)
    {x y : V} (hx : x ∈ D) (hy : y ∈ D)
    (hwalk : ∃ w : G.Walk x y, ∀ z ∈ w.support, z ∈ D) :
    0 < greenFn G D ⟨x, hx⟩ ⟨y, hy⟩ := by
  classical
  set u : V → ℝ := unitPotential G D y with hu
  have hu_nonneg : ∀ w : V, 0 ≤ u w := by
    intro w
    by_cases hw : w ∈ D
    · rw [hu, unitPotential_apply_mem G hy hw]
      exact greenFn_nonneg G hG hDc _ _
    · simp [hu, unitPotential, hw]
  have huy : 0 < u y := by
    rw [hu, unitPotential_apply_mem G hy hy]
    exact greenFn_diag_pos G hG hDc ⟨y, hy⟩
  have hprop : ∀ a ∈ D, a ≠ y → u a = 0 → ∀ w, G.Adj a w → u w = 0 := by
    intro a ha hay hua w haw
    have hlap : (G.lapMatrix ℝ *ᵥ u) a = 0 := by
      have h := lapMatrix_mulVec_unitPotential G hG hDc hy a ha
      rw [hu]
      simpa [hay] using h
    rw [SimpleGraph.lapMatrix_mulVec_apply, hua] at hlap
    have hsum : ∑ z ∈ G.neighborFinset a, u z = 0 := by linarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hu_nonneg z)).mp hsum
    exact hz w (by simpa using haw)
  obtain ⟨wlk, hwlk⟩ := hwalk
  by_contra hcon
  push_neg at hcon
  have hx0 : u x = 0 := by
    have hux : u x = greenFn G D ⟨x, hx⟩ ⟨y, hy⟩ := by
      rw [hu, unitPotential_apply_mem G hy hx]
    have hnn : 0 ≤ greenFn G D ⟨x, hx⟩ ⟨y, hy⟩ := greenFn_nonneg G hG hDc _ _
    rw [hux]; linarith
  have := zero_propagates_along_walk G wlk hprop hwlk hx0
  linarith

/-- The harmonic measure of a boundary vertex reachable inside `D` is positive. -/
theorem harmMeas_pos_of_walk (hG : G.Connected) {D : Finset V} (hDc : Dᶜ.Nonempty)
    (y : D) {z : V} {x : V} (hx : x ∈ D) (hadj : G.Adj x z)
    (hwalk : ∃ w : G.Walk (y : V) x, ∀ a ∈ w.support, a ∈ D) :
    0 < harmMeas G D y z := by
  have hterm : 0 < greenFn G D y ⟨x, hx⟩ * (if G.Adj x z then (1 : ℝ) else 0) := by
    rw [if_pos hadj, mul_one]
    exact greenFn_pos G hG hDc y.2 hx hwalk
  refine lt_of_lt_of_le hterm ?_
  refine Finset.single_le_sum (f := fun x : D => greenFn G D y x *
      (if G.Adj (x : V) z then (1 : ℝ) else 0)) ?_ (Finset.mem_univ (⟨x, hx⟩ : D))
  intro w _
  refine mul_nonneg (greenFn_nonneg G hG hDc _ _) ?_
  split_ifs <;> norm_num

/-! ### The one-step oscillation contraction for harmonic functions -/

/-- **Oscillation contraction for harmonic functions.**

Let `u` be harmonic on the interior `D` of a cell, let `B` be a set containing
every boundary vertex of `D` (every vertex outside `D` adjacent to `D`), and let
`A` be a subset of the cell all of whose points lie in `D`, with the possible
exception of one distinguished vertex `p ∈ B`.  If the harmonic measure of every
`z ∈ B` seen from every point of `A ∩ D` is at least `ε`, then

`oscOn u A ≤ (1 - ε) * oscOn u B`.

This is the formal counterpart of "a function harmonic in the interior of a cell
has oscillation over each child cell at most `θ` times its oscillation over the
cell", with contraction factor `θ = 1 - ε`. -/
theorem oscOn_contraction_of_harmonic (hG : G.Connected) {D : Finset V} (hDc : Dᶜ.Nonempty)
    {u : V → ℝ} (hu : ∀ x ∈ D, (G.lapMatrix ℝ *ᵥ u) x = 0)
    {A B : Finset V} {p : V} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hpB : p ∈ B) (hBD : B ⊆ Dᶜ)
    (hbdry : ∀ x ∈ D, ∀ z, z ∉ D → G.Adj x z → z ∈ B)
    (hAD : ∀ y ∈ A, y ≠ p → y ∈ D)
    (hpos : ∀ y ∈ A, ∀ hy : y ∈ D, ∀ z ∈ B, ε ≤ harmMeas G D ⟨y, hy⟩ z) :
    oscOn u A ≤ (1 - ε) * oscOn u B := by
  classical
  set w : V → V → ℝ := fun y z => if hy : y ∈ D then harmMeas G D ⟨y, hy⟩ z else 0 with hw
  have hBne : B.Nonempty := ⟨p, hpB⟩
  -- outside `B` the harmonic measure vanishes
  have hzero : ∀ (y : V) (hy : y ∈ D), ∀ z ∈ Dᶜ, z ∉ B → harmMeas G D ⟨y, hy⟩ z = 0 := by
    intro y hy z hz hzB
    refine harmMeas_eq_zero G ⟨y, hy⟩ ?_
    intro x hx hadj
    exact hzB (hbdry x hx z (Finset.mem_compl.mp hz) hadj)
  have hsumB : ∀ (y : V) (hy : y ∈ D), ∑ z ∈ B, harmMeas G D ⟨y, hy⟩ z = 1 := by
    intro y hy
    rw [← harmMeas_sum_one G hG hDc ⟨y, hy⟩]
    refine Finset.sum_subset (f := fun z => harmMeas G D ⟨y, hy⟩ z) hBD ?_
    intro z hz hzB
    exact hzero y hy z hz hzB
  refine oscOn_meanValue_contraction (w := w) (ε := ε) hBne hε0 hε1 hpB ?_ ?_ ?_
  · intro y hy hyp z hz
    have hyD : y ∈ D := hAD y hy hyp
    simpa [hw, hyD] using hpos y hy hyD z hz
  · intro y hy hyp
    have hyD : y ∈ D := hAD y hy hyp
    simpa [hw, hyD] using hsumB y hyD
  · intro y hy hyp
    have hyD : y ∈ D := hAD y hy hyp
    have hrepr := harmonic_repr G hG hDc hu ⟨y, hyD⟩
    have hBsum : ∑ z ∈ Dᶜ, harmMeas G D ⟨y, hyD⟩ z * u z
        = ∑ z ∈ B, harmMeas G D ⟨y, hyD⟩ z * u z := by
      refine (Finset.sum_subset (f := fun z => harmMeas G D ⟨y, hyD⟩ z * u z) hBD ?_).symm
      intro z hz hzB
      show harmMeas G D ⟨y, hyD⟩ z * u z = 0
      rw [hzero y hyD z hz hzB, zero_mul]
    simp only [hw, hyD, dif_pos]
    rw [← hBsum]
    simpa using hrepr

end EIGS
