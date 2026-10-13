import Mathlib
import RequestProject.Section2Local

/-!
# Lemma 2.14 (local mass estimate) on the graph side

This file formalises, on the *graph* side, the trimmed statement of Lemma 2.14
of the paper together with the **`a₀`-shift proof of its upper bound**, and the
matching counting proof of the lower bound.

Recall the statement of the paper: for a `k`-born vertex `v ∈ Vₖ(Ξⁿ)` and a
radius `r` with `c_d ρ_min(D)^m ≤ r ≤ C_d ρ_min(D)^m` and `m ≤ n - k - a₀`,

  `c_lm ρ(N)^{n-k-m} ρ(M)^m ≤ |V(B_{Ξⁿ}(v, r))| ≤ C_lm ρ(N)^{n-k-m} ρ(M)^m`,

where the integer `a₀` is fixed once and for all by `C_d ρ_min(D)^{-a₀} ≤ c_d`.

The mechanism of the upper-bound proof is entirely captured by the following
three steps, which are what is formalised here.

* `radius_le_of_a0_shift` — the arithmetic of the `a₀` shift: the choice of `a₀`
  makes the level-`(m + a₀)` distance lower bound `c_d ρ_min^{m+a₀}` exceed the
  radius `r ≤ C_d ρ_min^m`, so the far endpoints `b_e` of the coarse edges lie
  *outside* the ball.

* `graphBall_subset_of_separators` — the graph-theoretic core: if every walk
  leaving the union `F` of the branches must pass through one of the separating
  vertices `b_e`, and each `b_e` is farther than `r` from `v`, then
  `B(v, r) ⊆ F`.

* `graphBall_card_le_of_cover` / `local_mass_upper_bound` — the counting: the
  ball is covered by `deg` branches of at most `C_V ρ(M)^{m+a₀}` vertices each,
  which after absorbing `ρ(M)^{a₀}` into the constant gives the upper bound
  `C_V C_deg ρ(M)^{a₀} · ρ(N)^{n-k-m} ρ(M)^m`.

For the lower bound (`local_mass_lower_bound`) the corresponding counting step
is the disjointness of the punctured descendant cells `V(Λ_e) \ {v}`, all of
which lie inside the ball by the diameter bound.

`local_mass_two_sided` assembles the two halves into the trimmed form of
Lemma 2.14.
-/

namespace EIGS

open scoped BigOperators
open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### The arithmetic of the `a₀` shift -/

/-- **The `a₀` shift.**  With `a₀` chosen so that `C_d ρ_min^{-a₀} ≤ c_d`
(equivalently `C_d ≤ c_d ρ_min^{a₀}`), a radius `r ≤ C_d ρ_min^m` is dominated by
the level-`(m + a₀)` distance lower bound `c_d ρ_min^{m + a₀}`.  This is the step
"`d(vₖⁿ, b_e) ≥ c_d ρ_min^{m+a₀} ≥ C_d ρ_min^m ≥ r`" of the proof of Lemma 2.14. -/
theorem radius_le_of_a0_shift {cd Cd rho r : ℝ} {m a0 : ℕ}
    (hrho : 0 ≤ rho) (hshift : Cd ≤ cd * rho ^ a0) (hr : r ≤ Cd * rho ^ m) :
    r ≤ cd * rho ^ (m + a0) := by
  have hpow : (0 : ℝ) ≤ rho ^ m := pow_nonneg hrho m
  have h1 : Cd * rho ^ m ≤ (cd * rho ^ a0) * rho ^ m :=
    mul_le_mul_of_nonneg_right hshift hpow
  have h2 : (cd * rho ^ a0) * rho ^ m = cd * rho ^ (m + a0) := by
    rw [pow_add]; ring
  linarith

/-! ### The geometric core: separators push the ball inside the branches -/

/-- **Ball inclusion from separation.**  Suppose every walk from `v` to a vertex
outside `F` meets the separating set `Sep`, and every separating vertex is at
distance more than `r` from `v`.  Then the ball `B(v, r)` is contained in `F`.

In the situation of Lemma 2.14, `F` is the union of the `(m + a₀)`-step
substituted copies `H_e^{(m+a₀)}` of the coarse edges at `v`, and `Sep` is the
set of their far endpoints `b_e`; the distance hypothesis is provided by
`radius_le_of_a0_shift`. -/
theorem graphBall_subset_of_separators (hG : G.Connected) {v : V} {r : ℕ}
    {F Sep : Finset V}
    (hsep : ∀ y : V, y ∉ F → ∀ w : G.Walk v y, ∃ b ∈ Sep, b ∈ w.support)
    (hfar : ∀ b ∈ Sep, r < G.dist v b) :
    graphBall G v r ⊆ F := by
  classical
  intro y hy
  have hdy : G.dist v y ≤ r := by
    simpa [graphBall] using hy
  by_contra hyF
  -- a geodesic from `v` to `y`
  obtain ⟨w, hw⟩ := (hG.preconnected v y).exists_walk_length_eq_dist
  obtain ⟨b, hbSep, hbw⟩ := hsep y hyF w
  have hpre : G.dist v b ≤ (w.takeUntil b hbw).length :=
    SimpleGraph.dist_le (w.takeUntil b hbw)
  have hle : (w.takeUntil b hbw).length ≤ w.length :=
    SimpleGraph.Walk.length_takeUntil_le w hbw
  have : G.dist v b ≤ r := by
    have : (w.length : ℕ) = G.dist v y := hw
    omega
  exact absurd this (not_le.mpr (hfar b hbSep))

/-- **The `a₀`-shift ball inclusion.**  The two previous steps combined: with
`a₀` chosen so that `C_d ρ_min^{-a₀} ≤ c_d`, a radius `r ≤ C_d ρ_min^m`, and
separating vertices at distance more than `c_d ρ_min^{m+a₀}` from `v`, the ball
`B(v,r)` is contained in the union `F` of the branches. -/
theorem graphBall_subset_of_a0_shift (hG : G.Connected) {v : V} {r : ℕ}
    {F Sep : Finset V} {cd Cd rho : ℝ} {m a0 : ℕ}
    (hrho : 0 ≤ rho) (hshift : Cd ≤ cd * rho ^ a0) (hr : (r : ℝ) ≤ Cd * rho ^ m)
    (hsep : ∀ y : V, y ∉ F → ∀ w : G.Walk v y, ∃ b ∈ Sep, b ∈ w.support)
    (hdist : ∀ b ∈ Sep, cd * rho ^ (m + a0) < (G.dist v b : ℝ)) :
    graphBall G v r ⊆ F := by
  refine graphBall_subset_of_separators G hG hsep ?_
  intro b hb
  have h1 : (r : ℝ) ≤ cd * rho ^ (m + a0) := radius_le_of_a0_shift hrho hshift hr
  have h2 : (r : ℝ) < (G.dist v b : ℝ) := lt_of_le_of_lt h1 (hdist b hb)
  exact_mod_cast h2

/-! ### Counting: the covering upper bound -/

/-- If a ball is covered by finitely many cells of size at most `Ccell`, its
cardinality is at most the number of cells times `Ccell`. -/
theorem graphBall_card_le_of_cover {v : V} {r : ℕ} {ι : Type} [Fintype ι]
    (H : ι → Finset V) (hcover : graphBall G v r ⊆ Finset.univ.biUnion H)
    {Ccell : ℝ} (hcell : ∀ i, ((H i).card : ℝ) ≤ Ccell) :
    ((graphBall G v r).card : ℝ) ≤ (Fintype.card ι : ℝ) * Ccell := by
  classical
  have h1 : (graphBall G v r).card ≤ (Finset.univ.biUnion H).card :=
    Finset.card_le_card hcover
  have h2 : (Finset.univ.biUnion H).card ≤ ∑ i : ι, (H i).card :=
    Finset.card_biUnion_le
  have h3 : ((∑ i : ι, (H i).card : ℕ) : ℝ) ≤ ∑ i : ι, ((H i).card : ℝ) := by
    push_cast
    exact le_rfl
  have h4 : ∑ i : ι, ((H i).card : ℝ) ≤ (Fintype.card ι : ℝ) * Ccell := by
    calc ∑ i : ι, ((H i).card : ℝ) ≤ ∑ _i : ι, Ccell :=
          Finset.sum_le_sum fun i _ => hcell i
      _ = (Fintype.card ι : ℝ) * Ccell := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h12 : ((graphBall G v r).card : ℝ) ≤ ((∑ i : ι, (H i).card : ℕ) : ℝ) := by
    exact_mod_cast le_trans h1 h2
  linarith

/-- **Lemma 2.14, upper bound (the `a₀`-shift proof).**

Let the ball `B(v,r)` be covered by the branches `H i` (one for each coarse edge
at `v` at level `n - m - a₀`), each of which has at most `C_V ρ(M)^{m+a₀}`
vertices (Lemma 2.13), and let the number of branches — the degree of `v` at
level `n - m - a₀` — be at most `C_deg ρ(N)^{q'}` with `q' + a₀ = q`
(`q = n - k - m`).  Then

`|V(B(v,r))| ≤ (C_V C_deg ρ(M)^{a₀}) · ρ(N)^q ρ(M)^m`,

which is the upper half of Lemma 2.14 with `C_lm = C_V C_deg ρ(M)^{a₀}`. -/
theorem local_mass_upper_bound {v : V} {r : ℕ} {ι : Type} [Fintype ι]
    (H : ι → Finset V) (hcover : graphBall G v r ⊆ Finset.univ.biUnion H)
    {CV Cdeg rhoM rhoN : ℝ} {m a0 q q' : ℕ} (hq : q' + a0 = q)
    (hCV : 0 ≤ CV) (hCdeg : 0 ≤ Cdeg) (hrhoM : 0 ≤ rhoM) (hrhoN : 1 ≤ rhoN)
    (hdeg : (Fintype.card ι : ℝ) ≤ Cdeg * rhoN ^ q')
    (hcell : ∀ i, ((H i).card : ℝ) ≤ CV * rhoM ^ (m + a0)) :
    ((graphBall G v r).card : ℝ) ≤ (CV * Cdeg * rhoM ^ a0) * (rhoN ^ q * rhoM ^ m) := by
  have hCcell : (0 : ℝ) ≤ CV * rhoM ^ (m + a0) := by positivity
  have hcover_bd := graphBall_card_le_of_cover G H hcover hcell
  have hmul : (Fintype.card ι : ℝ) * (CV * rhoM ^ (m + a0))
      ≤ (Cdeg * rhoN ^ q') * (CV * rhoM ^ (m + a0)) :=
    mul_le_mul_of_nonneg_right hdeg hCcell
  have hq' : rhoN ^ q' ≤ rhoN ^ q := by
    refine pow_le_pow_right₀ hrhoN ?_
    omega
  have hpos : (0 : ℝ) ≤ Cdeg * (CV * rhoM ^ (m + a0)) := by positivity
  have hfin : (Cdeg * rhoN ^ q') * (CV * rhoM ^ (m + a0))
      ≤ (CV * Cdeg * rhoM ^ a0) * (rhoN ^ q * rhoM ^ m) := by
    have : (Cdeg * rhoN ^ q') * (CV * rhoM ^ (m + a0))
        = (Cdeg * (CV * rhoM ^ (m + a0))) * rhoN ^ q' := by ring
    rw [this]
    calc (Cdeg * (CV * rhoM ^ (m + a0))) * rhoN ^ q'
        ≤ (Cdeg * (CV * rhoM ^ (m + a0))) * rhoN ^ q :=
          mul_le_mul_of_nonneg_left hq' hpos
      _ = (CV * Cdeg * rhoM ^ a0) * (rhoN ^ q * rhoM ^ m) := by
          rw [pow_add]; ring
  linarith

/-- **Lemma 2.14, upper bound, full `a₀`-shift proof.**  The covering hypothesis
of `local_mass_upper_bound` is itself obtained from the separation of the
branches and the `a₀` shift. -/
theorem local_mass_upper_bound_of_a0_shift (hG : G.Connected) {v : V} {r : ℕ}
    {Sep : Finset V} {ι : Type} [Fintype ι] (H : ι → Finset V)
    {cd Cd rho : ℝ} {CV Cdeg rhoM rhoN : ℝ} {m a0 q q' : ℕ} (hq : q' + a0 = q)
    (hrho : 0 ≤ rho) (hshift : Cd ≤ cd * rho ^ a0) (hr : (r : ℝ) ≤ Cd * rho ^ m)
    (hsep : ∀ y : V, y ∉ Finset.univ.biUnion H → ∀ w : G.Walk v y,
      ∃ b ∈ Sep, b ∈ w.support)
    (hdist : ∀ b ∈ Sep, cd * rho ^ (m + a0) < (G.dist v b : ℝ))
    (hCV : 0 ≤ CV) (hCdeg : 0 ≤ Cdeg) (hrhoM : 0 ≤ rhoM) (hrhoN : 1 ≤ rhoN)
    (hdeg : (Fintype.card ι : ℝ) ≤ Cdeg * rhoN ^ q')
    (hcell : ∀ i, ((H i).card : ℝ) ≤ CV * rhoM ^ (m + a0)) :
    ((graphBall G v r).card : ℝ) ≤ (CV * Cdeg * rhoM ^ a0) * (rhoN ^ q * rhoM ^ m) :=
  local_mass_upper_bound G H
    (graphBall_subset_of_a0_shift G hG hrho hshift hr hsep hdist)
    hq hCV hCdeg hrhoM hrhoN hdeg hcell

/-! ### Counting: the disjoint-subcell lower bound -/

/-- **Lemma 2.14, lower bound (the disjoint descendant cells).**

If the descendant cells `Λ i` all lie inside the ball (by the diameter bound
`diam(Λ_e) ≤ C_d ρ_min^{m-a₀} ≤ r`), are pairwise disjoint after removing the
common centre `v`, and each has at least `K` vertices, then the ball contains at
least `|ι| · (K - 1)` vertices. -/
theorem local_mass_lower_bound {v : V} {r : ℕ} {ι : Type} [Fintype ι]
    (Λ : ι → Finset V) (hΛ : ∀ i, Λ i ⊆ graphBall G v r)
    (hdisj : ∀ i i', i ≠ i' → Disjoint ((Λ i).erase v) ((Λ i').erase v))
    {K : ℝ} (hcard : ∀ i, K ≤ ((Λ i).card : ℝ)) :
    (Fintype.card ι : ℝ) * (K - 1) ≤ ((graphBall G v r).card : ℝ) := by
  classical
  have hunion : (Finset.univ : Finset ι).biUnion (fun i => (Λ i).erase v)
      ⊆ graphBall G v r := by
    intro y hy
    obtain ⟨i, _, hyi⟩ := Finset.mem_biUnion.mp hy
    exact hΛ i (Finset.mem_of_mem_erase hyi)
  have hcards : ((Finset.univ : Finset ι).biUnion (fun i => (Λ i).erase v)).card
      = ∑ i : ι, ((Λ i).erase v).card :=
    Finset.card_biUnion fun i _ i' _ hne => hdisj i i' hne
  have hpunct : ∀ i : ι, K - 1 ≤ (((Λ i).erase v).card : ℝ) := by
    intro i
    have h1 : ((Λ i).card : ℝ) - 1 ≤ (((Λ i).erase v).card : ℝ) := by
      by_cases hv : v ∈ Λ i
      · rw [Finset.card_erase_of_mem hv]
        have h2 : 1 ≤ (Λ i).card := Finset.card_pos.mpr ⟨v, hv⟩
        push_cast [Nat.cast_sub h2]
        linarith
      · rw [Finset.erase_eq_of_notMem hv]
        linarith
    linarith [hcard i]
  have hsum : (Fintype.card ι : ℝ) * (K - 1)
      ≤ ((((Finset.univ : Finset ι).biUnion (fun i => (Λ i).erase v)).card : ℕ) : ℝ) := by
    rw [hcards]
    push_cast
    calc (Fintype.card ι : ℝ) * (K - 1) = ∑ _i : ι, (K - 1) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
      _ ≤ ∑ i : ι, (((Λ i).erase v).card : ℝ) := Finset.sum_le_sum fun i _ => hpunct i
  have hle : ((((Finset.univ : Finset ι).biUnion (fun i => (Λ i).erase v)).card : ℕ) : ℝ)
      ≤ ((graphBall G v r).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hunion
  linarith

/-! ### The trimmed form of Lemma 2.14 -/

/-- **Lemma 2.14 (trimmed form).**

Combining the two counting arguments: with the branches `H i` covering the ball
(via the `a₀` shift) and the descendant cells `Λ i` sitting inside it, the ball
volume is two-sidedly comparable to `ρ(N)^q ρ(M)^m`, where `q = n - k - m`:

`(cdeg · cV / 2) · ρ(N)^q ρ(M)^m ≤ |V(B(v,r))| ≤ (C_V C_deg ρ(M)^{a₀}) · ρ(N)^q ρ(M)^m`.

The lower constant comes from `|V(Λ)| - 1 ≥ |V(Λ)|/2`, valid because the cells
have at least two vertices. -/
theorem local_mass_two_sided {v : V} {r : ℕ}
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (H : ι → Finset V) (Λ : κ → Finset V)
    (hcover : graphBall G v r ⊆ Finset.univ.biUnion H)
    (hΛ : ∀ i, Λ i ⊆ graphBall G v r)
    (hdisj : ∀ i i', i ≠ i' → Disjoint ((Λ i).erase v) ((Λ i').erase v))
    {CV Cdeg cV cdeg rhoM rhoN : ℝ} {m a0 q q' : ℕ} (hq : q' + a0 = q)
    (hCV : 0 ≤ CV) (hCdeg : 0 ≤ Cdeg) (hrhoM : 0 ≤ rhoM) (hrhoN : 1 ≤ rhoN)
    (hcdeg : 0 ≤ cdeg)
    (hdeg : (Fintype.card ι : ℝ) ≤ Cdeg * rhoN ^ q')
    (hcell : ∀ i, ((H i).card : ℝ) ≤ CV * rhoM ^ (m + a0))
    (hdeg' : cdeg * rhoN ^ q ≤ (Fintype.card κ : ℝ))
    (hcell' : ∀ i, 2 * (cV * rhoM ^ m) ≤ ((Λ i).card : ℝ))
    (hbig : 1 ≤ cV * rhoM ^ m) :
    (cdeg * cV) * (rhoN ^ q * rhoM ^ m) ≤ ((graphBall G v r).card : ℝ)
      ∧ ((graphBall G v r).card : ℝ)
          ≤ (CV * Cdeg * rhoM ^ a0) * (rhoN ^ q * rhoM ^ m) := by
  refine ⟨?_, local_mass_upper_bound G H hcover hq hCV hCdeg hrhoM hrhoN hdeg hcell⟩
  have hlow := local_mass_lower_bound G Λ hΛ hdisj (K := 2 * (cV * rhoM ^ m)) hcell'
  have hstep : (cdeg * rhoN ^ q) * (2 * (cV * rhoM ^ m) - 1)
      ≤ (Fintype.card κ : ℝ) * (2 * (cV * rhoM ^ m) - 1) := by
    refine mul_le_mul_of_nonneg_right hdeg' ?_
    linarith
  have hhalf : (cdeg * rhoN ^ q) * (cV * rhoM ^ m)
      ≤ (cdeg * rhoN ^ q) * (2 * (cV * rhoM ^ m) - 1) := by
    refine mul_le_mul_of_nonneg_left (by linarith) ?_
    have : (0 : ℝ) ≤ rhoN ^ q := by positivity
    positivity
  have hfin : (cdeg * cV) * (rhoN ^ q * rhoM ^ m)
      = (cdeg * rhoN ^ q) * (cV * rhoM ^ m) := by ring
  rw [hfin]
  linarith

end EIGS
