import Mathlib
import RequestProject.Contraction
import RequestProject.Section2Local

/-!
# Discharging the `hnd` and `hvol` hypotheses of the exit-time lower bound (§2.2)

The conditional lower bound `Section2Green.exit_ge_volume_mul_resistance` was
stated relative to two inputs:

* `hnd`  : a near-diagonal lower bound `c · g_S(v,v) ≤ g_S(v,y)` for `y` in a
  sizeable set `T ⊆ S` (previously carried as an *assumption*, in the spirit of
  an elliptic Harnack comparison);
* `hvol` : a local volume share `c' · V(S) ≤ ∑_{y ∈ T} deg(y)`.

The proof of Lemma 2.22 in the paper *proves* both of these from the oscillation
contraction of harmonic functions along a chain of descendant cells and from the
cell vertex-count estimates of Lemma 2.13.  This file carries that out:

* `green_near_diagonal_of_contraction` — **`hnd` with `c = 1/2`, proved.**  If
  the oscillation of the Dirichlet Green column `g_S(v, ·)` contracts by a factor
  `θ` along a chain of `j` nested cells all containing `v`, with `θ ^ j ≤ 1/2`,
  then `½ · g_S(v,v) ≤ g_S(v,y)` for every `y` in the innermost cell.  The
  contraction hypothesis itself is supplied by
  `Contraction.oscOn_contraction_of_harmonic`, i.e. by the harmonic measure of
  the cells, and is *not* an elliptic Harnack assumption.
* `volume_share_of_disjoint_cells` — **`hvol`, proved** from a family of pairwise
  disjoint descendant cells of controlled size sitting inside `T`, together with
  the (cited) vertex-count bounds; the total degree of `S` is bounded by twice
  the number of edges.
* `exit_ge_of_contraction_and_cells`, `exit_two_sided_of_contraction_and_cells` —
  the assembled exit-time estimates, in which `hnd` and `hvol` no longer appear.
-/

namespace EIGS

open scoped BigOperators
open SimpleGraph Matrix Finset

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### The Green column: harmonicity, bounds, and the oscillation estimate -/

/-- The Green column `g_S(v, ·)` (extended by `0` off `S`) is harmonic at every
vertex of `S` other than `v`. -/
lemma unitPotential_harmonic_off_center (hG : G.Connected) {S : Finset V}
    (hSc : Sᶜ.Nonempty) {v : V} (hv : v ∈ S) {D : Finset V} (hD : D ⊆ S.erase v) :
    ∀ x ∈ D, (G.lapMatrix ℝ *ᵥ unitPotential G S v) x = 0 := by
  intro x hx
  have hx' : x ∈ S.erase v := hD hx
  have hxS : x ∈ S := Finset.mem_of_mem_erase hx'
  have hxv : x ≠ v := Finset.ne_of_mem_erase hx'
  rw [lapMatrix_mulVec_unitPotential G hG hSc hv x hxS, if_neg hxv]

/-- The Green column is bounded between `0` and its diagonal value. -/
lemma unitPotential_le_diag (hG : G.Connected) {S : Finset V} (hSc : Sᶜ.Nonempty)
    {v : V} (hv : v ∈ S) (y : V) :
    0 ≤ unitPotential G S v y ∧ unitPotential G S v y ≤ unitPotential G S v v := by
  have hdiag : unitPotential G S v v = greenFn G S ⟨v, hv⟩ ⟨v, hv⟩ :=
    unitPotential_apply_mem G hv hv
  by_cases hy : y ∈ S
  · rw [unitPotential_apply_mem G hv hy, hdiag]
    refine ⟨greenFn_nonneg G hG hSc _ _, ?_⟩
    rw [green_symm G S ⟨y, hy⟩ ⟨v, hv⟩]
    exact green_le_diag G hG hSc hv ⟨y, hy⟩
  · rw [show unitPotential G S v y = 0 by simp [unitPotential, hy], hdiag]
    exact ⟨le_rfl, greenFn_nonneg G hG hSc _ _⟩

/-- The oscillation of the Green column over any set is at most its diagonal
value. -/
lemma oscOn_unitPotential_le_diag (hG : G.Connected) {S : Finset V} (hSc : Sᶜ.Nonempty)
    {v : V} (hv : v ∈ S) (A : Finset V) :
    oscOn (unitPotential G S v) A ≤ greenFn G S ⟨v, hv⟩ ⟨v, hv⟩ := by
  have hdiag : unitPotential G S v v = greenFn G S ⟨v, hv⟩ ⟨v, hv⟩ :=
    unitPotential_apply_mem G hv hv
  have h0 : (0 : ℝ) ≤ greenFn G S ⟨v, hv⟩ ⟨v, hv⟩ := greenFn_nonneg G hG hSc _ _
  have := oscOn_le_sub (f := unitPotential G S v) (A := A) (a := 0)
    (b := greenFn G S ⟨v, hv⟩ ⟨v, hv⟩) h0
    (fun x _ => (unitPotential_le_diag G hG hSc hv x).1)
    (fun x _ => by simpa [hdiag] using (unitPotential_le_diag G hG hSc hv x).2)
  simpa using this

/-- **One contraction step of the chain, from the geometry of a cell.**

If `D` is the interior of a parent cell `Cpar` (so `D` avoids the centre `v`,
where the Green column fails to be harmonic), `Bdry ⊆ Cpar` contains every
boundary vertex of `D`, the child cell `Cchild` meets `Bdry` at most in the
planting vertex `p`, and the harmonic measure seen from `Cchild ∩ D` is at least
`ε` on `Bdry`, then the oscillation of the Green column contracts by `1 - ε`
from the parent cell to the child cell.  This provides the hypothesis `hstep`
of `green_near_diagonal_of_contraction`. -/
theorem oscOn_step_of_harmonic_cell (hG : G.Connected) {S : Finset V}
    (hSc : Sᶜ.Nonempty) {v : V} (hv : v ∈ S)
    {D Cpar Cchild Bdry : Finset V} {p : V} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hDS : D ⊆ S.erase v) (hDc : Dᶜ.Nonempty)
    (hpB : p ∈ Bdry) (hBD : Bdry ⊆ Dᶜ) (hBpar : Bdry ⊆ Cpar)
    (hbdry : ∀ x ∈ D, ∀ z, z ∉ D → G.Adj x z → z ∈ Bdry)
    (hAD : ∀ y ∈ Cchild, y ≠ p → y ∈ D)
    (hpos : ∀ y ∈ Cchild, ∀ hy : y ∈ D, ∀ z ∈ Bdry, ε ≤ harmMeas G D ⟨y, hy⟩ z) :
    oscOn (unitPotential G S v) Cchild ≤ (1 - ε) * oscOn (unitPotential G S v) Cpar := by
  have hharm := unitPotential_harmonic_off_center G hG hSc hv hDS
  have hstep := oscOn_contraction_of_harmonic G hG hDc hharm hε0 hε1 hpB hBD hbdry hAD hpos
  refine hstep.trans ?_
  exact mul_le_mul_of_nonneg_left (oscOn_mono hBpar) (by linarith)

/-! ### `hnd`, proved from the oscillation contraction -/

/-- **The near-diagonal Green lower bound `hnd`, with `c = 1/2`, proved.**

If the oscillation of the Green column `g_S(v, ·)` contracts by the factor `θ`
along the chain of cells `C 0 ⊇ C 1 ⊇ … ⊇ C j` — the situation produced by
`Contraction.oscOn_contraction_of_harmonic` applied to each substitution step —
and `θ ^ j ≤ 1/2`, then the Green column stays above half its diagonal value on
the innermost cell:

`½ · g_S(v,v) ≤ g_S(v,y)` for all `y ∈ T ⊆ C j`.

This is exactly the input `hnd` of `exit_ge_volume_mul_resistance`, now a
theorem rather than an assumption. -/
theorem green_near_diagonal_of_contraction (hG : G.Connected) {S : Finset V}
    (hSc : Sᶜ.Nonempty) {v : V} (hv : v ∈ S)
    {C : ℕ → Finset V} {j : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθj : θ ^ j ≤ 1 / 2)
    (hvC : v ∈ C j)
    (hstep : ∀ i, i < j →
      oscOn (unitPotential G S v) (C (i + 1)) ≤ θ * oscOn (unitPotential G S v) (C i))
    {T : Finset V} (hTS : T ⊆ S) (hTC : T ⊆ C j) :
    ∀ y : V, ∀ hy : y ∈ T,
      (1 / 2) * greenFn G S ⟨v, hv⟩ ⟨v, hv⟩ ≤ greenFn G S ⟨v, hv⟩ ⟨y, hTS hy⟩ := by
  intro y hy
  have hdiag0 : (0 : ℝ) ≤ greenFn G S ⟨v, hv⟩ ⟨v, hv⟩ := greenFn_nonneg G hG hSc _ _
  -- the oscillation over the innermost cell is at most half the diagonal value
  have hchain : oscOn (unitPotential G S v) (C j)
      ≤ θ ^ j * oscOn (unitPotential G S v) (C 0) :=
    oscOn_chain_pow hθ0 j hstep
  have hosc0 : oscOn (unitPotential G S v) (C 0) ≤ greenFn G S ⟨v, hv⟩ ⟨v, hv⟩ :=
    oscOn_unitPotential_le_diag G hG hSc hv _
  have hoscj : oscOn (unitPotential G S v) (C j)
      ≤ (1 / 2) * greenFn G S ⟨v, hv⟩ ⟨v, hv⟩ := by
    have hpow : (0 : ℝ) ≤ θ ^ j := pow_nonneg hθ0 j
    calc oscOn (unitPotential G S v) (C j)
        ≤ θ ^ j * oscOn (unitPotential G S v) (C 0) := hchain
      _ ≤ θ ^ j * greenFn G S ⟨v, hv⟩ ⟨v, hv⟩ := by
          exact mul_le_mul_of_nonneg_left hosc0 hpow
      _ ≤ (1 / 2) * greenFn G S ⟨v, hv⟩ ⟨v, hv⟩ := by
          exact mul_le_mul_of_nonneg_right hθj hdiag0
  -- hence the value at `y` is at least half the value at `v`
  have hsub : unitPotential G S v v - unitPotential G S v y
      ≤ oscOn (unitPotential G S v) (C j) := sub_le_oscOn hvC (hTC hy)
  have hvv : unitPotential G S v v = greenFn G S ⟨v, hv⟩ ⟨v, hv⟩ :=
    unitPotential_apply_mem G hv hv
  have hvy : unitPotential G S v y = greenFn G S ⟨v, hv⟩ ⟨y, hTS hy⟩ := by
    rw [unitPotential_apply_mem G hv (hTS hy)]
    exact green_symm G S ⟨y, hTS hy⟩ ⟨v, hv⟩
  rw [hvv, hvy] at hsub
  linarith

/-! ### `hvol`, proved from a disjoint family of descendant cells -/

omit [DecidableEq V] in
/-- The volume (total degree) of any set is at most twice the number of edges. -/
lemma volume_le_two_card_edges (S : Finset V) :
    volume G S ≤ 2 * (G.edgeFinset.card : ℝ) := by
  have hsub : ∑ x ∈ S, (G.degree x : ℝ) ≤ ∑ x : V, (G.degree x : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) ?_
    intro i _ _
    positivity
  have htot : ∑ x : V, (G.degree x : ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
    have := SimpleGraph.sum_degrees_eq_twice_card_edges G
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this
  rw [volume]
  linarith [hsub, htot.le, htot.ge]

/-- **The local volume share `hvol`, proved.**

Let `Λ i` be a family of descendant cells, pairwise disjoint once the common
centre `v` is removed, each of them containing at least `K` vertices and sitting
(after removal of `v`) inside `T`.  If the volume of `S` is at most `B` and
`c' · B ≤ |ι| · (K - 1)`, then `T` carries at least the fraction `c'` of the
volume of `S`:

`c' · V(S) ≤ ∑_{y ∈ T} deg(y)`.

Together with `volume_le_two_card_edges` and the (cited) vertex-count bounds of
Lemma 2.13, this is exactly the counting step of the proof of Lemma 2.22. -/
theorem volume_share_of_disjoint_cells {S T : Finset V} {v : V}
    {ι : Type} [Fintype ι] (Λ : ι → Finset V) {K B c' : ℝ} (hc' : 0 ≤ c')
    (hsub : ∀ i, (Λ i).erase v ⊆ T)
    (hdisj : ∀ i i', i ≠ i' → Disjoint ((Λ i).erase v) ((Λ i').erase v))
    (hcard : ∀ i, K ≤ ((Λ i).card : ℝ))
    (hdeg : ∀ y ∈ T, (1 : ℝ) ≤ (G.degree y : ℝ))
    (hvolS : volume G S ≤ B)
    (hB : c' * B ≤ (Fintype.card ι : ℝ) * (K - 1)) :
    c' * volume G S ≤ ∑ y ∈ T, (G.degree y : ℝ) := by
  classical
  -- the union of the punctured cells sits inside `T`
  have hunion : (Finset.univ : Finset ι).biUnion (fun i => (Λ i).erase v) ⊆ T := by
    intro y hy
    obtain ⟨i, _, hyi⟩ := Finset.mem_biUnion.mp hy
    exact hsub i hyi
  have hcards : ((Finset.univ : Finset ι).biUnion (fun i => (Λ i).erase v)).card
      = ∑ i : ι, ((Λ i).erase v).card := by
    refine Finset.card_biUnion ?_
    intro i _ i' _ hne
    exact hdisj i i' hne
  -- each punctured cell has at least `K - 1` vertices
  have hpunct : ∀ i : ι, K - 1 ≤ (((Λ i).erase v).card : ℝ) := by
    intro i
    have h1 : ((Λ i).card : ℝ) - 1 ≤ (((Λ i).erase v).card : ℝ) := by
      by_cases hv : v ∈ Λ i
      · rw [Finset.card_erase_of_mem hv]
        have h2 : 1 ≤ (Λ i).card := Finset.card_pos.mpr ⟨v, hv⟩
        have : ((Λ i).card - 1 : ℕ) = (Λ i).card - 1 := rfl
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
  -- the number of vertices of `T` bounds the volume from below
  have hTcard : ((T.card : ℕ) : ℝ) ≤ ∑ y ∈ T, (G.degree y : ℝ) := by
    calc ((T.card : ℕ) : ℝ) = ∑ _y ∈ T, (1 : ℝ) := by simp
      _ ≤ ∑ y ∈ T, (G.degree y : ℝ) := Finset.sum_le_sum hdeg
  have hbig : ((((Finset.univ : Finset ι).biUnion (fun i => (Λ i).erase v)).card : ℕ) : ℝ)
      ≤ ((T.card : ℕ) : ℝ) := by
    exact_mod_cast Finset.card_le_card hunion
  have hcvol : c' * volume G S ≤ c' * B := mul_le_mul_of_nonneg_left hvolS hc'
  linarith

/-! ### The assembled exit-time estimates, free of `hnd` and `hvol` -/

/-- **Exit-time lower bound with `hnd` discharged.**  Only the oscillation
contraction along a chain of cells (an output of the harmonic-measure machinery)
and the local volume share are used. -/
theorem exit_ge_of_contraction (hG : G.Connected) {S : Finset V} (hSc : Sᶜ.Nonempty)
    {τ : V → ℝ} (hτ : ExitSystem G S τ) {v : V} (hv : v ∈ S)
    {C : ℕ → Finset V} {j : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθj : θ ^ j ≤ 1 / 2)
    (hvC : v ∈ C j)
    (hstep : ∀ i, i < j →
      oscOn (unitPotential G S v) (C (i + 1)) ≤ θ * oscOn (unitPotential G S v) (C i))
    {T : Finset V} (hTS : T ⊆ S) (hTC : T ⊆ C j) {c' : ℝ}
    (hvol : c' * volume G S ≤ ∑ y ∈ T, (G.degree y : ℝ)) :
    (1 / 2) * c' * effResToBoundary G S v * volume G S ≤ τ v :=
  exit_ge_volume_mul_resistance G hG hSc hτ hv hTS (by norm_num)
    (green_near_diagonal_of_contraction G hG hSc hv hθ0 hθj hvC hstep hTS hTC) hvol

/-- **Two-sided exit-time estimate with both `hnd` and `hvol` discharged.**

The remaining inputs are exactly the two ingredients of the proof of Lemma 2.22:
the oscillation contraction along a chain of descendant cells, and a disjoint
family of descendant cells of controlled cardinality inside `T` (whose size is
given by the cited vertex-count estimates of Lemma 2.13). -/
theorem exit_two_sided_of_cells (hG : G.Connected) {S : Finset V} (hSc : Sᶜ.Nonempty)
    {τ : V → ℝ} (hτ : ExitSystem G S τ) {v : V} (hv : v ∈ S)
    {C : ℕ → Finset V} {j : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθj : θ ^ j ≤ 1 / 2)
    (hvC : v ∈ C j)
    (hstep : ∀ i, i < j →
      oscOn (unitPotential G S v) (C (i + 1)) ≤ θ * oscOn (unitPotential G S v) (C i))
    {T : Finset V} (hTS : T ⊆ S) (hTC : T ⊆ C j)
    {ι : Type} [Fintype ι] (Λ : ι → Finset V) {K B c' : ℝ} (hc' : 0 ≤ c')
    (hsub : ∀ i, (Λ i).erase v ⊆ T)
    (hdisj : ∀ i i', i ≠ i' → Disjoint ((Λ i).erase v) ((Λ i').erase v))
    (hcard : ∀ i, K ≤ ((Λ i).card : ℝ))
    (hdeg : ∀ y ∈ T, (1 : ℝ) ≤ (G.degree y : ℝ))
    (hvolS : volume G S ≤ B)
    (hB : c' * B ≤ (Fintype.card ι : ℝ) * (K - 1)) :
    (1 / 2) * c' * effResToBoundary G S v * volume G S ≤ τ v
      ∧ τ v ≤ effResToBoundary G S v * volume G S := by
  refine ⟨exit_ge_of_contraction G hG hSc hτ hv hθ0 hθj hvC hstep hTS hTC
    (volume_share_of_disjoint_cells G Λ hc' hsub hdisj hcard hdeg hvolS hB),
    exit_le_volume_mul_resistance G hG hSc hτ hv⟩

/-- **The ball version: `exit_two_sided_local` with `hnd` and `hvol` removed.**

This is the direct replacement of `Section2Local.exit_two_sided_local`, whose
near-diagonal Green hypothesis `hnd` and volume-doubling hypothesis are here
replaced by the oscillation contraction along a chain of cells and by a disjoint
family of descendant cells inside the inner ball. -/
theorem exit_two_sided_local_of_cells (hG : G.Connected) {o : V} {r : ℕ}
    (hSc : (graphBall G o (2 * r))ᶜ.Nonempty)
    {τ : V → ℝ} (hτ : ExitSystem G (graphBall G o (2 * r)) τ)
    {C : ℕ → Finset V} {j : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθj : θ ^ j ≤ 1 / 2)
    (hoC : o ∈ C j)
    (hstep : ∀ i, i < j →
      oscOn (unitPotential G (graphBall G o (2 * r)) o) (C (i + 1))
        ≤ θ * oscOn (unitPotential G (graphBall G o (2 * r)) o) (C i))
    (hTC : graphBall G o r ⊆ C j)
    {ι : Type} [Fintype ι] (Λ : ι → Finset V) {K B c' : ℝ} (hc' : 0 ≤ c')
    (hsub : ∀ i, (Λ i).erase o ⊆ graphBall G o r)
    (hdisj : ∀ i i', i ≠ i' → Disjoint ((Λ i).erase o) ((Λ i').erase o))
    (hcard : ∀ i, K ≤ ((Λ i).card : ℝ))
    (hdeg : ∀ y ∈ graphBall G o r, (1 : ℝ) ≤ (G.degree y : ℝ))
    (hvolS : volume G (graphBall G o (2 * r)) ≤ B)
    (hB : c' * B ≤ (Fintype.card ι : ℝ) * (K - 1)) :
    (1 / 2) * c' * effResToBoundary G (graphBall G o (2 * r)) o
        * volume G (graphBall G o (2 * r)) ≤ τ o
      ∧ τ o ≤ effResToBoundary G (graphBall G o (2 * r)) o
        * volume G (graphBall G o (2 * r)) :=
  exit_two_sided_of_cells G hG hSc hτ (self_mem_graphBall G o (2 * r)) hθ0 hθj hoC hstep
    (graphBall_mono G o (by omega)) hTC Λ hc' hsub hdisj hcard hdeg hvolS hB

end EIGS
