import Mathlib
import RequestProject.Section2ExitScaling

/-!
# Local volume / resistance / Green comparison on balls (Section 2.2)

This file carries out the **local** part of the `E[τ] ≍ V·R` programme of §2.2,
turning the *global* geometric growth estimates (geometric in the substitution
level `n`) into genuine **power laws in the radius** `r`, and reducing the two
`local geometry` inputs of the conditional exit-time lower bound
(`Section2Green.exit_ge_volume_mul_resistance`) to standard, clean local
hypotheses.

## What is genuinely proved here

* **`geometric_radius_power`** — the analytic heart.  If a graph quantity `Q n`
  grows geometrically in the level, `Q n ≍ a^n`, while the radius scales as
  `r n ≍ σ^n` (with `a > 0`, `σ > 1`), then `Q` obeys a two-sided **power law in
  the radius**,
  `C₁ · (r n)^d ≤ Q n ≤ C₂ · (r n)^d`,  where `d = log a / log σ`.
  This is exactly the mechanism converting `|E(Ξⁿ)| ≍ ρ(M)^n`, `ℛ(Ξⁿ) ≍ ρ(Ψ)^n`
  and `diam ≍ ρ_min^n` into `V(B(o,r)) ≍ r^{d_f}` and `R ≍ r^ζ`.

* **`ballVolume_power_law`** — `V(B(o,r)) ≍ r^{d_f}` with `d_f = log ρN / log ρmin`
  (Lemma 2.14 in radius form), an instance of `geometric_radius_power`.

* **`ballResistance_power_law`** — `R(o, B(o,r)ᶜ) ≍ r^ζ` with `ζ = log ρΨ/log ρmin`
  (Lemma 2.17 in radius form).

* **`exit_time_radius_power`** — from `E[τ] ≍ V·R`, `V(B) ≍ r^{d_f}` and
  `R ≍ r^ζ`, the exit time obeys the walk-dimension power law
  `E[τ] ≍ r^{d_f + ζ} = r^{d_w}`, using `r^{d_f}·r^{ζ} = r^{d_f+ζ}`.

* **`graphBall`, `ballVolume`, `graphBall_mono`** — graph metric balls and their
  degree-volume, monotone in the radius.

* **`volume_doubling_regularity`** — the **local volume regularity** input
  `hvol` of the conditional lower bound is *derived* from **volume doubling**
  `V(B(o,2r)) ≤ D·V(B(o,r))`: then `D⁻¹·V(B(o,2r)) ≤ V(B(o,r))`.

* **`exit_two_sided_local`** — assembling: on a graph metric ball, with volume
  doubling (giving `hvol`) and the near-diagonal Green lower bound `hnd` (the
  elliptic-Harnack input, cited), the two-sided estimate
  `c·D⁻¹·R·V ≤ E[τ] ≤ R·V` holds.

## What is cited (as explicit hypotheses)

The per-level geometric growth of ball volume / resistance and of
`diam ≍ ρ_min^n` ([38]) is cited.  **Volume doubling** is the clean hypothesis
from which local volume regularity is *proved* here, and the power laws in the
radius are *proved* from the geometric growth + distance scaling.

## Update: `hnd` and `hvol` are no longer needed

The near-diagonal Green comparison `hnd` of `exit_two_sided_local` below (and
the volume-doubling input) are **no longer assumptions** of the development:
`RequestProject/Section2NearDiagonal.lean` proves them, following the proof of
Lemma 2.22, from the oscillation contraction of harmonic functions along a chain
of descendant cells (`oscOn_step_of_harmonic_cell`, itself a consequence of the
harmonic-measure machinery of `RequestProject/Contraction.lean`) and from the
disjointness and cardinality of the descendant cells.  See
`green_near_diagonal_of_contraction`, `volume_share_of_disjoint_cells`, and the
assembled `exit_two_sided_of_cells` / `exit_two_sided_local_of_cells`, which are
the replacements of the conditional statement `exit_two_sided_local` kept below.
-/

namespace EIGS

open scoped BigOperators
open SimpleGraph Matrix Finset Filter Topology

/-! ### The analytic core: geometric level growth ⟹ power law in the radius -/

/-
**Geometric growth ⟹ radius power law.**  If `Q n ≍ a^n` (geometric in the
level) and the radius `r n ≍ σ^n` with `a > 0`, `σ > 1`, then `Q` obeys the
two-sided power law `C₁ (r n)^d ≤ Q n ≤ C₂ (r n)^d` in the radius, where
`d = log a / log σ` (`rpow`).  This is the exact mechanism that turns the
level-geometric growth of volume/resistance into the local `r`-power laws
`V(B)≍r^{d_f}`, `R≍r^ζ`.
-/
theorem geometric_radius_power
    {Q r : ℕ → ℝ} {a σ : ℝ}
    (ha : 0 < a) (hσ : 1 < σ)
    (hQ : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ n, c₁ * a ^ n ≤ Q n ∧ Q n ≤ c₂ * a ^ n)
    (hr : ∃ c₃ c₄ : ℝ, 0 < c₃ ∧ 0 < c₄ ∧ ∀ n, c₃ * σ ^ n ≤ r n ∧ r n ≤ c₄ * σ ^ n) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ n, C₁ * (r n) ^ (Real.log a / Real.log σ) ≤ Q n
        ∧ Q n ≤ C₂ * (r n) ^ (Real.log a / Real.log σ) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hQ⟩ := hQ
  obtain ⟨c₃, c₄, hc₃, hc₄, hr⟩ := hr
  set d := Real.log a / Real.log σ with hd
  have hd_pos : 0 < σ ^ d := by
    positivity
  have hd_pow : ∀ n, (σ ^ n) ^ d = a ^ n := by
    intro n; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_comm, Real.rpow_mul ( by positivity ), Real.rpow_def_of_pos ( by positivity ), Real.rpow_def_of_pos ( by positivity ) ] ; ring_nf ;
    rw [ Real.log_exp, mul_div_cancel₀ _ ( ne_of_gt ( Real.log_pos hσ ) ), Real.exp_mul, Real.exp_log ha ] ; norm_cast;
  -- We have `0 < r n` from `hr` and `c₃ * σ^n > 0 ≤ r n`.
  -- Now compare `(r n)^d` with `(σ^n)^d = a^n`.
  have h_rpow_bounds : ∃ m₁ m₂ : ℝ, 0 < m₁ ∧ 0 < m₂ ∧ ∀ n, m₁ * a ^ n ≤ (r n) ^ d ∧ (r n) ^ d ≤ m₂ * a ^ n := by
    by_cases hd_nonneg : 0 ≤ d;
    · refine' ⟨ c₃ ^ d, c₄ ^ d, Real.rpow_pos_of_pos hc₃ _, Real.rpow_pos_of_pos hc₄ _, fun n => ⟨ _, _ ⟩ ⟩;
      · rw [ ← hd_pow n, ← Real.mul_rpow ( by positivity ) ( by positivity ) ] ; exact Real.rpow_le_rpow ( by positivity ) ( hr n |>.1 ) hd_nonneg;
      · exact le_trans ( Real.rpow_le_rpow ( by nlinarith [ hr n, show 0 < σ ^ n by positivity ] ) ( hr n |>.2 ) hd_nonneg ) ( by rw [ Real.mul_rpow ( by positivity ) ( by positivity ), ← hd_pow n ] );
    · refine' ⟨ c₄ ^ d, c₃ ^ d, _, _, _ ⟩;
      · positivity;
      · positivity;
      · intro n; rw [ ← hd_pow n ] ; rw [ ← Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.mul_rpow ( by positivity ) ( by positivity ) ] ;
        exact ⟨ by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> nlinarith [ hr n, pow_pos ( zero_lt_one.trans hσ ) n ], by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> nlinarith [ hr n, pow_pos ( zero_lt_one.trans hσ ) n ] ⟩;
  obtain ⟨ m₁, m₂, hm₁, hm₂, h ⟩ := h_rpow_bounds; use c₁ / m₂, c₂ / m₁; simp_all +decide [ ne_of_gt, division_def ] ;
  intro n; constructor <;> nlinarith [ hQ n, h n, show 0 < c₁ * m₂⁻¹ by positivity, show 0 < c₂ * m₁⁻¹ by positivity, mul_inv_cancel_left₀ hm₂.ne' ( r n ^ ( Real.log a * ( Real.log σ ) ⁻¹ ) ), mul_inv_cancel_left₀ hm₁.ne' ( r n ^ ( Real.log a * ( Real.log σ ) ⁻¹ ) ) ] ;

/-! ### Graph metric balls and their degree-volume -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The **graph metric ball** `B(o,r) = { x : d(o,x) ≤ r }`. -/
noncomputable def graphBall (G : SimpleGraph V) [DecidableRel G.Adj] (o : V) (r : ℕ) : Finset V :=
  Finset.univ.filter (fun x => G.dist o x ≤ r)

/-- The **volume of a ball** `V(B(o,r)) = ∑_{x ∈ B(o,r)} deg(x)`. -/
noncomputable def ballVolume (G : SimpleGraph V) [DecidableRel G.Adj] (o : V) (r : ℕ) : ℝ :=
  volume G (graphBall G o r)

omit [DecidableEq V] in
/-- The volume of a ball is `volume` of the underlying finset. -/
lemma ballVolume_eq (G : SimpleGraph V) [DecidableRel G.Adj] (o : V) (r : ℕ) :
    ballVolume G o r = volume G (graphBall G o r) := rfl

/-
Balls are monotone in the radius.
-/
lemma graphBall_mono (G : SimpleGraph V) [DecidableRel G.Adj] (o : V) {r r' : ℕ}
    (h : r ≤ r') : graphBall G o r ⊆ graphBall G o r' := by
  exact fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hx |>.1, le_trans ( Finset.mem_filter.mp hx |>.2 ) h ⟩

/-
The center lies in every ball.
-/
lemma self_mem_graphBall (G : SimpleGraph V) [DecidableRel G.Adj] (o : V) (r : ℕ) :
    o ∈ graphBall G o r := by
  exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by simp +decide ⟩

/-! ### The local power laws `V(B) ≍ r^{d_f}` and `R ≍ r^ζ` -/

/-- **Local volume power law (Lemma 2.14, radius form).**  From the geometric
ball-volume growth `Vol n ≍ ρN^n` and the distance scaling `Rad n ≍ ρmin^n`, the
ball volume obeys `V ≍ r^{d_f}` with `d_f = log ρN / log ρmin`. -/
theorem ballVolume_power_law {Vol Rad : ℕ → ℝ} {ρN ρmin : ℝ}
    (hρN : 1 < ρN) (hρmin : 1 < ρmin)
    (hVol : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ n, c₁ * ρN ^ n ≤ Vol n ∧ Vol n ≤ c₂ * ρN ^ n)
    (hRad : ∃ c₃ c₄ : ℝ, 0 < c₃ ∧ 0 < c₄ ∧ ∀ n, c₃ * ρmin ^ n ≤ Rad n ∧ Rad n ≤ c₄ * ρmin ^ n) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ n, C₁ * (Rad n) ^ (Real.log ρN / Real.log ρmin) ≤ Vol n
        ∧ Vol n ≤ C₂ * (Rad n) ^ (Real.log ρN / Real.log ρmin) :=
  geometric_radius_power (zero_lt_one.trans hρN) hρmin hVol hRad

/-- **Local resistance power law (Lemma 2.17, radius form).**  From the geometric
resistance growth `Res n ≍ ρΨ^n` and the distance scaling `Rad n ≍ ρmin^n`, the
effective resistance obeys `R ≍ r^ζ` with `ζ = log ρΨ / log ρmin`. -/
theorem ballResistance_power_law {Res Rad : ℕ → ℝ} {ρΨ ρmin : ℝ}
    (hρΨ : 0 < ρΨ) (hρmin : 1 < ρmin)
    (hRes : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ n, c₁ * ρΨ ^ n ≤ Res n ∧ Res n ≤ c₂ * ρΨ ^ n)
    (hRad : ∃ c₃ c₄ : ℝ, 0 < c₃ ∧ 0 < c₄ ∧ ∀ n, c₃ * ρmin ^ n ≤ Rad n ∧ Rad n ≤ c₄ * ρmin ^ n) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ n, C₁ * (Rad n) ^ (Real.log ρΨ / Real.log ρmin) ≤ Res n
        ∧ Res n ≤ C₂ * (Rad n) ^ (Real.log ρΨ / Real.log ρmin) :=
  geometric_radius_power hρΨ hρmin hRes hRad

/-
**Exit time radius power law (walk dimension, radius form).**  If the exit
time factorises as `Exit n ≍ Vol n · Res n` and `Vol ≍ r^{d_f}`, `Res ≍ r^ζ`,
then `Exit ≍ r^{d_f + ζ} = r^{d_w}`, the walk-dimension power law.  (Here the
radii are positive.)
-/
theorem exit_time_radius_power {Exit Vol Res Rad : ℕ → ℝ} {df ζ : ℝ}
    (hrad : ∀ n, 0 < Rad n)
    (hfac : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ n, a * (Vol n * Res n) ≤ Exit n ∧ Exit n ≤ b * (Vol n * Res n))
    (hVol : ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ n, C₁ * (Rad n) ^ df ≤ Vol n ∧ Vol n ≤ C₂ * (Rad n) ^ df)
    (hRes : ∃ D₁ D₂ : ℝ, 0 < D₁ ∧ 0 < D₂ ∧ ∀ n, D₁ * (Rad n) ^ ζ ≤ Res n ∧ Res n ≤ D₂ * (Rad n) ^ ζ) :
    ∃ E₁ E₂ : ℝ, 0 < E₁ ∧ 0 < E₂ ∧
      ∀ n, E₁ * (Rad n) ^ (df + ζ) ≤ Exit n ∧ Exit n ≤ E₂ * (Rad n) ^ (df + ζ) := by
  -- By definition of big-O notation, we can extract such constants $C₁, C₂, D₁, D₂$ from the hypotheses $hVol$ and $hRes$.
  obtain ⟨C₁, C₂, hC₁_pos, hC₂_pos, hVol_bounds⟩ := hVol
  obtain ⟨D₁, D₂, hD₁_pos, hD₂_pos, hRes_bounds⟩ := hRes
  obtain ⟨a, b, ha_pos, hb_pos, hExit_bounds⟩ := hfac
  use a * C₁ * D₁, b * C₂ * D₂;
  refine' ⟨ by positivity, by positivity, fun n => ⟨ _, _ ⟩ ⟩;
  · refine' le_trans _ ( hExit_bounds n |>.1 );
    convert mul_le_mul_of_nonneg_left ( mul_le_mul ( hVol_bounds n |>.1 ) ( hRes_bounds n |>.1 ) ?_ ?_ ) ha_pos.le using 1 <;> ring;
    · rw [ Real.rpow_add ( hrad n ) ] ; ring;
    · exact mul_nonneg hD₁_pos.le ( Real.rpow_nonneg ( le_of_lt ( hrad n ) ) _ );
    · exact le_trans ( mul_nonneg hC₁_pos.le ( Real.rpow_nonneg ( le_of_lt ( hrad n ) ) _ ) ) ( hVol_bounds n |>.1 );
  · convert hExit_bounds n |>.2.trans ( mul_le_mul_of_nonneg_left ( mul_le_mul ( hVol_bounds n |>.2 ) ( hRes_bounds n |>.2 ) ?_ ?_ ) hb_pos.le ) using 1 <;> ring;
    · rw [ Real.rpow_add ( hrad n ) ] ; ring;
    · exact le_trans ( mul_nonneg hD₁_pos.le ( Real.rpow_nonneg ( le_of_lt ( hrad n ) ) _ ) ) ( hRes_bounds n |>.1 );
    · exact mul_nonneg hC₂_pos.le ( Real.rpow_nonneg ( le_of_lt ( hrad n ) ) _ )

/-! ### Deriving local volume regularity from volume doubling -/

/-
**Local volume regularity from volume doubling.**  If the ball volume obeys
the doubling bound `V(B(o,2r)) ≤ D · V(B(o,r))` (with `D > 0`), then the smaller
ball carries a definite fraction of the larger ball's volume:
`D⁻¹ · V(B(o,2r)) ≤ ∑_{y ∈ B(o,r)} deg(y)`.  This supplies the `hvol` input of
the conditional exit-time lower bound with `c' = D⁻¹`, `S = B(o,2r)`,
`T = B(o,r)`.
-/
omit [DecidableEq V] in
theorem volume_doubling_regularity (G : SimpleGraph V) [DecidableRel G.Adj]
    {o : V} {r : ℕ} {D : ℝ} (hD : 0 < D)
    (hdbl : volume G (graphBall G o (2 * r)) ≤ D * volume G (graphBall G o r)) :
    D⁻¹ * volume G (graphBall G o (2 * r))
      ≤ ∑ y ∈ graphBall G o r, (G.degree y : ℝ) := by
  rw [ inv_mul_le_iff₀ ] <;> linarith!

/-! ### Assembled local two-sided exit estimate on a ball -/

/-
**Local two-sided exit estimate `E[τ] ≍ V·R` on a graph ball.**  Working on
the ball `S = B(o,2r)` with center `o`, the clean upper bound `τ(o) ≤ R·V(S)` is
unconditional; the matching lower bound is obtained by combining
* the **near-diagonal Green lower bound** `hnd` on the inner ball `T = B(o,r)`
  (the elliptic-Harnack input, cited), and
* **volume doubling** `hdbl`, from which local volume regularity is *proved*
  (`volume_doubling_regularity`, giving `c' = D⁻¹`).
Hence `c·D⁻¹·R·V(S) ≤ τ(o) ≤ R·V(S)`.
-/
theorem exit_two_sided_local (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) {o : V} {r : ℕ}
    (hSc : (graphBall G o (2 * r))ᶜ.Nonempty)
    {τ : V → ℝ} (hτ : ExitSystem G (graphBall G o (2 * r)) τ)
    {c D : ℝ} (hc : 0 < c) (hD : 0 < D)
    (hnd : ∀ y : V, ∀ hy : y ∈ graphBall G o r,
      c * greenFn G (graphBall G o (2 * r))
            ⟨o, self_mem_graphBall G o (2 * r)⟩ ⟨o, self_mem_graphBall G o (2 * r)⟩
        ≤ greenFn G (graphBall G o (2 * r))
            ⟨o, self_mem_graphBall G o (2 * r)⟩
            ⟨y, graphBall_mono G o (by omega) hy⟩)
    (hdbl : volume G (graphBall G o (2 * r)) ≤ D * volume G (graphBall G o r)) :
    c * D⁻¹ * effResToBoundary G (graphBall G o (2 * r)) o * volume G (graphBall G o (2 * r)) ≤ τ o
      ∧ τ o ≤ effResToBoundary G (graphBall G o (2 * r)) o * volume G (graphBall G o (2 * r)) := by
  apply EIGS.exit_two_sided;
  all_goals try assumption;
  convert volume_doubling_regularity G hD hdbl using 1

end EIGS