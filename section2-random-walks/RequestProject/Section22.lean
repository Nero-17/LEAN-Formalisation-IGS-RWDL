import Mathlib
import RequestProject.Section2
import RequestProject.Section2Network
import RequestProject.Section21

/-!
# Formalisation of Section 2.2 of arXiv:2603.13798
  *Iterated Graph Systems (I): random walks and diffusion limits*

Section 2.2 ("Walk dimension") determines, for the combinatorial limit `Ξ` of a
(canonical) EIGS, the local mass dimension, the local resistance dimension, the
walk dimension, and proves the **Einstein relation**
`dim_W(Ξ) = dim_B(Ξ) + dim_R(Ξ)`, together with the recurrence criterion and the
universal lower bound `dim_W(Ξ) ≥ 2`.

The mathematical backbone of every dimension statement in Section 2.2 is a
two-sided *geometric* growth estimate
`c · base^(index) ≤ Quantity ≤ C · base^(index)`
for the relevant graph quantity (ball volume, effective resistance from a vertex
to the complement of a ball, exit time, ...), where the index is a level
parameter going to infinity, combined with the distance scaling
`c · ρ_min^(level) ≤ diam ≤ C · ρ_min^(level)`.

These two-sided geometric estimates are precisely the deep combinatorial inputs
of the paper:
* **Lemma 2.13** ([36, 38]): vertex/edge counts `~ ρ(M)^m`, diameters
  `~ ρ_min(𝒟)^m`, degrees `~ ρ(N)^{n-k}`;
* **Lemma 2.14** (local mass): `|V(B(v,r))| ~ ρ(N)^{n-k-m} ρ(M)^m`;
* **Lemma 2.17** (local resistance): `ℛ(v, B(v,r)^c) ~ ρ(Ψ)^m / ρ(N)^{n-k-m}`;
* **Lemma 2.22 / Theorem 2.23** (exit time): `E^v[τ] ~ ρ(M)^m ρ(Ψ)^m`;
* the **commute-time identity** `T = 2|E| ℛ` and the
  Nash-Williams/Cauchy-Schwarz `|E| ℛ ≥ d²`.

Exactly as in `Section21.lean`, those geometric inputs are taken as hypotheses
(they belong to the Section 1 substitution framework), and what is *proved* here
is the analytic / algebraic content of Section 2.2: that these geometric
estimates yield the claimed dimension values, the Einstein relation, the
recurrence dichotomy, the lower bound `dim_W ≥ 2`, and the explicit `(u,v)`-flower
example.

The numerator `resistanceDimension R D := lim_n log(R n)/log(D n)` is reused from
`Section21.lean`; every dimension in Section 2.2 is an instance of this limit.
-/

namespace EIGS

open scoped BigOperators
open Filter Topology

/-! ### General analytic core

The scaling-dimension limit.  If a quantity `R n` is squeezed between
`c₁ a^{m n}` and `c₂ a^{m n}` (with `a > 0`) and the scale `D n` between
`c₃ σ^{m n}` and `c₄ σ^{m n}` (with `σ > 1`), and the level `m n → ∞`, then
`log(R n)/log(D n) → log a / log σ`.

This generalises `resistance_dimension_limit` of `Section21.lean` in two ways:
the numerator base `a` is allowed to be any positive real (not necessarily `> 1`,
needed for the *decaying* local resistance of Proposition 2.19), and the level is
reindexed by an arbitrary sequence `m n → ∞` (needed for the walk dimension,
Theorem 2.23/Definition 2.25, where the level `m_n` is not `n` itself). -/

theorem scaling_ratio_tendsto
    {R D : ℕ → ℝ} {a σ : ℝ} {m : ℕ → ℕ}
    (ha : 0 < a) (hσ : 1 < σ) (hm : Tendsto m atTop atTop)
    (hR : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ n, c₁ * a ^ (m n) ≤ R n ∧ R n ≤ c₂ * a ^ (m n))
    (hD : ∃ c₃ c₄ : ℝ, 0 < c₃ ∧ 0 < c₄ ∧ ∀ n, c₃ * σ ^ (m n) ≤ D n ∧ D n ≤ c₄ * σ ^ (m n)) :
    Tendsto (fun n => Real.log (R n) / Real.log (D n)) atTop
      (nhds (Real.log a / Real.log σ)) := by
  -- By dividing both the numerator and the denominator by $m_n$, we get:
  have h_div : Filter.Tendsto (fun n => Real.log (R n) / (m n : ℝ)) Filter.atTop (nhds (Real.log a)) ∧ Filter.Tendsto (fun n => Real.log (D n) / (m n : ℝ)) Filter.atTop (nhds (Real.log σ)) := by
    constructor <;> rw [ Metric.tendsto_nhds ] <;> norm_num;
    · intro ε hε;
      -- Using the bounds from `hR`, we can derive the inequality for `Real.log (R n) / (m n : ℝ)`.
      obtain ⟨c₁, c₂, hc₁, hc₂, hR_bounds⟩ := hR;
      have h_log_bounds : ∀ n, m n > 0 → Real.log c₁ / (m n : ℝ) + Real.log a ≤ Real.log (R n) / (m n : ℝ) ∧ Real.log (R n) / (m n : ℝ) ≤ Real.log c₂ / (m n : ℝ) + Real.log a := by
        intro n hn_pos
        have h_log_bounds : Real.log c₁ + m n * Real.log a ≤ Real.log (R n) ∧ Real.log (R n) ≤ Real.log c₂ + m n * Real.log a := by
          exact ⟨ by simpa [ Real.log_mul, ha.ne', hc₁.ne' ] using Real.log_le_log ( by positivity ) ( hR_bounds n |>.1 ), by simpa [ Real.log_mul, ha.ne', hc₂.ne' ] using Real.log_le_log ( by exact lt_of_lt_of_le ( by positivity ) ( hR_bounds n |>.1 ) ) ( hR_bounds n |>.2 ) ⟩;
        exact ⟨ by rw [ div_add', div_le_div_iff_of_pos_right ] <;> first | positivity | linarith, by rw [ div_add', div_le_div_iff_of_pos_right ] <;> first | positivity | linarith ⟩;
      -- Since $m_n \to \infty$, we have $\frac{\log c₁}{m_n} \to 0$ and $\frac{\log c₂}{m_n} \to 0$.
      have h_log_c1_c2_zero : Filter.Tendsto (fun n => Real.log c₁ / (m n : ℝ)) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun n => Real.log c₂ / (m n : ℝ)) Filter.atTop (nhds 0) := by
        exact ⟨ tendsto_const_nhds.div_atTop <| tendsto_natCast_atTop_atTop.comp hm, tendsto_const_nhds.div_atTop <| tendsto_natCast_atTop_atTop.comp hm ⟩;
      rcases Metric.tendsto_atTop.mp h_log_c1_c2_zero.1 ( ε / 2 ) ( half_pos hε ) with ⟨ N₁, hN₁ ⟩ ; rcases Metric.tendsto_atTop.mp h_log_c1_c2_zero.2 ( ε / 2 ) ( half_pos hε ) with ⟨ N₂, hN₂ ⟩ ; rcases Filter.eventually_atTop.mp ( hm.eventually_gt_atTop 0 ) with ⟨ N₃, hN₃ ⟩ ; exact ⟨ Max.max N₁ ( Max.max N₂ N₃ ), fun n hn => abs_lt.mpr ⟨ by linarith [ abs_lt.mp ( hN₁ n ( le_trans ( le_max_left _ _ ) hn ) ), abs_lt.mp ( hN₂ n ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hn ) ), h_log_bounds n ( hN₃ n ( le_trans ( le_max_of_le_right ( le_max_right _ _ ) ) hn ) ) ], by linarith [ abs_lt.mp ( hN₁ n ( le_trans ( le_max_left _ _ ) hn ) ), abs_lt.mp ( hN₂ n ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hn ) ), h_log_bounds n ( hN₃ n ( le_trans ( le_max_of_le_right ( le_max_right _ _ ) ) hn ) ) ] ⟩ ⟩ ;
    · intro ε hε;
      -- Using the bounds on $D_n$, we can derive the inequality for $\frac{\log(D_n)}{m_n}$.
      obtain ⟨c₃, c₄, hc₃, hc₄, hD_bounds⟩ := hD;
      have h_log_bounds : ∀ n, Real.log c₃ + m n * Real.log σ ≤ Real.log (D n) ∧ Real.log (D n) ≤ Real.log c₄ + m n * Real.log σ := by
        exact fun n => ⟨ by simpa [ Real.log_mul, hc₃.ne', show σ ≠ 0 by positivity ] using Real.log_le_log ( by positivity ) ( hD_bounds n |>.1 ), by simpa [ Real.log_mul, hc₄.ne', show σ ≠ 0 by positivity ] using Real.log_le_log ( by exact lt_of_lt_of_le ( by positivity ) ( hD_bounds n |>.1 ) ) ( hD_bounds n |>.2 ) ⟩;
      -- Using the bounds on $D_n$, we can derive the inequality for $\frac{\log(D_n)}{m_n}$ and show that it converges to $\log(\sigma)$.
      have h_log_div_bounds : ∀ n, m n > 0 → |Real.log (D n) / (m n : ℝ) - Real.log σ| ≤ (|Real.log c₃| + |Real.log c₄|) / (m n : ℝ) := by
        intro n hn; rw [ abs_le ] ; constructor <;> cases abs_cases ( Real.log c₃ ) <;> cases abs_cases ( Real.log c₄ ) <;> nlinarith [ h_log_bounds n, show ( m n : ℝ ) > 0 by positivity, mul_div_cancel₀ ( Real.log ( D n ) ) ( by positivity : ( m n : ℝ ) ≠ 0 ), mul_div_cancel₀ ( |Real.log c₃| + |Real.log c₄| ) ( by positivity : ( m n : ℝ ) ≠ 0 ) ] ;
      rcases Filter.eventually_atTop.mp ( hm.eventually_gt_atTop ⌈ ( |Real.log c₃| + |Real.log c₄| ) / ε⌉₊ ) with ⟨ N, hN ⟩ ; use N ; intros n hn ; specialize h_log_div_bounds n ( pos_of_gt ( hN n hn ) ) ; refine' lt_of_le_of_lt h_log_div_bounds _ ; rw [ div_lt_iff₀ ] <;> nlinarith [ Nat.le_ceil ( ( |Real.log c₃| + |Real.log c₄| ) / ε ), mul_div_cancel₀ ( |Real.log c₃| + |Real.log c₄| ) hε.ne', show ( m n : ℝ ) ≥ ⌈ ( |Real.log c₃| + |Real.log c₄| ) / ε⌉₊ + 1 by exact_mod_cast hN n hn ] ;
  have := h_div.1.div h_div.2;
  exact this ( ne_of_gt ( Real.log_pos hσ ) ) |> fun h => h.congr' ( by filter_upwards [ hm.eventually_gt_atTop 0 ] with n hn; simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hn.ne' ] )

/-- The scaling dimension equals `log a / log σ` under the same hypotheses. -/
theorem scalingDimension_eq
    {R D : ℕ → ℝ} {a σ : ℝ} {m : ℕ → ℕ}
    (ha : 0 < a) (hσ : 1 < σ) (hm : Tendsto m atTop atTop)
    (hR : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ n, c₁ * a ^ (m n) ≤ R n ∧ R n ≤ c₂ * a ^ (m n))
    (hD : ∃ c₃ c₄ : ℝ, 0 < c₃ ∧ 0 < c₄ ∧ ∀ n, c₃ * σ ^ (m n) ≤ D n ∧ D n ≤ c₄ * σ ^ (m n)) :
    resistanceDimension R D = Real.log a / Real.log σ :=
  (scaling_ratio_tendsto ha hσ hm hR hD).limUnder_eq

/-
If `B · s^n ≤ A · t^n` for all `n`, with all constants and bases positive,
then `s ≤ t`.  (Geometric domination forces base ordering; the analytic core of
Proposition 2.27.)
-/
theorem base_le_of_geometric_dom
    {A B s t : ℝ} (hB : 0 < B) (ht : 0 < t)
    (h : ∀ n : ℕ, B * s ^ n ≤ A * t ^ n) : s ≤ t := by
  contrapose! h;
  -- Since $s > t$, we can choose $n$ such that $(s/t)^n > A/B$.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (s / t) ^ n > A / B := by
    exact pow_unbounded_of_one_lt _ ( by rw [ lt_div_iff₀ ht ] ; linarith );
  exact ⟨ n, by rw [ div_pow, gt_iff_lt, div_lt_div_iff₀ ] at hn <;> first | positivity | linarith ⟩

/-! ### Local mass dimension (Lemma 2.14, Definition 2.15, Proposition 2.16)

`|V(B(v,r_*))| ~ ρ(N)^{n-k}` (Lemma 2.14 with `r_*` fixed, i.e. `m` fixed) and
`diam(Ξⁿ)/r_* ~ ρ_min(𝒟)^n` (Lemma 2.13).  Hence the local mass dimension equals
`log ρ(N) / log ρ_min(𝒟)`.  (Note `ρ(N) > 1` is the locally-infinite/scale-free
hypothesis of Proposition 2.16.) -/

/-- **Proposition 2.16 (local mass dimension).** -/
theorem local_mass_dimension_eq
    {Vol Diam : ℕ → ℝ} {ρN ρmin : ℝ}
    (hρN : 1 < ρN) (hρmin : 1 < ρmin)
    (hVol : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ n, c₁ * ρN ^ n ≤ Vol n ∧ Vol n ≤ c₂ * ρN ^ n)
    (hDiam : ∃ c₃ c₄ : ℝ, 0 < c₃ ∧ 0 < c₄ ∧ ∀ n, c₃ * ρmin ^ n ≤ Diam n ∧ Diam n ≤ c₄ * ρmin ^ n) :
    resistanceDimension Vol Diam = Real.log ρN / Real.log ρmin :=
  scalingDimension_eq (m := id) (zero_lt_one.trans hρN) hρmin tendsto_id hVol hDiam

/-! ### Local resistance dimension (Lemma 2.17, Definition 2.18, Proposition 2.19)

`ℛ(v, B(v,r_*)^c) ~ ρ(N)^{-(n-k)} = (ρ(N)⁻¹)^{n-k}` (Proposition 2.19) and
`diam(Ξⁿ)/r_* ~ ρ_min(𝒟)^n`.  The local resistance dimension is therefore
`log(ρ(N)⁻¹)/log ρ_min(𝒟) = - log ρ(N) / log ρ_min(𝒟)`, which is *negative* —
the scale-free paradox highlighted in the paper. -/

/-- **Proposition 2.19 (local resistance dimension).** -/
theorem local_resistance_dimension_eq
    {Res Diam : ℕ → ℝ} {ρN ρmin : ℝ}
    (hρN : 1 < ρN) (hρmin : 1 < ρmin)
    (hRes : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ n, c₁ * (ρN⁻¹) ^ n ≤ Res n ∧ Res n ≤ c₂ * (ρN⁻¹) ^ n)
    (hDiam : ∃ c₃ c₄ : ℝ, 0 < c₃ ∧ 0 < c₄ ∧ ∀ n, c₃ * ρmin ^ n ≤ Diam n ∧ Diam n ≤ c₄ * ρmin ^ n) :
    resistanceDimension Res Diam = - Real.log ρN / Real.log ρmin := by
  have h := scalingDimension_eq (m := id) (inv_pos.mpr (zero_lt_one.trans hρN)) hρmin
    tendsto_id hRes hDiam
  rwa [Real.log_inv] at h

/-! ### Walk dimension and the Einstein relation
(Lemma 2.22, Theorem 2.23, Definition 2.25, Theorem 2.26)

The exit time satisfies `E^v[τ] ~ (ρ(M)·ρ(Ψ))^{m_n}` (Theorem 2.23) while the
radius satisfies `r_n ~ ρ_min(𝒟)^{m_n}` (Definition 2.25 admissibility); here the
crucial cancellation of the local `ρ(N)^m` factors makes the level uniform.
Hence the walk dimension is `log(ρ(M)ρ(Ψ))/log ρ_min(𝒟)`, and the **Einstein
relation** is the additive split of this logarithm:
`dim_W = log ρ(M)/log ρ_min + log ρ(Ψ)/log ρ_min = dim_B + dim_R`. -/

/-- **Theorem 2.23 / Definition 2.25 (walk dimension value).** -/
theorem walk_dimension_eq
    {Exit Rad : ℕ → ℝ} {ρM ρPsi ρmin : ℝ} {m : ℕ → ℕ}
    (hρM : 0 < ρM) (hρPsi : 0 < ρPsi) (hρmin : 1 < ρmin) (hm : Tendsto m atTop atTop)
    (hExit : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ n, c₁ * (ρM * ρPsi) ^ (m n) ≤ Exit n ∧ Exit n ≤ c₂ * (ρM * ρPsi) ^ (m n))
    (hRad : ∃ c₃ c₄ : ℝ, 0 < c₃ ∧ 0 < c₄ ∧
      ∀ n, c₃ * ρmin ^ (m n) ≤ Rad n ∧ Rad n ≤ c₄ * ρmin ^ (m n)) :
    resistanceDimension Exit Rad = Real.log (ρM * ρPsi) / Real.log ρmin :=
  scalingDimension_eq (mul_pos hρM hρPsi) hρmin hm hExit hRad

/-- **Theorem 2.26 (Einstein relation), algebraic form.**  The walk dimension
`log(ρ(M)ρ(Ψ))/log ρ_min` splits as the sum of the Minkowski (box) dimension
`log ρ(M)/log ρ_min` and the resistance dimension `log ρ(Ψ)/log ρ_min`. -/
theorem einstein_relation {ρM ρPsi ρmin : ℝ} (hρM : 0 < ρM) (hρPsi : 0 < ρPsi) :
    Real.log (ρM * ρPsi) / Real.log ρmin
      = Real.log ρM / Real.log ρmin + Real.log ρPsi / Real.log ρmin := by
  rw [Real.log_mul (ne_of_gt hρM) (ne_of_gt hρPsi), add_div]

/-- **Theorem 2.26 (Einstein relation), combined form.**  The walk dimension of
`Ξ` (as the scaling limit of exit-time vs. radius) equals `dim_B + dim_R`. -/
theorem walk_dimension_einstein
    {Exit Rad : ℕ → ℝ} {ρM ρPsi ρmin : ℝ} {m : ℕ → ℕ}
    (hρM : 0 < ρM) (hρPsi : 0 < ρPsi) (hρmin : 1 < ρmin) (hm : Tendsto m atTop atTop)
    (hExit : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ n, c₁ * (ρM * ρPsi) ^ (m n) ≤ Exit n ∧ Exit n ≤ c₂ * (ρM * ρPsi) ^ (m n))
    (hRad : ∃ c₃ c₄ : ℝ, 0 < c₃ ∧ 0 < c₄ ∧
      ∀ n, c₃ * ρmin ^ (m n) ≤ Rad n ∧ Rad n ≤ c₄ * ρmin ^ (m n)) :
    resistanceDimension Exit Rad
      = Real.log ρM / Real.log ρmin + Real.log ρPsi / Real.log ρmin := by
  rw [walk_dimension_eq hρM hρPsi hρmin hm hExit hRad, einstein_relation hρM hρPsi]

/-! ### Commute time (Proposition 2.24)

The commute-time identity `T = 2|E| ℛ(𝔳₊,𝔳₋)` combined with `|E| ~ ρ(M)^n`
(Lemma 2.13) and `ℛ(𝔳₊,𝔳₋) ~ ρ(Ψ)^n` (Lemma 2.9) gives `T ~ (ρ(M)ρ(Ψ))^n`. -/

/-
**Proposition 2.24 (commute time).**
-/
theorem commute_time_bounds
    {Edges Res : ℕ → ℝ} {ρM ρPsi cE CE cΨ CΨ : ℝ}
    (hcE : 0 < cE) (hcΨ : 0 < cΨ) (hρM : 0 < ρM) (hρPsi : 0 < ρPsi)
    (hE : ∀ n, cE * ρM ^ n ≤ Edges n ∧ Edges n ≤ CE * ρM ^ n)
    (hR : ∀ n, cΨ * ρPsi ^ n ≤ Res n ∧ Res n ≤ CΨ * ρPsi ^ n) :
    ∀ n, 2 * cE * cΨ * (ρM * ρPsi) ^ n ≤ 2 * Edges n * Res n
        ∧ 2 * Edges n * Res n ≤ 2 * CE * CΨ * (ρM * ρPsi) ^ n := by
  intro n;
  constructor <;> ring_nf at *;
  · nlinarith [ hE n, hR n, show 0 < cE * ρM ^ n by positivity, show 0 < cΨ * ρPsi ^ n by positivity ];
  · nlinarith [ hE n, hR n, show 0 ≤ ρM ^ n * cE by positivity, show 0 ≤ ρPsi ^ n * cΨ by positivity ]

/-! ### Proposition 2.27 and Proposition 2.28 (the inequality `dim_W ≥ 2`)

From `|E| ℛ ≥ d²` with `|E| ~ ρ(M)^n`, `ℛ ~ ρ(Ψ)^n`, `d ~ ρ_min^n` one gets
`ρ(M)ρ(Ψ) ≥ ρ_min²`, whence `dim_W = log(ρ(M)ρ(Ψ))/log ρ_min ≥ 2`. -/

/-- **Proposition 2.27.**  `ρ_min(𝒟)² ≤ ρ(M)·ρ(Ψ)`, deduced from the geometric
domination `c_d² (ρ_min²)^n ≤ A (ρ(M)ρ(Ψ))^n` coming from `|E| ℛ ≥ d²`. -/
theorem rhomin_sq_le_prod
    {ρM ρPsi ρmin A cd : ℝ} (hcd : 0 < cd) (hprod : 0 < ρM * ρPsi)
    (h : ∀ n : ℕ, cd ^ 2 * (ρmin ^ 2) ^ n ≤ A * (ρM * ρPsi) ^ n) :
    ρmin ^ 2 ≤ ρM * ρPsi :=
  base_le_of_geometric_dom (by positivity) hprod h

/-
**Proposition 2.28.**  `dim_W(Ξ) ≥ 2`.
-/
theorem walk_dimension_ge_two
    {ρM ρPsi ρmin : ℝ} (hρmin : 1 < ρmin)
    (hge : ρmin ^ 2 ≤ ρM * ρPsi) :
    2 ≤ Real.log (ρM * ρPsi) / Real.log ρmin := by
  rw [ le_div_iff₀ ( Real.log_pos hρmin ) ] ; simpa using Real.log_le_log ( by positivity ) hge

/-! ### Recurrence (Definition 2.20, Proposition 2.21)

`Ξ` is recurrent iff the effective resistance to infinity is `∞`.  With the
geometric estimate `ℛ_n ~ ρ(Ψ)^n` (from Corollary 2.7), the resistance to
infinity diverges iff `ρ(Ψ) > 1`. -/

/-
**Proposition 2.21 (recurrence criterion).**  Given a two-sided geometric
description `c·ρ(Ψ)^n ≤ ℛ_n ≤ C·ρ(Ψ)^n` of the resistance to the ball
complement, the resistance to infinity diverges (i.e. `Ξ` is recurrent) iff
`ρ(Ψ) > 1`.
-/
theorem recurrence_iff
    {Res : ℕ → ℝ} {ρPsi c C : ℝ} (hc : 0 < c) (hC : 0 < C) (hρPsi : 0 < ρPsi)
    (hRes : ∀ n, c * ρPsi ^ n ≤ Res n ∧ Res n ≤ C * ρPsi ^ n) :
    Tendsto Res atTop atTop ↔ 1 < ρPsi := by
  constructor <;> intro h;
  · contrapose! h;
    exact fun H => absurd ( H.eventually_gt_atTop ( C ) ) fun H' => by obtain ⟨ n, hn ⟩ := H'.exists; nlinarith [ hRes n, pow_le_pow_of_le_one hρPsi.le h ( show n ≥ 0 by norm_num ) ] ;
  · exact Filter.tendsto_atTop_mono ( fun n => hRes n |>.1 ) ( tendsto_pow_atTop_atTop_of_one_lt h |> Filter.Tendsto.const_mul_atTop hc )

/-! ### Example 2.29 (the `(u,v)`-flower)

For the single-coloured `(u,v)`-flower EIGS, one replacement block is `u` parallel
chains of `v` unit edges, so `Ψ(x) = (v/u) x`, and
`ρ(M) = uv`, `ρ_min(𝒟) = v`, `ρ(Ψ) = v/u`.  Hence
`dim_B = 1 + log u/log v`, `dim_R = 1 - log u/log v`, and `dim_W = 2`
(exactly diffusive). -/

/-- The renormalisation map of the `(u,v)`-flower is the scalar `x ↦ (v/u) x`. -/
noncomputable def flowerPsi (u v : ℕ) (x : ℝ) : ℝ := (v / u) * x

/-
**Example 2.29 (flower dimensions).**  For the `(u,v)`-flower with `u, v ≥ 2`:
the Minkowski (box) dimension is `1 + log u/log v`, the resistance dimension is
`1 - log u/log v`, and the walk dimension is exactly `2`.
-/
theorem flower_dims (u v : ℕ) (hu : 2 ≤ u) (hv : 2 ≤ v) :
    Real.log ((u : ℝ) * v) / Real.log v = 1 + Real.log u / Real.log v
  ∧ Real.log ((v : ℝ) / u) / Real.log v = 1 - Real.log u / Real.log v
  ∧ Real.log (((u : ℝ) * v) * ((v : ℝ) / u)) / Real.log v = 2 := by
  field_simp;
  rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_div ( by positivity ) ( by positivity ), Real.log_pow ] ; ring_nf ; norm_num [ ne_of_gt, Real.log_pos, show u > 1 by linarith, show v > 1 by linarith ] ;
  constructor <;> ring

end EIGS