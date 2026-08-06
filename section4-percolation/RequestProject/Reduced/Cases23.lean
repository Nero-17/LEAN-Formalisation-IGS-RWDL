import RequestProject.Reduced.Moments

/-!
# Lemma 4.5 of the paper, Cases 2 and 3 (the uniform product–moment bound for all `p`)

`RequestProject.Reduced.Moments` proves the uniform product–moment bound
`E[R n]·E[1/R n] ≤ 11/5` of paper Lemma 4.5 in **Case 1** (`pdiamond ≤ 1/2`).

This file completes the remaining two regimes of Lemma 4.5:

* **Case 2** (`1/2 ≤ pdiamond ≤ 1/√3`, here written `1/2 ≤ pd` and `pd^2 ≤ 1/3`):
  the relative second moment now satisfies the looser bound `E[R²] ≤ 3·E[R]²`, and together with
  the one–step logistic estimate this still yields `E[R n]·E[1/R n] ≤ 11/5` for all `n`.
  The proof of `E[R²] ≤ 3·E[R]²` needs two extra Cauchy–Schwarz estimates over the four–fold
  product (`diamond_CS`, the refined diamond second–moment estimate, and `harm_CS`, the
  harmonic–mean estimate giving `E[D] ≥ (5/11)E[R]`).

* **Case 3** (`pdiamond > 1/√3`, here `1/2 < pd`, `pd < 1`, `1/3 < pd^2`):
  here one uses the almost–sure monotonicity `R_{n+1} ≥ R_n` of the resistance process —
  a graph–level (Rayleigh monotonicity) input which in this distributional model is taken as the
  hypothesis `hmono : ∀ k, E1 pd ps k ≤ E1 pd ps (k+1)` (the paper deduces it from the coupled
  graph construction).  With it the relative second moment stays bounded by
  `(2-pd)/(2pd-1)`, and the product moment satisfies an affine recursion with contraction factor
  `(3/2)(1-pd²) < 1`, giving a finite uniform bound.

Combining the three cases gives the uniform product–moment bound for **every** `p ∈ (0,1)`.
-/

namespace Reduced

open MeasureTheory Measure Real Set

noncomputable section

variable {pd ps : ℝ}

/-- Pure real–analytic closing inequality for Case 2, step 2.  Given the one–step second–moment
bound `E2s ≤ (8−7p)a² − (5/(3p))((2−p)a − r)²` and the lower bound `r ≥ ((22−17p)/11)·a` on the
new mean, the new relative second moment stays `≤ 3`, i.e. `E2s ≤ 3 r²`, when `1/2 ≤ p` and
`p² ≤ 1/3`. -/
lemma case2_close (p a r E2s : ℝ)
    (hpd1 : 1 / 2 ≤ p) (hpd2 : p ^ 2 ≤ 1 / 3) (ha : 1 ≤ a)
    (hr0 : (22 - 17 * p) / 11 * a ≤ r)
    (hbound : E2s ≤ (8 - 7 * p) * a ^ 2 - (5 / (3 * p)) * ((2 - p) * a - r) ^ 2) :
    E2s ≤ 3 * r ^ 2 := by
  have hpdpos : 0 < p := by linarith
  set r0 : ℝ := (22 - 17 * p) / 11 * a with hr0def
  have hrr0 : 0 ≤ r - r0 := by linarith
  have h1 : 0 ≤ 2601 * p ^ 2 - 4011 * p + 1452 := by
    nlinarith [hpd1, hpd2, sq_nonneg (p - 1 / 2), sq_nonneg (3 * p - 2)]
  have h2 : 0 ≤ 336 - 306 * p := by nlinarith [hpd2, hpd1]
  have hG : 0 ≤ 9 * p * r ^ 2 - 3 * p * (8 - 7 * p) * a ^ 2 + 5 * ((2 - p) * a - r) ^ 2 := by
    have hid : 9 * p * r ^ 2 - 3 * p * (8 - 7 * p) * a ^ 2 + 5 * ((2 - p) * a - r) ^ 2
        = a ^ 2 * p * (2601 * p ^ 2 - 4011 * p + 1452) / 121
          + (p * a * (336 - 306 * p) / 11) * (r - r0)
          + (9 * p + 5) * (r - r0) ^ 2 := by
      rw [hr0def]; ring
    rw [hid]
    have t1 : 0 ≤ a ^ 2 * p * (2601 * p ^ 2 - 4011 * p + 1452) / 121 := by positivity
    have t2 : 0 ≤ (p * a * (336 - 306 * p) / 11) * (r - r0) := by
      apply mul_nonneg _ hrr0; positivity
    have t3 : 0 ≤ (9 * p + 5) * (r - r0) ^ 2 := by positivity
    linarith
  have hdiff : 3 * r ^ 2 - ((8 - 7 * p) * a ^ 2 - (5 / (3 * p)) * ((2 - p) * a - r) ^ 2)
      = (9 * p * r ^ 2 - 3 * p * (8 - 7 * p) * a ^ 2 + 5 * ((2 - p) * a - r) ^ 2) / (3 * p) := by
    field_simp; ring
  have hkey : 0 ≤ 3 * r ^ 2 - ((8 - 7 * p) * a ^ 2 - (5 / (3 * p)) * ((2 - p) * a - r) ^ 2) := by
    rw [hdiff]; exact div_nonneg hG (by linarith)
  linarith [hbound, hkey]

/-- Pure real–analytic closing inequality for Case 3.  Converts the `logistic_step` output
(with relative second moment `c = (2−p)/(2p−1)`) into the affine recursion
`Q ≤ (3/2)(1−p²)P + (1+p)(2p−1)`. -/
lemma case3_affine_close (p P Q : ℝ)
    (hpd_lo : 1 / 2 < p) (hpd_hi : p < 1) (hP1 : 1 ≤ P)
    (hstep : Q * ((2 - p) / (2 * p - 1) * P - 1)
      ≤ ((2 - p) * (1 + p) / 2) * (((2 - p) / (2 * p - 1) - 1) * P ^ 2 + P - 1)) :
    Q ≤ (3 / 2) * (1 - p ^ 2) * P + (1 + p) * (2 * p - 1) := by
  have hD : 0 < 2 * p - 1 := by linarith
  have hDne : (2 * p - 1) ≠ 0 := ne_of_gt hD
  have hstepD0 := mul_le_mul_of_nonneg_right hstep hD.le
  have eL : ((2 - p) / (2 * p - 1) * P - 1) * (2 * p - 1) = (2 - p) * P - (2 * p - 1) := by
    field_simp
  have eR : (((2 - p) / (2 * p - 1) - 1) * P ^ 2 + P - 1) * (2 * p - 1)
      = 3 * (1 - p) * P ^ 2 + (P - 1) * (2 * p - 1) := by
    field_simp; ring
  rw [mul_assoc, eL, mul_assoc, eR] at hstepD0
  have helem : ((2 - p) * (1 + p) / 2) * (3 * (1 - p) * P ^ 2 + (P - 1) * (2 * p - 1))
      ≤ ((3 / 2) * (1 - p ^ 2) * P + (1 + p) * (2 * p - 1)) * ((2 - p) * P - (2 * p - 1)) := by
    have hfac : 0 ≤ 2 - p + (P - 2) * (2 * p - 1) := by nlinarith [hP1, hpd_lo, hpd_hi]
    have hKD : 0 ≤ (2 - p) * (1 + p) / 2 * (2 * p - 1) := by
      apply mul_nonneg; apply mul_nonneg <;> [nlinarith [hpd_hi]; nlinarith [hpd_lo]]; linarith
    nlinarith [mul_nonneg hKD hfac, hpd_lo, hpd_hi, hP1]
  have hQpos : 0 < (2 - p) * P - (2 * p - 1) := by nlinarith [hP1, hpd_lo, hpd_hi]
  have hfin : Q * ((2 - p) * P - (2 * p - 1))
      ≤ ((3 / 2) * (1 - p ^ 2) * P + (1 + p) * (2 * p - 1)) * ((2 - p) * P - (2 * p - 1)) :=
    le_trans hstepD0 helem
  exact le_of_mul_le_mul_right hfin hQpos

section Cases

variable (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1)

include hpd hps hsum

/-! ### A reusable one–step logistic estimate (paper Lemma 4.4, general relative second moment) -/

/-
**General one–step logistic estimate.** If the relative second moment at level `n` satisfies
`E[R²] ≤ c·E[R]²`, then (in cleared, division–free form)
`E[R_{n+1}]E[1/R_{n+1}]·(c·P − 1) ≤ K·((c−1)P² + P − 1)`,
where `P = E[R_n]E[1/R_n]` and `K = (2−pd)(1+pd)/2`.  This is the engine behind Cases 1–3.
-/
lemma logistic_step (c : ℝ) (n : ℕ) (hc2n : E2 pd ps n ≤ c * (E1 pd ps n) ^ 2) :
    E1 pd ps (n + 1) * Einv pd ps (n + 1)
        * (c * (E1 pd ps n * Einv pd ps n) - 1)
      ≤ ((2 - pd) * (1 + pd) / 2)
          * ((c - 1) * (E1 pd ps n * Einv pd ps n) ^ 2 + (E1 pd ps n * Einv pd ps n) - 1) := by
  have hE1Einv_le : E1 pd ps n * Einv pd ps n ≥ 1 := by
    apply E1Einv_ge_one;
    · linarith;
    · linarith;
    · exact hsum;
  have hE1_ge_one : 1 ≤ E1 pd ps n := by
    apply Reduced.E1_ge_one;
    · linarith;
    · linarith;
    · exact hsum
  have hEinv_pos : 0 < Einv pd ps n := by
    grind +suggestions
  have hE1s : E1 pd ps (n + 1) = 2 * ps * E1 pd ps n + pd * Dmean pd ps n := by
    apply E1_succ;
    · linarith;
    · linarith;
    · exact hsum
  have hEinvval : Einv pd ps (n + 1) = (1 + pd) * (Einv pd ps n / 2 - Delta pd ps n / 4) := by
    rw [ Einv_succ, Sinv_eq ];
    all_goals assumption;
  have hDmean : Dmean pd ps n ≤ E1 pd ps n := by
    apply Dmean_le_E1; all_goals linarith
  have hDnn : 0 ≤ Delta pd ps n := by
    grind +suggestions
  have hWCS : 2 * (E1 pd ps n * Einv pd ps n - 1) ^ 2 ≤ Delta pd ps n * (E2 pd ps n * Einv pd ps n - E1 pd ps n) := by
    apply WCS; all_goals linarith;
  -- Substitute the bounds into the inequality.
  have h_subst : E1 pd ps (n + 1) * Einv pd ps (n + 1) ≤ (1 + ps) * E1 pd ps n * ((1 + pd) * (Einv pd ps n / 2 - Delta pd ps n / 4)) := by
    rw [hE1s, hEinvval];
    exact mul_le_mul_of_nonneg_right ( by nlinarith ) ( mul_nonneg ( by linarith ) ( by nlinarith [ show Delta pd ps n ≤ 2 * Einv pd ps n from by
                                                                                                      grind +suggestions ] ) );
  have h_subst : (E1 pd ps n * Einv pd ps n - E1 pd ps n * Delta pd ps n / 2) * (c * (E1 pd ps n * Einv pd ps n) - 1) ≤ (c - 1) * (E1 pd ps n * Einv pd ps n) ^ 2 + E1 pd ps n * Einv pd ps n - 1 := by
    nlinarith [ mul_le_mul_of_nonneg_left hE1Einv_le hDnn ];
  refine le_trans ( mul_le_mul_of_nonneg_right ‹_› ?_ ) ?_;
  · have h_subst : E2 pd ps n ≥ (E1 pd ps n) ^ 2 := by
      apply E2_ge_E1sq;
      · grobner;
      · linarith;
      · finiteness;
    nlinarith [ mul_le_mul_of_nonneg_left hE1_ge_one hEinv_pos.le ];
  · convert mul_le_mul_of_nonneg_left h_subst ( show 0 ≤ ( 2 - pd ) * ( 1 + pd ) / 2 by nlinarith ) using 1 ; rw [ ← eq_sub_iff_add_eq' ] at hsum ; subst_vars ; ring

/-! ### New four–fold product integral identities (Case 2) -/

/-- `∫ ((A) + (B)) ∂prod4 = 4·E[R]`, where `A = X₁+X₂`, `B = X₃+X₄`. -/
lemma int_prod4_sumAB (n : ℕ) :
    (∫ q : ℝ × ℝ × ℝ × ℝ, ((q.1 + q.2.1) + (q.2.2.1 + q.2.2.2))
        ∂(prod4 (lawMeasure pd ps n)))
      = 4 * E1 pd ps n := by
  haveI := prob_law hpd hps hsum n
  set μ := lawMeasure pd ps n with hμ
  have hab : ∫ q : ℝ × ℝ × ℝ × ℝ, (q.1 + q.2.1) ∂(prod4 μ) = 2 * E1 pd ps n := by
    have h := int_prod_sum hpd hps hsum n
    rw [← prod4_map12 μ, integral_map (by fun_prop) (by fun_prop)] at h
    exact h
  have hcd : ∫ q : ℝ × ℝ × ℝ × ℝ, (q.2.2.1 + q.2.2.2) ∂(prod4 μ) = 2 * E1 pd ps n := by
    have h := int_prod_sum hpd hps hsum n
    rw [← prod4_map34 μ, integral_map (by fun_prop) (by fun_prop)] at h
    exact h
  have iab : Integrable (fun q : ℝ × ℝ × ℝ × ℝ => q.1 + q.2.1) (prod4 μ) :=
    integrable_prod4_law hpd hps hsum n _ (by fun_prop) (2 ^ n + 2 ^ n)
      (fun q h1 h2 h3 h4 => by rw [abs_of_nonneg (by linarith [h1.1, h2.1])]; linarith [h1.2, h2.2])
  have icd : Integrable (fun q : ℝ × ℝ × ℝ × ℝ => q.2.2.1 + q.2.2.2) (prod4 μ) :=
    integrable_prod4_law hpd hps hsum n _ (by fun_prop) (2 ^ n + 2 ^ n)
      (fun q h1 h2 h3 h4 => by rw [abs_of_nonneg (by linarith [h3.1, h4.1])]; linarith [h3.2, h4.2])
  rw [integral_add iab icd, hab, hcd]; ring

/-
`∫ (A−B)²/(A+B) ∂prod4 = 4·E[R] − 4·E[D]`, where `A = X₁+X₂`, `B = X₃+X₄`.
Uses `(A−B)²/(A+B) = (A+B) − 4·par(A,B)`.
-/
lemma int_C_int (n : ℕ) :
    (∫ q : ℝ × ℝ × ℝ × ℝ,
        ((q.1 + q.2.1) - (q.2.2.1 + q.2.2.2)) ^ 2 / ((q.1 + q.2.1) + (q.2.2.1 + q.2.2.2))
        ∂(prod4 (lawMeasure pd ps n)))
      = 4 * E1 pd ps n - 4 * Dmean pd ps n := by
  convert integral_congr_ae _ using 1;
  rotate_left;
  exact fun q => ( q.1 + q.2.1 + ( q.2.2.1 + q.2.2.2 ) ) - 4 * ( q.1 + q.2.1 ) * ( q.2.2.1 + q.2.2.2 ) / ( ( q.1 + q.2.1 ) + ( q.2.2.1 + q.2.2.2 ) );
  · filter_upwards [ ae_box_prod4 hpd hps hsum n ] with q hq;
    rw [ sub_div' ] <;> ring ; linarith [ Set.mem_Icc.mp hq.1, Set.mem_Icc.mp hq.2.1, Set.mem_Icc.mp hq.2.2.1, Set.mem_Icc.mp hq.2.2.2 ];
  · rw [ MeasureTheory.integral_sub ];
    · congr! 1;
      · convert int_prod4_sumAB hpd hps hsum n |> Eq.symm using 1;
      · convert congr_arg ( fun x : ℝ => 4 * x ) ( show Dmean pd ps n = ∫ q : ℝ × ℝ × ℝ × ℝ, ( q.1 + q.2.1 ) * ( q.2.2.1 + q.2.2.2 ) / ( q.1 + q.2.1 + ( q.2.2.1 + q.2.2.2 ) ) ∂prod4 ( lawMeasure pd ps n ) from ?_ ) using 1;
        · simp +decide only [mul_assoc, mul_div_assoc, integral_const_mul];
        · rfl;
    · convert int_prod4_sumAB hpd hps hsum n |> fun h => ( show Integrable ( fun a : ℝ × ℝ × ℝ × ℝ => ( a.1 + a.2.1 ) + ( a.2.2.1 + a.2.2.2 ) ) ( prod4 ( lawMeasure pd ps n ) ) from ?_ ) using 1;
      exact ( by by_contra h; rw [ MeasureTheory.integral_undef h ] at *; linarith [ show 0 < E1 pd ps n from lt_of_lt_of_le zero_lt_one ( E1_ge_one hpd hps hsum n ) ] );
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun q => 4 * ( 2 ^ n + 2 ^ n ) * ( 2 ^ n + 2 ^ n ) / ( 1 + 1 );
      · apply_rules [ MeasureTheory.integrable_const ];
        constructor;
        have := prob_law hpd hps hsum n;
        simp +decide [ prod4 ];
      · refine' Measurable.aestronglyMeasurable _;
        fun_prop;
      · filter_upwards [ ae_box_prod4 hpd hps hsum n ] with q hq;
        rw [ Real.norm_of_nonneg ( div_nonneg ( mul_nonneg ( mul_nonneg zero_le_four ( add_nonneg ( by linarith [ Set.mem_Icc.mp hq.1 ] ) ( by linarith [ Set.mem_Icc.mp hq.2.1 ] ) ) ) ( add_nonneg ( by linarith [ Set.mem_Icc.mp hq.2.2.1 ] ) ( by linarith [ Set.mem_Icc.mp hq.2.2.2 ] ) ) ) ( by linarith [ Set.mem_Icc.mp hq.1, Set.mem_Icc.mp hq.2.1, Set.mem_Icc.mp hq.2.2.1, Set.mem_Icc.mp hq.2.2.2 ] ) ) ];
        gcongr <;> linarith [ Set.mem_Icc.mp hq.1, Set.mem_Icc.mp hq.2.1, Set.mem_Icc.mp hq.2.2.1, Set.mem_Icc.mp hq.2.2.2 ]

/-
`∫ AB(A−B)²/(A+B)² ∂prod4 = 4·E[R]² − 4·E[D²]`.
Uses `AB(A−B)²/(A+B)² = AB − 4·par(A,B)²`.
-/
lemma int_K_int (n : ℕ) :
    (∫ q : ℝ × ℝ × ℝ × ℝ,
        (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2)
          * (((q.1 + q.2.1) - (q.2.2.1 + q.2.2.2)) ^ 2)
          / ((q.1 + q.2.1) + (q.2.2.1 + q.2.2.2)) ^ 2
        ∂(prod4 (lawMeasure pd ps n)))
      = 4 * (E1 pd ps n) ^ 2 - 4 * Dsq pd ps n := by
  rw [ MeasureTheory.integral_congr_ae ];
  any_goals exact fun q => ( q.1 + q.2.1 ) * ( q.2.2.1 + q.2.2.2 ) - 4 * ( ( q.1 + q.2.1 ) * ( q.2.2.1 + q.2.2.2 ) / ( q.1 + q.2.1 + ( q.2.2.1 + q.2.2.2 ) ) ) ^ 2;
  · rw [ MeasureTheory.integral_sub, MeasureTheory.integral_const_mul ];
    · congr! 1;
      convert int_prod4_ab hpd hps hsum n using 1 ; ring;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun q => ( 2 ^ n + 2 ^ n ) * ( 2 ^ n + 2 ^ n );
      · apply_rules [ MeasureTheory.integrable_const ];
        constructor;
        have := prob_law hpd hps hsum n;
        simp +decide [ prod4 ];
      · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( measurable_fst.add measurable_snd.fst ) ( measurable_snd.snd.fst.add measurable_snd.snd.snd ) );
      · filter_upwards [ ae_box_prod4 hpd hps hsum n ] with q hq;
        rw [ Real.norm_of_nonneg ( by nlinarith [ Set.mem_Icc.mp hq.1, Set.mem_Icc.mp hq.2.1, Set.mem_Icc.mp hq.2.2.1, Set.mem_Icc.mp hq.2.2.2 ] ) ] ; nlinarith [ Set.mem_Icc.mp hq.1, Set.mem_Icc.mp hq.2.1, Set.mem_Icc.mp hq.2.2.1, Set.mem_Icc.mp hq.2.2.2 ];
    · refine' MeasureTheory.Integrable.const_mul _ _;
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun q => ( 2 ^ n ) ^ 2;
      · have := prob_law hpd hps hsum n;
        simp +decide [ prod4 ];
      · refine' Measurable.aestronglyMeasurable _;
        fun_prop;
      · filter_upwards [ ae_box_prod4 hpd hps hsum n ] with q hq;
        rw [ Real.norm_of_nonneg ( sq_nonneg _ ) ];
        exact pow_le_pow_left₀ ( div_nonneg ( mul_nonneg ( add_nonneg ( by linarith [ Set.mem_Icc.mp hq.1 ] ) ( by linarith [ Set.mem_Icc.mp hq.2.1 ] ) ) ( add_nonneg ( by linarith [ Set.mem_Icc.mp hq.2.2.1 ] ) ( by linarith [ Set.mem_Icc.mp hq.2.2.2 ] ) ) ) ( add_nonneg ( add_nonneg ( by linarith [ Set.mem_Icc.mp hq.1 ] ) ( by linarith [ Set.mem_Icc.mp hq.2.1 ] ) ) ( add_nonneg ( by linarith [ Set.mem_Icc.mp hq.2.2.1 ] ) ( by linarith [ Set.mem_Icc.mp hq.2.2.2 ] ) ) ) ) ( div_le_of_le_mul₀ ( by linarith [ Set.mem_Icc.mp hq.1, Set.mem_Icc.mp hq.2.1, Set.mem_Icc.mp hq.2.2.1, Set.mem_Icc.mp hq.2.2.2 ] ) ( by linarith [ Set.mem_Icc.mp hq.1, Set.mem_Icc.mp hq.2.1, Set.mem_Icc.mp hq.2.2.1, Set.mem_Icc.mp hq.2.2.2 ] ) ( by nlinarith [ Set.mem_Icc.mp hq.1, Set.mem_Icc.mp hq.2.1, Set.mem_Icc.mp hq.2.2.1, Set.mem_Icc.mp hq.2.2.2 ] ) ) _;
  · filter_upwards [ ae_box_prod4 hpd hps hsum n ] with q hq;
    grind

/-
`∫ (A−B)²/(AB) ∂prod4 = 4·E[R]·Sinv − 2`, where `Sinv = E[1/(X+Y)]`.
Uses `(A−B)²/(AB) = A/B + B/A − 2` and independence of the two blocks.
-/
lemma int_J_int (n : ℕ) :
    (∫ q : ℝ × ℝ × ℝ × ℝ,
        ((q.1 + q.2.1) - (q.2.2.1 + q.2.2.2)) ^ 2 / ((q.1 + q.2.1) * (q.2.2.1 + q.2.2.2))
        ∂(prod4 (lawMeasure pd ps n)))
      = 4 * E1 pd ps n * Sinv pd ps n - 2 := by
  have h_integrable : MeasureTheory.Integrable (fun q : ℝ × ℝ × ℝ × ℝ => (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2)⁻¹) (prod4 (lawMeasure pd ps n)) ∧ MeasureTheory.Integrable (fun q : ℝ × ℝ × ℝ × ℝ => (q.2.2.1 + q.2.2.2) * (q.1 + q.2.1)⁻¹) (prod4 (lawMeasure pd ps n)) := by
    constructor;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun q => 2 ^ n * 2 ^ n;
      · unfold prod4;
        have := prob_law hpd hps hsum n;
        norm_num [ MeasureTheory.integrable_const_iff ];
        infer_instance;
      · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( measurable_fst.add measurable_snd.fst ) ( Measurable.inv ( measurable_snd.snd.fst.add measurable_snd.snd.snd ) ) );
      · have h_bound : ∀ᵐ q ∂prod4 (lawMeasure pd ps n), q.1 ∈ Set.Icc (1 : ℝ) (2 ^ n) ∧ q.2.1 ∈ Set.Icc (1 : ℝ) (2 ^ n) ∧ q.2.2.1 ∈ Set.Icc (1 : ℝ) (2 ^ n) ∧ q.2.2.2 ∈ Set.Icc (1 : ℝ) (2 ^ n) := by
          apply_rules [ ae_box_prod4 ];
        filter_upwards [ h_bound ] with q hq using by rw [ Real.norm_of_nonneg ( mul_nonneg ( add_nonneg ( by linarith [ hq.1.1 ] ) ( by linarith [ hq.2.1.1 ] ) ) ( inv_nonneg.2 ( add_nonneg ( by linarith [ hq.2.2.1.1 ] ) ( by linarith [ hq.2.2.2.1 ] ) ) ) ) ] ; exact div_le_of_le_mul₀ ( by linarith [ hq.2.2.1.1, hq.2.2.2.1 ] ) ( by positivity ) ( by nlinarith [ hq.1.1, hq.1.2, hq.2.1.1, hq.2.1.2, hq.2.2.1.1, hq.2.2.1.2, hq.2.2.2.1, hq.2.2.2.2 ] ) ;
    · have h_integrable : MeasureTheory.Integrable (fun q : ℝ × ℝ × ℝ × ℝ => (q.2.2.1 + q.2.2.2) * (q.1 + q.2.1)⁻¹) (prod4 (lawMeasure pd ps n)) := by
        have h_bound : ∀ q : ℝ × ℝ × ℝ × ℝ, q.1 ∈ Set.Icc 1 (2 ^ n) → q.2.1 ∈ Set.Icc 1 (2 ^ n) → q.2.2.1 ∈ Set.Icc 1 (2 ^ n) → q.2.2.2 ∈ Set.Icc 1 (2 ^ n) → |(q.2.2.1 + q.2.2.2) * (q.1 + q.2.1)⁻¹| ≤ 2 * 2 ^ n := by
          norm_num +zetaDelta at *;
          exact fun a b c d ha hb hc hd he hf hg hh => by rw [ ← div_eq_mul_inv ] ; rw [ div_le_iff₀ ] <;> cases abs_cases ( c + d ) <;> cases abs_cases ( a + b ) <;> nlinarith;
        apply_rules [ integrable_prod4_law ];
        exact Measurable.mul ( measurable_snd.snd.fst.add measurable_snd.snd.snd ) ( Measurable.inv ( measurable_fst.add measurable_snd.fst ) );
      convert h_integrable using 1;
  have h_integrable : ∫ q : ℝ × ℝ × ℝ × ℝ, (q.1 + q.2.1 - (q.2.2.1 + q.2.2.2)) ^ 2 / ((q.1 + q.2.1) * (q.2.2.1 + q.2.2.2)) ∂(prod4 (lawMeasure pd ps n)) = (∫ q : ℝ × ℝ × ℝ × ℝ, (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2)⁻¹ ∂(prod4 (lawMeasure pd ps n))) + (∫ q : ℝ × ℝ × ℝ × ℝ, (q.2.2.1 + q.2.2.2) * (q.1 + q.2.1)⁻¹ ∂(prod4 (lawMeasure pd ps n))) - 2 := by
    rw [ ← MeasureTheory.integral_add h_integrable.1 h_integrable.2 ];
    rw [ MeasureTheory.integral_congr_ae ];
    rotate_right;
    use fun q => ( q.1 + q.2.1 ) * ( q.2.2.1 + q.2.2.2 ) ⁻¹ + ( q.2.2.1 + q.2.2.2 ) * ( q.1 + q.2.1 ) ⁻¹ - 2;
    · rw [ MeasureTheory.integral_sub ] <;> norm_num;
      · unfold prod4; norm_num [ MeasureTheory.Measure.real ] ;
        have := prob_law hpd hps hsum n; simp_all +decide [ MeasureTheory.Measure.prod_apply ] ;
      · exact MeasureTheory.Integrable.add h_integrable.1 h_integrable.2;
      · have h_prob : IsProbabilityMeasure (lawMeasure pd ps n) := by
          grind +suggestions;
        simp +decide [ prod4 ];
    · have h_eq : ∀ᵐ q : ℝ × ℝ × ℝ × ℝ ∂(prod4 (lawMeasure pd ps n)), 0 < q.1 + q.2.1 ∧ 0 < q.2.2.1 + q.2.2.2 := by
        have h_eq : ∀ᵐ q : ℝ × ℝ × ℝ × ℝ ∂(prod4 (lawMeasure pd ps n)), q.1 ∈ Set.Icc (1 : ℝ) (2 ^ n) ∧ q.2.1 ∈ Set.Icc (1 : ℝ) (2 ^ n) ∧ q.2.2.1 ∈ Set.Icc (1 : ℝ) (2 ^ n) ∧ q.2.2.2 ∈ Set.Icc (1 : ℝ) (2 ^ n) := by
          apply ae_box_prod4;
          · linarith;
          · linarith;
          · exact hsum;
        filter_upwards [ h_eq ] with q hq using ⟨ by linarith [ hq.1.1, hq.2.1.1 ], by linarith [ hq.2.2.1.1, hq.2.2.2.1 ] ⟩;
      filter_upwards [ h_eq ] with q hq using by rw [ ← div_eq_mul_inv, ← div_eq_mul_inv ] ; rw [ div_add_div, div_sub', div_eq_div_iff ] <;> nlinarith;
  have h_integrable : ∫ q : ℝ × ℝ × ℝ × ℝ, (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2)⁻¹ ∂(prod4 (lawMeasure pd ps n)) = (∫ q : ℝ × ℝ, (q.1 + q.2) ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n))) * (∫ q : ℝ × ℝ, (q.1 + q.2)⁻¹ ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n))) := by
    rw [ int_prod4_eq_assoc ];
    · convert MeasureTheory.integral_prod_mul _ _ using 1;
      · rfl;
      · have h_finite : IsFiniteMeasure (lawMeasure pd ps n) := by
          constructor;
          have := prob_law hpd hps hsum n;
          exact this.measure_univ.symm ▸ ENNReal.one_lt_top;
        infer_instance;
      · have h_finite : IsFiniteMeasure (lawMeasure pd ps n) := by
          constructor;
          have := prob_law hpd hps hsum n;
          exact this.measure_univ.symm ▸ ENNReal.one_lt_top;
        infer_instance;
    · linarith;
    · linarith;
    · linarith;
    · exact Measurable.mul ( measurable_fst.add measurable_snd.fst ) ( Measurable.inv ( measurable_snd.snd.fst.add measurable_snd.snd.snd ) );
  have h_integrable : ∫ q : ℝ × ℝ × ℝ × ℝ, (q.2.2.1 + q.2.2.2) * (q.1 + q.2.1)⁻¹ ∂(prod4 (lawMeasure pd ps n)) = (∫ q : ℝ × ℝ, (q.1 + q.2) ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n))) * (∫ q : ℝ × ℝ, (q.1 + q.2)⁻¹ ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n))) := by
    rw [ int_prod4_eq_assoc ];
    · convert MeasureTheory.integral_prod_mul ( fun p : ℝ × ℝ => ( p.1 + p.2 ) ⁻¹ ) ( fun p : ℝ × ℝ => p.1 + p.2 ) using 1;
      congr! 1;
      · exact funext fun x => by rw [ mul_comm ] ; rfl;
      · ring;
      · have := prob_law hpd hps hsum n;
        infer_instance;
      · have h_finite : IsFiniteMeasure (lawMeasure pd ps n) := by
          constructor;
          have := prob_law hpd hps hsum n;
          exact this.measure_univ.symm ▸ ENNReal.one_lt_top;
        infer_instance;
    · linarith;
    · linarith;
    · linarith;
    · fun_prop;
  simp_all +decide [ int_prod_sum, Sinv ];
  ring

/-! ### The two Cauchy–Schwarz estimates of Case 2 -/

/-
**Refined diamond second–moment estimate (Cauchy–Schwarz).**
`(4E[R] − 4E[D])² ≤ (4E[R]² − 4E[D²])·(4E[R]·Sinv − 2)`.
-/
lemma diamond_CS (n : ℕ) :
    (4 * E1 pd ps n - 4 * Dmean pd ps n) ^ 2
      ≤ (4 * (E1 pd ps n) ^ 2 - 4 * Dsq pd ps n) * (4 * E1 pd ps n * Sinv pd ps n - 2) := by
  have := @integral_cauchy_schwarz_sq;
  convert this (prod4 (lawMeasure pd ps n)) (fun q => ((q.1 + q.2.1) - (q.2.2.1 + q.2.2.2)) ^ 2 / ((q.1 + q.2.1) + (q.2.2.1 + q.2.2.2))) (fun q => (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2) * ((q.1 + q.2.1 - (q.2.2.1 + q.2.2.2)) ^ 2) / ((q.1 + q.2.1) + (q.2.2.1 + q.2.2.2)) ^ 2) (fun q => ((q.1 + q.2.1) - (q.2.2.1 + q.2.2.2)) ^ 2 / ((q.1 + q.2.1) * (q.2.2.1 + q.2.2.2))) _ _ _ _ using 1;
  any_goals rw [ int_C_int ];
  any_goals assumption;
  · rw [ int_K_int, int_J_int ];
    all_goals assumption;
  · refine' integrable_prod4_law hpd hps hsum n _ _ _ _;
    fun_prop;
    exact ( 2 ^ n + 2 ^ n ) * ( 2 ^ n + 2 ^ n );
    intro q hq1 hq2 hq3 hq4; rw [ abs_of_nonneg ( by exact div_nonneg ( mul_nonneg ( mul_nonneg ( by linarith [ Set.mem_Icc.mp hq1, Set.mem_Icc.mp hq2 ] ) ( by linarith [ Set.mem_Icc.mp hq3, Set.mem_Icc.mp hq4 ] ) ) ( sq_nonneg _ ) ) ( sq_nonneg _ ) ) ] ; rw [ div_le_iff₀ ] <;> norm_num at *;
    · exact mul_le_mul ( by nlinarith ) ( by nlinarith ) ( by nlinarith ) ( by positivity );
    · exact sq_pos_of_pos ( by linarith );
  · refine' integrable_prod4_law hpd hps hsum n _ _ _ _;
    fun_prop;
    exact ( 2 ^ n + 2 ^ n ) ^ 2 / ( 1 * 1 );
    intro q hq1 hq2 hq3 hq4; rw [ abs_of_nonneg ( div_nonneg ( sq_nonneg _ ) ( mul_nonneg ( add_nonneg ( by linarith [ hq1.1 ] ) ( by linarith [ hq2.1 ] ) ) ( add_nonneg ( by linarith [ hq3.1 ] ) ( by linarith [ hq4.1 ] ) ) ) ) ] ; rw [ div_le_div_iff₀ ] <;> try nlinarith [ hq1.1, hq1.2, hq2.1, hq2.2, hq3.1, hq3.2, hq4.1, hq4.2 ];
    nlinarith only [ sq_nonneg ( q.1 + q.2.1 - ( q.2.2.1 + q.2.2.2 ) ), hq1.1, hq1.2, hq2.1, hq2.2, hq3.1, hq3.2, hq4.1, hq4.2, mul_le_mul_of_nonneg_left hq1.1 ( show 0 ≤ q.2.2.1 + q.2.2.2 by linarith [ hq3.1, hq4.1 ] ), mul_le_mul_of_nonneg_left hq2.1 ( show 0 ≤ q.2.2.1 + q.2.2.2 by linarith [ hq3.1, hq4.1 ] ) ];
  · refine' integrable_prod4_law hpd hps hsum n _ _ _ _;
    fun_prop;
    exact 4 * 2 ^ n;
    intro q hq1 hq2 hq3 hq4; rw [ abs_of_nonneg ( div_nonneg ( sq_nonneg _ ) ( by linarith [ Set.mem_Icc.mp hq1, Set.mem_Icc.mp hq2, Set.mem_Icc.mp hq3, Set.mem_Icc.mp hq4 ] ) ) ] ; rw [ div_le_iff₀ ] <;> nlinarith [ Set.mem_Icc.mp hq1, Set.mem_Icc.mp hq2, Set.mem_Icc.mp hq3, Set.mem_Icc.mp hq4, pow_pos ( zero_lt_two' ℝ ) n ] ;
  · intro t;
    filter_upwards [ ae_box_prod4 hpd hps hsum n ] with q hq;
    field_simp;
    rw [ div_add_div, mul_div, le_div_iff₀ ] <;> try nlinarith [ Set.mem_Icc.mp hq.1, Set.mem_Icc.mp hq.2.1, Set.mem_Icc.mp hq.2.2.1, Set.mem_Icc.mp hq.2.2.2 ];
    · norm_num +zetaDelta at *;
      exact mul_nonneg ( sq_nonneg _ ) ( by nlinarith [ sq_nonneg ( ( q.1 + q.2.1 ) * ( q.2.2.1 + q.2.2.2 ) - ( q.1 + q.2.1 + ( q.2.2.1 + q.2.2.2 ) ) * t ) ] );
    · exact mul_pos ( sq_pos_of_pos ( by linarith [ Set.mem_Icc.mp hq.1, Set.mem_Icc.mp hq.2.1, Set.mem_Icc.mp hq.2.2.1, Set.mem_Icc.mp hq.2.2.2 ] ) ) ( mul_pos ( by linarith [ Set.mem_Icc.mp hq.1, Set.mem_Icc.mp hq.2.1 ] ) ( by linarith [ Set.mem_Icc.mp hq.2.2.1, Set.mem_Icc.mp hq.2.2.2 ] ) )

/-
**Harmonic–mean estimate (Cauchy–Schwarz).** `1 ≤ 2·Sinv·E[D]`, i.e. `E[D] ≥ 1/(2 Sinv)`.
-/
lemma harm_CS (n : ℕ) : 1 ≤ (2 * Sinv pd ps n) * Dmean pd ps n := by
  have h_integrable : MeasureTheory.Integrable (fun q : ℝ × ℝ × ℝ × ℝ => (diamondMap q)⁻¹) (prod4 (lawMeasure pd ps n)) ∧ MeasureTheory.Integrable (fun q : ℝ × ℝ × ℝ × ℝ => diamondMap q) (prod4 (lawMeasure pd ps n)) := by
    constructor;
    · refine' integrable_prod4_law hpd hps hsum n _ _ _ _;
      exact Measurable.inv ( measurable_diamondMap );
      exact 1;
      intro q hq1 hq2 hq3 hq4; rw [ abs_of_nonneg ( inv_nonneg.mpr ( show 0 ≤ diamondMap q from by
                                                                      exact div_nonneg ( mul_nonneg ( add_nonneg ( le_trans zero_le_one hq1.1 ) ( le_trans zero_le_one hq2.1 ) ) ( add_nonneg ( le_trans zero_le_one hq3.1 ) ( le_trans zero_le_one hq4.1 ) ) ) ( add_nonneg ( add_nonneg ( le_trans zero_le_one hq1.1 ) ( le_trans zero_le_one hq2.1 ) ) ( add_nonneg ( le_trans zero_le_one hq3.1 ) ( le_trans zero_le_one hq4.1 ) ) ) ) ) ] ; exact inv_le_one_of_one_le₀ ( by
                                                                      exact Reduced.diamond_bounds hq1.1 hq1.2 hq2.1 hq2.2 hq3.1 hq3.2 hq4.1 hq4.2 |>.1 ) ;
    · refine' integrable_prod4_law hpd hps hsum n diamondMap measurable_diamondMap ( 2 ^ n ) _;
      unfold diamondMap; norm_num;
      intro a b c d ha hb hc hd he hf hg hh; rw [ abs_of_nonneg ( by exact div_nonneg ( mul_nonneg ( by linarith ) ( by linarith ) ) ( by linarith ) ) ] ; exact div_le_of_le_mul₀ ( by linarith ) ( by linarith ) ( by nlinarith ) ;
  convert integral_cauchy_schwarz_sq ( prod4 ( lawMeasure pd ps n ) ) ( fun _ => 1 ) ( fun q => ( diamondMap q ) ⁻¹ ) ( fun q => diamondMap q ) _ _ _ _ using 1 <;> norm_num [ h_integrable ];
  · unfold prod4 ;
    have := prob_law hpd hps hsum n; simp_all +decide [ MeasureTheory.Measure.prod_apply, MeasureTheory.Measure.real ] ;
  · rw [ int_prod4_diamond_inv ] ; ring!;
    · linarith;
    · linarith;
    · exact hsum;
  · apply_rules [ MeasureTheory.integrable_const ];
    constructor ; norm_num [ prod4 ];
    have := prob_law hpd hps hsum n; aesop;
  · intro t
    have h_nonneg : ∀ᵐ q ∂(prod4 (lawMeasure pd ps n)), 1 ≤ diamondMap q := by
      filter_upwards [ ae_box_prod4 hpd hps hsum n ] with q hq using by
        exact Reduced.diamond_bounds hq.1.1 hq.1.2 hq.2.1.1 hq.2.1.2 hq.2.2.1.1 hq.2.2.1.2 hq.2.2.2.1 hq.2.2.2.2 |>.1;
    filter_upwards [ h_nonneg ] with q hq using by norm_num; nlinarith [ sq_nonneg ( t * diamondMap q - 1 ), mul_inv_cancel₀ ( by linarith : diamondMap q ≠ 0 ) ] ;

/-! ### Consequences of the Cauchy–Schwarz estimates -/

/-
`2·E[R]·Sinv ≤ E[R]·E[1/R]` (since `2 Sinv = Einv − Δ/2 ≤ Einv`).
-/
lemma two_E1_Sinv_le (n : ℕ) : 2 * E1 pd ps n * Sinv pd ps n ≤ E1 pd ps n * Einv pd ps n := by
  -- By the properties of the mean and variance, we know that $Sinv pd ps n \leq Einv pd ps n / 2$.
  have h_Sinv_le_Einv_div_2 : Sinv pd ps n ≤ Einv pd ps n / 2 := by
    linarith [ Sinv_eq hpd hps hsum n, Delta_nonneg hpd hps hsum n ];
  nlinarith [ E1_ge_one hpd hps hsum n ]

/-
**Lower bound on the diamond mean (Case 2).** If `E[R]E[1/R] ≤ 11/5` then `E[D] ≥ (5/11)E[R]`.
-/
lemma Dmean_lb (n : ℕ) (hP : E1 pd ps n * Einv pd ps n ≤ 11 / 5) :
    5 / 11 * E1 pd ps n ≤ Dmean pd ps n := by
  -- By multiplying both sides of the inequality $1 \leq 2 * Sinv pd ps n * Dmean pd ps n$ by $E1 pd ps n$, we get $E1 pd ps n \leq 2 * E1 pd ps n * Sinv pd ps n * Dmean pd ps n$.
  have h_mul : E1 pd ps n ≤ 2 * E1 pd ps n * Sinv pd ps n * Dmean pd ps n := by
    have h_mul : 1 ≤ 2 * Sinv pd ps n * Dmean pd ps n := by
      grind +suggestions;
    nlinarith [ show 0 ≤ E1 pd ps n by exact le_trans zero_le_one ( E1_ge_one hpd hps hsum n ) ];
  by_cases hD : Dmean pd ps n ≥ 0;
  · nlinarith [ mul_le_mul_of_nonneg_left hP hD, mul_le_mul_of_nonneg_left ( two_E1_Sinv_le hpd hps hsum n ) hD, E1_ge_one hpd hps hsum n, Sinv_nonneg hpd hps hsum n ];
  · contrapose! h_mul;
    exact lt_of_le_of_lt ( mul_nonpos_of_nonneg_of_nonpos ( mul_nonneg ( mul_nonneg zero_le_two ( by linarith [ E1_ge_one hpd hps hsum n ] ) ) ( by linarith [ Sinv_nonneg hpd hps hsum n ] ) ) ( by linarith ) ) ( by linarith [ E1_ge_one hpd hps hsum n ] )

/-
**Upper bound on the diamond second moment (Case 2).** If `E[R]E[1/R] ≤ 11/5` then
`E[D²] ≤ E[R]² − (5/3)(E[R] − E[D])²`.
-/
lemma Dsq_ub (n : ℕ) (hP : E1 pd ps n * Einv pd ps n ≤ 11 / 5) :
    Dsq pd ps n ≤ (E1 pd ps n) ^ 2 - 5 / 3 * (E1 pd ps n - Dmean pd ps n) ^ 2 := by
  have := @diamond_CS;
  -- From `two_E1_Sinv_le hpd hps hsum n` and `hP : E1*Einv ≤ 11/5`: `2 E1 Sinv ≤ 11/5`, hence `4 E1 Sinv - 2 ≤ 2(E1 Einv - 1) ≤ 12/5`.
  have h_bound : 4 * E1 pd ps n * Sinv pd ps n - 2 ≤ 12 / 5 := by
    linarith [ two_E1_Sinv_le hpd hps hsum n ];
  nlinarith [ this hpd hps hsum n, Dsq_le_E1sq hpd hps hsum n ]

/-! ### Case 2: `1/2 ≤ pd ≤ 1/√3` -/

/-- **Case 2, step (product moment).** From the level-`n` invariant, `E[R]E[1/R] ≤ 11/5`
propagates to level `n+1` (via `logistic_step` with relative second moment `c = 3`). -/
lemma case2_stepA (hpd_lo : 1 / 2 ≤ pd) (hpd2 : pd ^ 2 ≤ 1 / 3) (n : ℕ)
    (h2 : E2 pd ps n ≤ 3 * (E1 pd ps n) ^ 2) (hP : E1 pd ps n * Einv pd ps n ≤ 11 / 5) :
    E1 pd ps (n + 1) * Einv pd ps (n + 1) ≤ 11 / 5 := by
  have hP1 : 1 ≤ E1 pd ps n * Einv pd ps n := E1Einv_ge_one hpd hps hsum n
  have hstep := logistic_step hpd hps hsum 3 n (by linarith [h2])
  have hK : (2 - pd) * (1 + pd) / 2 ≤ 9 / 8 := by nlinarith [sq_nonneg (2 * pd - 1)]
  have hKpos : 0 ≤ (2 - pd) * (1 + pd) / 2 := by nlinarith [hpd_lo, hpd2]
  have h3P : 0 < 3 * (E1 pd ps n * Einv pd ps n) - 1 := by linarith
  have hquad : ((2 - pd) * (1 + pd) / 2) * (2 * (E1 pd ps n * Einv pd ps n) ^ 2
        + (E1 pd ps n * Einv pd ps n) - 1)
      ≤ 11 / 5 * (3 * (E1 pd ps n * Einv pd ps n) - 1) := by
    nlinarith [hK, hKpos, hP1, hP,
      mul_nonneg (sub_nonneg.mpr hP) (sub_nonneg.mpr hP1),
      sq_nonneg (E1 pd ps n * Einv pd ps n - 11 / 5)]
  nlinarith [hstep, hquad, h3P]

/-- **Case 2, step (relative second moment).** From the level-`n` invariant, `E[R²] ≤ 3·E[R]²`
propagates to level `n+1`. -/
lemma case2_stepB (hpd_lo : 1 / 2 ≤ pd) (hpd2 : pd ^ 2 ≤ 1 / 3) (n : ℕ)
    (h2 : E2 pd ps n ≤ 3 * (E1 pd ps n) ^ 2) (hP : E1 pd ps n * Einv pd ps n ≤ 11 / 5) :
    E2 pd ps (n + 1) ≤ 3 * (E1 pd ps (n + 1)) ^ 2 := by
  have hpdpos : 0 < pd := by linarith
  have ha : 1 ≤ E1 pd ps n := E1_ge_one hpd hps hsum n
  have hDsq := Dsq_ub hpd hps hsum n hP
  have hE2s := E2_succ hpd hps hsum n
  have hE1s := E1_succ hpd hps hsum n
  have hDmean_lb := Dmean_lb hpd hps hsum n hP
  -- relation `pd*(E1 - Dmean) = (2-pd)*E1 - E1(n+1)`
  have hrel : pd * (E1 pd ps n - Dmean pd ps n) = (2 - pd) * E1 pd ps n - E1 pd ps (n + 1) := by
    rw [hE1s]; nlinarith [hsum]
  have hbound : E2 pd ps (n + 1)
      ≤ (8 - 7 * pd) * (E1 pd ps n) ^ 2
        - (5 / (3 * pd)) * ((2 - pd) * E1 pd ps n - E1 pd ps (n + 1)) ^ 2 := by
    have e : (5 / (3 * pd)) * ((2 - pd) * E1 pd ps n - E1 pd ps (n + 1)) ^ 2
        = (5 * pd / 3) * (E1 pd ps n - Dmean pd ps n) ^ 2 := by
      rw [← hrel]; field_simp
    rw [e]
    nlinarith [hE2s, hDsq, h2, hps, hpd, hsum, sq_nonneg (E1 pd ps n - Dmean pd ps n)]
  have hr0 : (22 - 17 * pd) / 11 * E1 pd ps n ≤ E1 pd ps (n + 1) := by
    rw [hE1s]; nlinarith [hDmean_lb, hpdpos, hsum]
  exact case2_close pd (E1 pd ps n) (E1 pd ps (n + 1)) (E2 pd ps (n + 1))
    hpd_lo hpd2 ha hr0 hbound

/-- **Case 2 joint invariant.** For `1/2 ≤ pd` and `pd² ≤ 1/3`, both
`E[R²] ≤ 3·E[R]²` and `E[R]E[1/R] ≤ 11/5` hold for every `n`. -/
lemma case2_inv (hpd_lo : 1 / 2 ≤ pd) (hpd2 : pd ^ 2 ≤ 1 / 3) (n : ℕ) :
    E2 pd ps n ≤ 3 * (E1 pd ps n) ^ 2 ∧ E1 pd ps n * Einv pd ps n ≤ 11 / 5 := by
  induction n with
  | zero => constructor <;> norm_num [E1, E2, Einv, integral_dirac]
  | succ n ih =>
    exact ⟨case2_stepB hpd hps hsum hpd_lo hpd2 n ih.1 ih.2,
           case2_stepA hpd hps hsum hpd_lo hpd2 n ih.1 ih.2⟩

/-- **Uniform product–moment bound, Case 2.** -/
lemma uniform_product_case2 (hpd_lo : 1 / 2 ≤ pd) (hpd2 : pd ^ 2 ≤ 1 / 3) :
    ∃ M : ℝ, ∀ n, E1 pd ps n * Einv pd ps n ≤ M :=
  ⟨11 / 5, fun n => (case2_inv hpd hps hsum hpd_lo hpd2 n).2⟩

/-- **Combined product–moment bound for `pd ≤ 1/√3`.** Under the single hypothesis
`pd² ≤ 1/3` (i.e. `pd ≤ 1/√3`), the uniform product–moment bound
`E[R n]·E[1/R n] ≤ 11/5` holds for every `n`.  This merges Case 1 (`pd ≤ 1/2`, via
`E1Einv_le`) and Case 2 (`1/2 < pd`, via the `.2` projection of `case2_inv`); neither branch
uses the monotonicity hypothesis `hmono`. -/
lemma E1Einv_le_of_sq (hthird : pd ^ 2 ≤ 1 / 3) (n : ℕ) :
    E1 pd ps n * Einv pd ps n ≤ 11 / 5 := by
  rcases le_or_gt pd (1 / 2) with h | h
  · exact E1Einv_le hpd hps hsum h n
  · exact (case2_inv hpd hps hsum (le_of_lt h) hthird n).2

/-! ### Case 3: `pd > 1/√3`, using the a.s. monotonicity `R_{n+1} ≥ R_n` -/

/-
Base value `E[R₁] = 2 ps + pd`.
-/
lemma E1_one : E1 pd ps 1 = 2 * ps + pd := by
  convert Reduced.E1_succ hpd hps hsum 0 using 1 ; ring;
  unfold E1 Dmean; norm_num [ Reduced.lawMeasure ] ; ring;
  unfold prod4; norm_num [ MeasureTheory.integral_dirac, diamondMap ] ;
  erw [ MeasureTheory.integral_prod ] ; norm_num [ diamondVal ] ; ring;
  · erw [ MeasureTheory.integral_prod ] ; norm_num [ par ];
    · erw [ MeasureTheory.integral_prod ] ; norm_num [ MeasureTheory.integral_dirac ];
      rw [ MeasureTheory.integrable_prod_iff ] ; norm_num [ MeasureTheory.integrable_dirac ];
      exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( measurable_const.mul ( measurable_fst.add measurable_snd ) ) ( Measurable.inv ( measurable_const.add ( measurable_fst.add measurable_snd ) ) ) );
    · rw [ MeasureTheory.integrable_prod_iff ] ; norm_num [ par ];
      · erw [ MeasureTheory.integrable_prod_iff ] ; norm_num [ MeasureTheory.integrable_dirac ];
        exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( measurable_const.mul ( measurable_fst.add measurable_snd ) ) ( Measurable.inv ( measurable_const.add ( measurable_fst.add measurable_snd ) ) ) );
      · exact Measurable.aestronglyMeasurable ( by exact Measurable.div ( measurable_const.add measurable_fst |> Measurable.mul <| measurable_snd.fst.add measurable_snd.snd ) ( measurable_const.add measurable_fst |> Measurable.add <| measurable_snd.fst.add measurable_snd.snd ) );
  · rw [ MeasureTheory.integrable_prod_iff ];
    · norm_num [ MeasureTheory.integrable_dirac, diamondVal ];
      rw [ MeasureTheory.integrable_prod_iff ];
      · norm_num [ MeasureTheory.integrable_dirac, par ];
        erw [ MeasureTheory.integrable_prod_iff ] ; norm_num [ MeasureTheory.integrable_dirac ];
        exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( measurable_const.mul ( measurable_fst.add measurable_snd ) ) ( Measurable.inv ( measurable_const.add ( measurable_fst.add measurable_snd ) ) ) );
      · exact Measurable.aestronglyMeasurable ( by exact Measurable.div ( measurable_const.add measurable_fst |> Measurable.mul <| measurable_snd.fst.add measurable_snd.snd ) ( measurable_const.add measurable_fst |> Measurable.add <| measurable_snd.fst.add measurable_snd.snd ) );
    · exact Measurable.aestronglyMeasurable ( by exact Measurable.div ( Measurable.mul ( measurable_fst.add measurable_snd.fst ) ( measurable_snd.snd.fst.add measurable_snd.snd.snd ) ) ( Measurable.add ( measurable_fst.add measurable_snd.fst ) ( measurable_snd.snd.fst.add measurable_snd.snd.snd ) ) )

/-
Base value `E[R₁²] = 4 ps + pd`.
-/
lemma E2_one : E2 pd ps 1 = 4 * ps + pd := by
  rw [ show E2 pd ps 1 = ps * ( 2 * E2 pd ps 0 + 2 * ( E1 pd ps 0 ) ^ 2 ) + pd * Dsq pd ps 0 by
        convert E2_succ hpd hps hsum 0 using 1 ];
  unfold E2 E1 Dsq;
  unfold lawMeasure prod4; norm_num;
  erw [ MeasureTheory.integral_prod ] ; norm_num [ diamondMap ];
  · erw [ MeasureTheory.integral_prod ] ; norm_num [ diamondVal ] ; ring;
    · erw [ MeasureTheory.integral_prod ] ; norm_num [ par ];
      erw [ MeasureTheory.integrable_prod_iff ] ; norm_num [ par ];
      · norm_num [ MeasureTheory.integrable_dirac ];
      · exact Measurable.aestronglyMeasurable ( by exact Measurable.pow_const ( by exact Measurable.div ( measurable_const.mul ( measurable_fst.add measurable_snd ) ) ( measurable_const.add ( measurable_fst.add measurable_snd ) ) ) _ );
    · erw [ MeasureTheory.integrable_prod_iff ] ; norm_num [ diamondVal ];
      · erw [ MeasureTheory.integrable_prod_iff ] ; norm_num [ diamondVal ];
        · norm_num [ MeasureTheory.integrable_dirac, par ];
        · exact Measurable.aestronglyMeasurable ( by exact Measurable.pow_const ( by exact Measurable.div ( measurable_const.mul ( measurable_fst.add measurable_snd ) ) ( measurable_const.add ( measurable_fst.add measurable_snd ) ) ) _ );
      · exact Measurable.aestronglyMeasurable ( by exact Measurable.pow_const ( by exact Measurable.div ( by exact Measurable.mul ( measurable_const.add measurable_fst ) ( measurable_snd.fst.add measurable_snd.snd ) ) ( by exact Measurable.add ( measurable_const.add measurable_fst ) ( measurable_snd.fst.add measurable_snd.snd ) ) ) _ );
  · erw [ MeasureTheory.integrable_prod_iff ] ; norm_num [ diamondMap ];
    · erw [ MeasureTheory.integrable_prod_iff ] ; norm_num [ diamondVal ];
      · erw [ MeasureTheory.integrable_prod_iff ] ; norm_num [ par ];
        · norm_num [ MeasureTheory.integrable_dirac ];
        · exact Measurable.aestronglyMeasurable ( by exact Measurable.pow_const ( by exact Measurable.div ( measurable_const.mul ( measurable_fst.add measurable_snd ) ) ( measurable_const.add ( measurable_fst.add measurable_snd ) ) ) _ );
      · exact Measurable.aestronglyMeasurable ( by exact Measurable.pow_const ( by exact Measurable.div ( by exact Measurable.mul ( measurable_const.add measurable_fst ) ( measurable_snd.fst.add measurable_snd.snd ) ) ( by exact Measurable.add ( measurable_const.add measurable_fst ) ( measurable_snd.fst.add measurable_snd.snd ) ) ) _ );
    · exact Measurable.aestronglyMeasurable ( by exact Measurable.pow_const ( by exact measurable_diamondMap ) _ )

/-
**Coarse one–step second moment bound.** `E[R²_{n+1}] ≤ 2 ps E[R²_n] + (2−pd)E[R_n]²`.
-/
lemma coarse_E2 (n : ℕ) :
    E2 pd ps (n + 1) ≤ 2 * ps * E2 pd ps n + (2 - pd) * (E1 pd ps n) ^ 2 := by
  have h_E2_succ : E2 pd ps (n + 1) = ps * (2 * E2 pd ps n + 2 * (E1 pd ps n) ^ 2) + pd * Dsq pd ps n :=
    E2_succ hpd hps hsum n
  nlinarith [h_E2_succ, Dsq_le_E1sq hpd hps hsum n, hps, hpd, hsum, sq_nonneg (E1 pd ps n)]

/-- **Relative second moment bound, Case 3.** Assuming the mean monotonicity `hmono`, for
`1/2 < pd < 1` one has `E[R²_n] ≤ ((2−pd)/(2pd−1))·E[R_n]²` for every `n ≥ 1`. -/
lemma E2_ratio_case3 (hmono : ∀ k, E1 pd ps k ≤ E1 pd ps (k + 1))
    (hpd_lo : 1 / 2 < pd) (hpd_hi : pd < 1) (n : ℕ) (hn : 1 ≤ n) :
    E2 pd ps n ≤ ((2 - pd) / (2 * pd - 1)) * (E1 pd ps n) ^ 2 := by
  have hden : 0 < 2 * pd - 1 := by linarith
  have hps1 : ps = 1 - pd := by linarith
  have hc_nonneg : 0 ≤ (2 - pd) / (2 * pd - 1) := by
    apply div_nonneg <;> linarith
  induction n, hn using Nat.le_induction with
  | base =>
    rw [E1_one hpd hps hsum, E2_one hpd hps hsum, hps1, div_mul_eq_mul_div, le_div_iff₀ hden]
    nlinarith [hpd_hi, hpd_lo]
  | succ n hn ih =>
    have hcoarse := coarse_E2 hpd hps hsum n
    have hmn := hmono n
    have hE1 : 1 ≤ E1 pd ps n := E1_ge_one hpd hps hsum n
    have hE1' : 1 ≤ E1 pd ps (n + 1) := E1_ge_one hpd hps hsum (n + 1)
    have hfp : 2 * ps * ((2 - pd) / (2 * pd - 1)) + (2 - pd) = (2 - pd) / (2 * pd - 1) := by
      rw [hps1]; field_simp; ring
    have h1 : 2 * ps * E2 pd ps n
        ≤ 2 * ps * (((2 - pd) / (2 * pd - 1)) * (E1 pd ps n) ^ 2) :=
      mul_le_mul_of_nonneg_left ih (by nlinarith [hps])
    have key : E2 pd ps (n + 1) ≤ ((2 - pd) / (2 * pd - 1)) * (E1 pd ps n) ^ 2 := by
      nlinarith [hcoarse, h1, hfp, sq_nonneg (E1 pd ps n)]
    have hmono2 : (E1 pd ps n) ^ 2 ≤ (E1 pd ps (n + 1)) ^ 2 := by nlinarith [hmn, hE1, hE1']
    calc E2 pd ps (n + 1)
        ≤ ((2 - pd) / (2 * pd - 1)) * (E1 pd ps n) ^ 2 := key
      _ ≤ ((2 - pd) / (2 * pd - 1)) * (E1 pd ps (n + 1)) ^ 2 :=
          mul_le_mul_of_nonneg_left hmono2 hc_nonneg

/-- **Affine one–step recursion, Case 3.** For `n ≥ 1`,
`E[R_{n+1}]E[1/R_{n+1}] ≤ (3/2)(1−pd²)·E[R_n]E[1/R_n] + (1+pd)(2pd−1)`. -/
lemma affine_step (hmono : ∀ k, E1 pd ps k ≤ E1 pd ps (k + 1))
    (hpd_lo : 1 / 2 < pd) (hpd_hi : pd < 1) (n : ℕ) (hn : 1 ≤ n) :
    E1 pd ps (n + 1) * Einv pd ps (n + 1)
      ≤ (3 / 2) * (1 - pd ^ 2) * (E1 pd ps n * Einv pd ps n) + (1 + pd) * (2 * pd - 1) := by
  have hP1 : 1 ≤ E1 pd ps n * Einv pd ps n := E1Einv_ge_one hpd hps hsum n
  have hc := E2_ratio_case3 hpd hps hsum hmono hpd_lo hpd_hi n hn
  have hstep := logistic_step hpd hps hsum ((2 - pd) / (2 * pd - 1)) n hc
  exact case3_affine_close pd (E1 pd ps n * Einv pd ps n)
    (E1 pd ps (n + 1) * Einv pd ps (n + 1)) hpd_lo hpd_hi hP1 hstep

/-- **Uniform product–moment bound, Case 3.** -/
lemma uniform_product_case3 (hmono : ∀ k, E1 pd ps k ≤ E1 pd ps (k + 1))
    (hpd_lo : 1 / 2 < pd) (hpd_hi : pd < 1) (hpd2 : 1 / 3 < pd ^ 2) :
    ∃ M : ℝ, ∀ n, E1 pd ps n * Einv pd ps n ≤ M := by
  have hlam_lt : (3 / 2) * (1 - pd ^ 2) < 1 := by nlinarith [hpd2]
  have hlam_nn : 0 ≤ (3 / 2) * (1 - pd ^ 2) := by nlinarith [hpd_hi, hpd_lo]
  have hbeta_nn : 0 ≤ (1 + pd) * (2 * pd - 1) := by
    apply mul_nonneg <;> linarith
  set lam := (3 / 2) * (1 - pd ^ 2) with hlamdef
  set beta := (1 + pd) * (2 * pd - 1) with hbetadef
  refine ⟨max (E1 pd ps 1 * Einv pd ps 1) (beta / (1 - lam)), fun n => ?_⟩
  set M := max (E1 pd ps 1 * Einv pd ps 1) (beta / (1 - lam)) with hMdef
  have hM1 : E1 pd ps 1 * Einv pd ps 1 ≤ M := le_max_left _ _
  have hMinf : beta / (1 - lam) ≤ M := le_max_right _ _
  have hMbound : lam * M + beta ≤ M := by
    have hble : beta ≤ M * (1 - lam) := (div_le_iff₀ (by linarith)).mp hMinf
    nlinarith [hble]
  have hge1 : ∀ m, 1 ≤ m → E1 pd ps m * Einv pd ps m ≤ M := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hM1
    | succ m hm ih =>
      have ha := affine_step hpd hps hsum hmono hpd_lo hpd_hi m hm
      have hle : lam * (E1 pd ps m * Einv pd ps m) ≤ lam * M :=
        mul_le_mul_of_nonneg_left ih hlam_nn
      calc E1 pd ps (m + 1) * Einv pd ps (m + 1)
          ≤ lam * (E1 pd ps m * Einv pd ps m) + beta := ha
        _ ≤ lam * M + beta := by linarith
        _ ≤ M := hMbound
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    have h0 : E1 pd ps 0 * Einv pd ps 0 = 1 := by norm_num [E1, Einv, integral_dirac]
    rw [h0]
    exact le_trans (E1Einv_ge_one hpd hps hsum 1) hM1
  · exact hge1 n h

end Cases

/-- **Paper Lemma 4.5, all regimes combined.** For every parameter with `0 < pd < 1`,
`ps ≥ 0`, `ps + pd = 1` (and, in the regime `pd > 1/√3`, the mean monotonicity `hmono`
coming from the a.s. monotonicity `R_{n+1} ≥ R_n` of the resistance), there is a finite uniform
product–moment bound `E[R_n]·E[1/R_n] ≤ M` for all `n`.  This stitches together Case 1
(`Reduced.uniform_product`, `pd ≤ 1/2`), Case 2 (`uniform_product_case2`,
`1/2 ≤ pd ≤ 1/√3`) and Case 3 (`uniform_product_case3`, `pd > 1/√3`). -/
theorem uniform_product_lemma45 {pd ps : ℝ} (hpd0 : 0 < pd) (hpd1 : pd < 1)
    (hps : 0 ≤ ps) (hsum : ps + pd = 1)
    (hmono : ∀ k, E1 pd ps k ≤ E1 pd ps (k + 1)) :
    ∃ M : ℝ, ∀ n, E1 pd ps n * Einv pd ps n ≤ M := by
  by_cases h : pd ≤ 1 / 2
  · exact uniform_product hpd0.le hps hsum h
  · have h' : 1 / 2 < pd := lt_of_not_ge h
    by_cases h2 : pd ^ 2 ≤ 1 / 3
    · exact uniform_product_case2 hpd0.le hps hsum h'.le h2
    · exact uniform_product_case3 hpd0.le hps hsum hmono h' hpd1 (lt_of_not_ge h2)

end

end Reduced