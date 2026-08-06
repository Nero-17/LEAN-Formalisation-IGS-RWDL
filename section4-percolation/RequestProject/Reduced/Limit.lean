import RequestProject.Reduced.Process

/-!
# The quenched exponent: existence and quenched = annealed

This file formalises the analytic heart of Subsection 4.1:

* `fekete_exponent`: if `m : ℕ → ℝ` is submultiplicative (`m (a+b) ≤ m a * m b`) with
  `1 ≤ m n ≤ 2 ^ n`, then `(log (m n)) / n` converges to a limit `α ∈ [0, log 2]`
  (Lemma "annealed exponent" — existence of `α` via Fekete's lemma).

* `quenched_ae`: for any process `R` on a probability space with `1 ≤ R n ≤ 2 ^ n`,
  uniformly bounded product moments `E[R n] · E[1/R n] ≤ M`, and `(log E[R n])/n → α`
  (equivalently `(E[log R n])/n → α`), the quenched limit `(log R n) / n → α` holds almost
  surely (Theorem "reduced quenched exponent": quenched equals annealed).

These take as inputs the quantities established (for the concrete law `lawMeasure`) by the
moment computations; here they are proved in full generality from Jensen's inequality, Markov's
inequality and the Borel–Cantelli lemma.
-/

namespace Reduced

open MeasureTheory Filter Topology Real Set

/-! ## Fekete's lemma: existence of the exponent -/

/-
Existence of the exponent `α` (Lemma "annealed exponent"). If `m` is submultiplicative with
`1 ≤ m n ≤ 2 ^ n`, then `(log (m n))/n → α` for some `α ∈ [0, log 2]`.
-/
theorem fekete_exponent (m : ℕ → ℝ) (hpos : ∀ n, 1 ≤ m n) (hle : ∀ n, m n ≤ 2 ^ n)
    (hsub : ∀ a b, m (a + b) ≤ m a * m b) :
    ∃ α, α ∈ Set.Icc (0 : ℝ) (Real.log 2) ∧
      Tendsto (fun n => Real.log (m n) / n) atTop (𝓝 α) := by
  obtain ⟨α, hα⟩ : ∃ α, Filter.Tendsto (fun n => Real.log (m n) / n) Filter.atTop (nhds α) := by
    set u : ℕ → ℝ := fun n => Real.log (m n);
    have h_subadd : ∀ a b, u (a + b) ≤ u a + u b := by
      exact fun a b => by rw [ ← Real.log_mul ( by linarith [ hpos a ] ) ( by linarith [ hpos b ] ) ] ; exact Real.log_le_log ( by linarith [ hpos ( a + b ) ] ) ( hsub a b ) ;
    have := @Subadditive.tendsto_lim;
    exact ⟨ _, this ( show Subadditive u from fun a b => h_subadd a b ) ⟨ 0, Set.forall_mem_range.mpr fun n => div_nonneg ( Real.log_nonneg ( hpos n ) ) ( Nat.cast_nonneg n ) ⟩ ⟩;
  refine' ⟨ α, _, hα ⟩;
  constructor;
  · exact le_of_tendsto_of_tendsto' tendsto_const_nhds hα fun n => div_nonneg ( Real.log_nonneg ( hpos n ) ) ( Nat.cast_nonneg n );
  · refine' le_of_tendsto hα ( Filter.eventually_atTop.mpr ⟨ 1, fun n hn => _ ⟩ );
    rw [ div_le_iff₀ ( by positivity ) ];
    simpa [ mul_comm ] using Real.log_le_log ( by linarith [ hpos n ] ) ( hle n )

/-
A real sequence `c n / n` tends to `0` if for every `k ≥ 1`, eventually `|c n| < n / k`.
-/
lemma tendsto_div_zero_of_eventually {c : ℕ → ℝ}
    (h : ∀ k : ℕ, 1 ≤ k → ∀ᶠ n in atTop, |c n| < (n : ℝ) / k) :
    Tendsto (fun n => c n / (n : ℝ)) atTop (𝓝 0) := by
  rw [ Metric.tendsto_nhds ];
  intro ε hε; rcases exists_nat_one_div_lt hε with ⟨ k, hk ⟩ ; rcases Filter.eventually_atTop.mp ( h ( k + 1 ) ( by linarith ) ) with ⟨ N, hN ⟩ ; refine Filter.eventually_atTop.mpr ⟨ N + 1, fun n hn ↦ ?_ ⟩ ; specialize hN n ( by linarith ) ; simp_all +decide [ abs_div ];
  exact lt_of_le_of_lt ( div_le_iff₀' ( Nat.cast_pos.mpr <| by linarith ) |>.2 <| by ring_nf at *; linarith ) hk

/-! ## The quenched = annealed almost sure convergence -/

section Quenched

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (R : ℕ → Ω → ℝ)

/-- The mean log of `R n`. -/
noncomputable def meanLog (n : ℕ) : ℝ := ∫ ω, Real.log (R n ω) ∂P

variable (hmeas : ∀ n, Measurable (R n)) (hge : ∀ n ω, 1 ≤ R n ω) (hle : ∀ n ω, R n ω ≤ 2 ^ n)

include hmeas hge hle

lemma integrable_R (n : ℕ) : Integrable (R n) P := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  exacts [ fun _ => 2 ^ n, by norm_num, ( hmeas n |> Measurable.aestronglyMeasurable ), Filter.Eventually.of_forall fun ω => by rw [ Real.norm_of_nonneg ( by linarith [ hge n ω ] ) ] ; exact hle n ω ]

lemma integrable_inv (n : ℕ) : Integrable (fun ω => (R n ω)⁻¹) P := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  exacts [ fun _ => 1, MeasureTheory.integrable_const _, ( hmeas n |> Measurable.inv |> Measurable.aestronglyMeasurable ), Filter.Eventually.of_forall fun ω => by rw [ Real.norm_of_nonneg ( inv_nonneg.2 ( by linarith [ hge n ω ] ) ) ] ; exact inv_le_one_of_one_le₀ ( by linarith [ hge n ω ] ) ]

lemma integrable_log (n : ℕ) : Integrable (fun ω => Real.log (R n ω)) P := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun ω => Real.log ( 2 ^ n );
  · fun_prop;
  · exact Measurable.aestronglyMeasurable ( by measurability );
  · filter_upwards [ ] with ω using by rw [ Real.norm_of_nonneg ( Real.log_nonneg ( hge n ω ) ) ] ; exact Real.log_le_log ( by linarith [ hge n ω ] ) ( hle n ω ) ;

/-
Jensen (upper): `exp (E[log R n]) ≤ E[R n]`.
-/
lemma exp_meanLog_le (n : ℕ) : Real.exp (meanLog P R n) ≤ ∫ ω, R n ω ∂P := by
  have h_jensen : ConvexOn ℝ (Set.univ : Set ℝ) Real.exp := by
    exact convexOn_exp;
  convert ConvexOn.map_integral_le h_jensen _ _ _;
  any_goals exact isClosed_univ;
  any_goals exact Real.continuousOn_exp;
  any_goals exact P;
  any_goals exact fun ω => Real.log ( R n ω );
  · simp +decide [ Real.exp_log ( zero_lt_one.trans_le ( hge n _ ) ) ];
    exact ⟨ fun h => fun _ _ => h, fun h => h ( integrable_log P R hmeas hge hle n ) ( by simpa only [ Function.comp_def, Real.exp_log ( zero_lt_one.trans_le ( hge n _ ) ) ] using integrable_R P R hmeas hge hle n ) ⟩;
  · infer_instance;
  · exact Filter.Eventually.of_forall fun ω => Set.mem_univ _

/-
Jensen (lower): `exp (- E[log R n]) ≤ E[1/R n]`.
-/
lemma exp_neg_meanLog_le (n : ℕ) :
    Real.exp (-(meanLog P R n)) ≤ ∫ ω, (R n ω)⁻¹ ∂P := by
  have h_jensen_lower : Real.exp (∫ ω, -(Real.log (R n ω)) ∂P) ≤ ∫ ω, Real.exp (-(Real.log (R n ω))) ∂P := by
    have h_jensen_lower : ConvexOn ℝ (Set.univ : Set ℝ) Real.exp := by
      exact convexOn_exp;
    apply_rules [ h_jensen_lower.map_integral_le ];
    · exact Real.continuousOn_exp;
    · exact isClosed_univ;
    · exact Filter.Eventually.of_forall fun ω => Set.mem_univ _;
    · exact MeasureTheory.Integrable.neg ( Reduced.integrable_log P R hmeas hge hle n );
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun ω => 1;
      · norm_num;
      · exact Measurable.aestronglyMeasurable ( by measurability );
      · filter_upwards [ ] with ω using by simpa using Real.exp_le_one_iff.mpr ( neg_nonpos.mpr ( Real.log_nonneg ( hge n ω ) ) ) ;
  convert h_jensen_lower using 1;
  · rw [ MeasureTheory.integral_neg, meanLog ];
  · exact congr_arg _ ( funext fun ω => by rw [ Real.exp_neg, Real.exp_log ( by linarith [ hge n ω ] ) ] )

variable (M : ℝ) (hM : ∀ n, (∫ ω, R n ω ∂P) * (∫ ω, (R n ω)⁻¹ ∂P) ≤ M)

include hM

/-
One-sided exponential moment bound: `E[exp(log R n − E[log R n])] ≤ M`.
-/
lemma exp_moment_up (n : ℕ) :
    (∫ ω, Real.exp (Real.log (R n ω) - meanLog P R n) ∂P) ≤ M := by
  refine' le_trans _ ( hM n );
  -- Using the properties of exponents, we can rewrite the integral as:
  have h_exp : ∫ ω, Real.exp (Real.log (R n ω) - meanLog P R n) ∂P = Real.exp (-meanLog P R n) * ∫ ω, R n ω ∂P := by
    rw [ ← MeasureTheory.integral_const_mul ] ; congr ; ext ω ; rw [ Real.exp_sub, Real.exp_log ( by linarith [ hge n ω ] ) ] ; ring;
    rw [ Real.exp_neg ];
  convert mul_le_mul_of_nonneg_left ( exp_neg_meanLog_le P R hmeas hge hle n ) ( MeasureTheory.integral_nonneg fun ω => le_trans zero_le_one ( hge n ω ) ) using 1 ; ring;
  rw [ h_exp, mul_comm ]

/-
One-sided exponential moment bound: `E[exp(−(log R n − E[log R n]))] ≤ M`.
-/
lemma exp_moment_dn (n : ℕ) :
    (∫ ω, Real.exp (-(Real.log (R n ω) - meanLog P R n)) ∂P) ≤ M := by
  have h_exp_neg_log : ∫ ω, Real.exp (-(Real.log (R n ω) - meanLog P R n)) ∂P = (∫ ω, (R n ω)⁻¹ ∂P) * Real.exp (meanLog P R n) := by
    rw [ ← MeasureTheory.integral_mul_const ];
    simp +decide [ Real.exp_sub, Real.exp_neg, Real.exp_log ( zero_lt_one.trans_le ( hge n _ ) ) ];
    simp +decide only [div_eq_mul_inv, mul_comm];
  refine' le_trans _ ( hM n );
  convert mul_le_mul_of_nonneg_left ( exp_meanLog_le P R hmeas hge hle n ) ( show ( 0 : ℝ ) ≤ ∫ ω, ( R n ω ) ⁻¹ ∂P from MeasureTheory.integral_nonneg fun ω => inv_nonneg.2 ( by linarith [ hge n ω ] ) ) using 1 ; ring

/-
Two-sided concentration tail bound via Markov.
-/
lemma tail_bound (n : ℕ) {t : ℝ} (ht : 0 < t) :
    P.real {ω | t ≤ |Real.log (R n ω) - meanLog P R n|} ≤ 2 * M * Real.exp (-t) := by
  -- Apply the one-sided exponential moment bounds and Markov's inequality to get the bounds on each term.
  have h_bound1 : P.real {ω | t ≤ Real.log (R n ω) - meanLog P R n} ≤ M * Real.exp (-t) := by
    have h_markov : P.real {ω | Real.exp t ≤ Real.exp (Real.log (R n ω) - meanLog P R n)} ≤ (∫ ω, Real.exp (Real.log (R n ω) - meanLog P R n) ∂P) / Real.exp t := by
      rw [ le_div_iff₀ ( Real.exp_pos _ ) ];
      convert mul_meas_ge_le_integral_of_nonneg _ _ _ using 1;
      rw [ mul_comm ];
      · exact Filter.Eventually.of_forall fun ω => Real.exp_nonneg _;
      · simp +decide only [exp_sub, Real.exp_log (zero_lt_one.trans_le (hge n _))];
        exact MeasureTheory.Integrable.div_const ( integrable_R P R hmeas hge hle n ) _;
    simp_all +decide [ Real.exp_le_exp, Real.exp_neg ];
    exact h_markov.trans ( mul_le_mul_of_nonneg_right ( exp_moment_up P R hmeas hge hle M hM n ) ( by positivity ) )
  have h_bound2 : P.real {ω | t ≤ -(Real.log (R n ω) - meanLog P R n)} ≤ M * Real.exp (-t) := by
    have := @mul_meas_ge_le_integral_of_nonneg;
    specialize this ( show 0 ≤ᶠ[ae P] fun ω => Real.exp ( - ( Real.log ( R n ω ) - meanLog P R n ) ) from Filter.Eventually.of_forall fun ω => Real.exp_nonneg _ ) ( show Integrable ( fun ω => Real.exp ( - ( Real.log ( R n ω ) - meanLog P R n ) ) ) P from ?_ ) ( Real.exp t );
    · convert integrable_inv P R hmeas hge hle n |> fun h => h.mul_const ( Real.exp ( meanLog P R n ) ) using 1 ; ext ; simp +decide [ Real.exp_add, Real.exp_sub, Real.exp_neg, Real.exp_log ( zero_lt_one.trans_le ( hge n _ ) ) ] ; ring;
    · convert mul_le_mul_of_nonneg_right ( this.trans ( exp_moment_dn P R hmeas hge hle M hM n ) ) ( inv_nonneg.2 ( Real.exp_nonneg t ) ) using 1;
      · simp +decide [ Real.exp_le_exp, mul_comm, ne_of_gt ( Real.exp_pos t ) ];
      · rw [ Real.exp_neg ];
  convert le_trans _ ( add_le_add h_bound1 h_bound2 ) using 1;
  · ring;
  · convert MeasureTheory.measureReal_union_le _ _ using 2;
    ext ω; simp [abs_eq_max_neg]

/-
Borel–Cantelli step: for each `k ≥ 1`, almost surely eventually `|log R n − E[log R n]| < n/k`.
-/
lemma ae_eventually_lt (k : ℕ) (hk : 1 ≤ k) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      |Real.log (R n ω) - meanLog P R n| < (n : ℝ) / k := by
  -- Let `s : ℕ → Set Ω` be the set of events where `|log R n − E[log R n]| ≥ n / k`.
  set s : ℕ → Set Ω := fun n => {ω | (n : ℝ) / k ≤ |Real.log (R n ω) - meanLog P R n|};
  -- By the Borel-Cantelli lemma, since $\sum_{n=1}^{\infty} P(s_n) < \infty$, we have $P(\limsup_{n \to \infty} s_n) = 0$.
  have h_borel_cantelli : P (Filter.limsup s Filter.atTop) = 0 := by
    have h_sum_finite : Summable (fun n => ENNReal.toReal (P (s n))) := by
      -- By the tail bound, we have $P(s_n) \leq 2M \exp(-(n/k))$.
      have h_tail_bound : ∀ n ≥ 1, (P (s n)).toReal ≤ 2 * M * Real.exp (-(n : ℝ) / k) := by
        intro n hn;
        convert tail_bound P R hmeas hge hle M hM n ( show 0 < ( n : ℝ ) / k by positivity ) using 1;
        ring;
      -- The series $\sum_{n=1}^{\infty} 2M \exp(-(n/k))$ is a geometric series with common ratio $e^{-1/k}$.
      have h_geo_series : Summable (fun n : ℕ => 2 * M * Real.exp (-(n : ℝ) / k)) := by
        have h_geo_series : Summable (fun n : ℕ => (Real.exp (-1 / k)) ^ n) := by
          exact summable_geometric_of_lt_one ( by positivity ) ( by rw [ Real.exp_lt_one_iff ] ; exact div_neg_of_neg_of_pos ( by norm_num ) ( by positivity ) );
        convert h_geo_series.mul_left ( 2 * M ) using 2 ; rw [ ← Real.exp_nat_mul ] ; ring;
      rw [ ← summable_nat_add_iff 1 ] at *;
      exact Summable.of_nonneg_of_le ( fun n => ENNReal.toReal_nonneg ) ( fun n => h_tail_bound _ le_add_self ) h_geo_series;
    apply_rules [ MeasureTheory.measure_limsup_atTop_eq_zero ];
    refine' ne_of_lt ( lt_of_le_of_lt ( ENNReal.tsum_le_tsum fun n => _ ) _ );
    use fun n => ENNReal.ofReal ( ENNReal.toReal ( P ( s n ) ) );
    · rw [ ENNReal.ofReal_toReal ];
      exact MeasureTheory.measure_ne_top _ _;
    · rw [ ← ENNReal.ofReal_tsum_of_nonneg ] <;> norm_num [ h_sum_finite ];
  filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h_borel_cantelli ] with ω hω;
  simp_all +decide [ Filter.limsup_eq_iInf_iSup_of_nat ];
  exact ⟨ hω.choose, fun n hn => lt_of_not_ge fun h => hω.choose_spec n hn h ⟩

/-
**Theorem (reduced quenched exponent), almost-sure part.**  If the annealed log-means
`(meanLog P R n)/n` converge to `α`, then quenched `(log (R n ω))/n → α` for a.e. `ω`.
-/
theorem quenched_ae {α : ℝ}
    (hannealed : Tendsto (fun n => meanLog P R n / n) atTop (𝓝 α)) :
    ∀ᵐ ω ∂P, Tendsto (fun n => Real.log (R n ω) / n) atTop (𝓝 α) := by
  -- By `MeasureTheory.ae_all_iff`, we can combine the per-k Borel–Cantelli facts.
  have hae : ∀ᵐ ω ∂P, ∀ k : ℕ, 1 ≤ k → ∀ᶠ n in atTop, |Real.log (R n ω) - meanLog P R n| < (n : ℝ) / k := by
    filter_upwards [ MeasureTheory.ae_all_iff.2 fun k : ℕ => MeasureTheory.ae_all_iff.2 fun hk : 1 ≤ k => ae_eventually_lt P R ( hmeas ) hge hle M hM k hk ] with ω hω using hω;
  filter_upwards [ hae ] with ω hω;
  convert hannealed.add ( tendsto_div_zero_of_eventually ( fun k hk => ?_ ) ) using 2 <;> norm_num;
  rw [ ← add_div ];
  rw [ add_sub_cancel ];
  exact Filter.eventually_atTop.mp ( hω k hk )

/-! ### Mean bounds and the quenched = annealed capstone -/

omit hM in
lemma one_le_mean (n : ℕ) : 1 ≤ ∫ ω, R n ω ∂P := by
  exact le_trans ( by norm_num ) ( MeasureTheory.integral_mono ( by norm_num ) ( by exact Reduced.integrable_R P R hmeas hge hle n ) fun ω => hge n ω )

omit hmeas hM in
lemma mean_le_pow (n : ℕ) : (∫ ω, R n ω ∂P) ≤ 2 ^ n := by
  refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
  exacts [ fun _ => 2 ^ n, Filter.Eventually.of_forall fun _ => le_trans zero_le_one ( hge _ _ ), MeasureTheory.integrable_const _, Filter.Eventually.of_forall fun _ => hle _ _, by simp +decide [ MeasureTheory.integral_const ] ]

omit hM in
lemma meanLog_le_log_mean (n : ℕ) : meanLog P R n ≤ Real.log (∫ ω, R n ω ∂P) := by
  have h_exp_log_le : Real.exp (meanLog P R n) ≤ ∫ ω, R n ω ∂P :=
    exp_meanLog_le P R hmeas hge hle n
  simpa using Real.log_le_log ( by positivity ) h_exp_log_le

lemma log_mean_sub_meanLog_le (n : ℕ) :
    Real.log (∫ ω, R n ω ∂P) - meanLog P R n ≤ Real.log M := by
  have hRpos : (0 : ℝ) < ∫ ω, R n ω ∂P :=
    lt_of_lt_of_le zero_lt_one (one_le_mean P R hmeas hge hle n)
  have hInvpos : (0 : ℝ) < ∫ ω, (R n ω)⁻¹ ∂P := by
    have hge' : ∀ ω, ((2 : ℝ) ^ n)⁻¹ ≤ (R n ω)⁻¹ :=
      fun ω => inv_anti₀ (lt_of_lt_of_le zero_lt_one (hge n ω)) (hle n ω)
    have hmono := MeasureTheory.integral_mono (μ := P) (f := fun _ : Ω => ((2 : ℝ) ^ n)⁻¹)
      (g := fun ω => (R n ω)⁻¹) (MeasureTheory.integrable_const _)
      (integrable_inv P R hmeas hge hle n) hge'
    have hc : ∫ _ : Ω, ((2 : ℝ) ^ n)⁻¹ ∂P = ((2 : ℝ) ^ n)⁻¹ := by simp
    rw [hc] at hmono
    exact lt_of_lt_of_le (by positivity) hmono
  have hneg : -meanLog P R n ≤ Real.log (∫ ω, (R n ω)⁻¹ ∂P) := by
    have h1 := Real.log_le_log (Real.exp_pos _) (exp_neg_meanLog_le P R hmeas hge hle n)
    simpa [Real.log_exp] using h1
  calc Real.log (∫ ω, R n ω ∂P) - meanLog P R n
      ≤ Real.log (∫ ω, R n ω ∂P) + Real.log (∫ ω, (R n ω)⁻¹ ∂P) := by linarith
    _ = Real.log ((∫ ω, R n ω ∂P) * (∫ ω, (R n ω)⁻¹ ∂P)) :=
        (Real.log_mul (ne_of_gt hRpos) (ne_of_gt hInvpos)).symm
    _ ≤ Real.log M := Real.log_le_log (by positivity) (hM n)

/-
**Theorem (reduced quenched exponent).** For a process `R` with `1 ≤ R n ≤ 2^n`, uniformly
bounded product moments (`hM`), and submultiplicative means (`hsub`, the self-similarity input),
the quenched limit `(log R n)/n` converges almost surely to a deterministic constant
`α ∈ [0, log 2]`, which also equals the annealed exponents `(log E[R n])/n` and `(E[log R n])/n`.
Thus the quenched and annealed unit-resistance exponents coincide.
-/
theorem reduced_quenched_exponent
    (hsub : ∀ a b, (∫ ω, R (a + b) ω ∂P) ≤ (∫ ω, R a ω ∂P) * (∫ ω, R b ω ∂P)) :
    ∃ α, α ∈ Set.Icc (0 : ℝ) (Real.log 2) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => Real.log (R n ω) / n) atTop (𝓝 α)) ∧
      Tendsto (fun n => Real.log (∫ ω, R n ω ∂P) / n) atTop (𝓝 α) ∧
      Tendsto (fun n => meanLog P R n / n) atTop (𝓝 α) := by
  obtain ⟨α, hαmem, hαlog⟩ : ∃ α ∈ Set.Icc 0 (Real.log 2), Tendsto (fun n => Real.log (∫ ω, R n ω ∂P) / n) atTop (𝓝 α) := by
    apply fekete_exponent (fun n => ∫ ω, R n ω ∂P) (one_le_mean P R hmeas hge hle) (mean_le_pow P R hge hle) hsub;
  refine' ⟨ α, hαmem, _, hαlog, _ ⟩;
  · apply quenched_ae P R hmeas hge hle M hM;
    have h_squeeze : Filter.Tendsto (fun n => (Real.log (∫ ω, R n ω ∂P) - meanLog P R n) / n) Filter.atTop (nhds 0) := by
      have h_g_div_n_zero : ∀ n, 0 ≤ Real.log (∫ ω, R n ω ∂P) - meanLog P R n ∧ Real.log (∫ ω, R n ω ∂P) - meanLog P R n ≤ Real.log M := by
        exact fun n => ⟨ sub_nonneg_of_le ( meanLog_le_log_mean P R hmeas hge hle n ), log_mean_sub_meanLog_le P R hmeas hge hle M hM n ⟩;
      exact squeeze_zero ( fun n => div_nonneg ( h_g_div_n_zero n |>.1 ) ( Nat.cast_nonneg n ) ) ( fun n => div_le_div_of_nonneg_right ( h_g_div_n_zero n |>.2 ) ( Nat.cast_nonneg n ) ) ( tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop );
    convert hαlog.sub h_squeeze using 2 <;> ring;
  · -- By the properties of logarithms and limits, we can rewrite the limit expression.
    have h_log_limit : Filter.Tendsto (fun n => (Real.log (∫ ω, R n ω ∂P) - meanLog P R n) / (n : ℝ)) Filter.atTop (nhds 0) := by
      have h_g_div_n_zero : ∀ n, 0 ≤ Real.log (∫ ω, R n ω ∂P) - meanLog P R n ∧ Real.log (∫ ω, R n ω ∂P) - meanLog P R n ≤ Real.log M := by
        exact fun n => ⟨ sub_nonneg_of_le ( meanLog_le_log_mean P R hmeas hge hle n ), log_mean_sub_meanLog_le P R hmeas hge hle M hM n ⟩;
      exact squeeze_zero ( fun n => div_nonneg ( h_g_div_n_zero n |>.1 ) ( Nat.cast_nonneg n ) ) ( fun n => div_le_div_of_nonneg_right ( h_g_div_n_zero n |>.2 ) ( Nat.cast_nonneg n ) ) ( tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop );
    convert hαlog.sub h_log_limit using 2 <;> ring

end Quenched

end Reduced