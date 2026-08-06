import RequestProject.Reduced.Process

/-!
# Moment computations for the reduced resistance process

This file verifies, for the concrete law `lawMeasure`, the *uniform product–moment bound*
(paper Lemma 4.5): there is a constant `M` with `E[R n] · E[1/R n] ≤ M` for all `n ≥ 1`,
in the regime `pdiamond ≤ 1/2` (which contains the critical parameter `p_c`, where
`pdiamond = √5 − 2 < 1/2`).

The development follows the paper:

* one-step integral identities for the law `lawMeasure pd ps (n+1)` in terms of `lawMeasure pd ps n`;
* the moment recursions for `E[R]`, `E[1/R]`, `E[R²]`;
* the relative-second-moment bound `E[R²]/E[R]² ≤ 2` (Lemma 4.5, Case 1);
* the one-step product-moment estimate (Lemma 4.4) and the resulting uniform bound `11/5`.
-/

namespace Reduced

open MeasureTheory Measure Real Set

noncomputable section

variable {pd ps : ℝ}

/-- `E[R n]`. -/
noncomputable def E1 (pd ps : ℝ) (n : ℕ) : ℝ := ∫ x, x ∂(lawMeasure pd ps n)
/-- `E[1/R n]`. -/
noncomputable def Einv (pd ps : ℝ) (n : ℕ) : ℝ := ∫ x, x⁻¹ ∂(lawMeasure pd ps n)
/-- `E[R n ^ 2]`. -/
noncomputable def E2 (pd ps : ℝ) (n : ℕ) : ℝ := ∫ x, x ^ 2 ∂(lawMeasure pd ps n)

/-- The pushforward of `prod4 μ` onto its first two coordinates is `μ × μ`. -/
lemma prod4_map12 (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (prod4 μ).map (fun q : ℝ × ℝ × ℝ × ℝ => (q.1, q.2.1)) = μ.prod μ := by
  unfold prod4
  rw [show (fun q : ℝ × ℝ × ℝ × ℝ => (q.1, q.2.1))
      = Prod.map (id : ℝ → ℝ) (Prod.fst : ℝ × ℝ × ℝ → ℝ) from rfl]
  rw [← Measure.map_prod_map _ _ measurable_id measurable_fst, Measure.map_id]
  congr 1
  exact Measure.fst_prod

/-- The pushforward of `prod4 μ` onto its last two coordinates is `μ × μ`. -/
lemma prod4_map34 (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (prod4 μ).map (fun q : ℝ × ℝ × ℝ × ℝ => (q.2.2.1, q.2.2.2)) = μ.prod μ := by
  unfold prod4
  rw [show (fun q : ℝ × ℝ × ℝ × ℝ => (q.2.2.1, q.2.2.2)) = Prod.snd ∘ Prod.snd from rfl]
  rw [← Measure.map_map measurable_snd measurable_snd]
  rw [show (μ.prod (μ.prod (μ.prod μ))).map Prod.snd = (μ.prod (μ.prod (μ.prod μ))).snd from rfl]
  rw [Measure.snd_prod]
  rw [show (μ.prod (μ.prod μ)).map Prod.snd = (μ.prod (μ.prod μ)).snd from rfl]
  rw [Measure.snd_prod]

section Foundation

variable (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1)

include hpd hps hsum

/-- Each law is a probability measure (restated for convenience). -/
lemma prob_law (n : ℕ) : IsProbabilityMeasure (lawMeasure pd ps n) :=
  isProb_lawMeasure hpd hps hsum n

/-
A measurable function bounded on the support `[1, 2^n]` is integrable w.r.t. `law n`.
-/
lemma integrable_law (n : ℕ) (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ)
    (hC : ∀ x ∈ Set.Icc (1 : ℝ) (2 ^ n), |g x| ≤ C) :
    Integrable g (lawMeasure pd ps n) := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun x => C;
  · convert MeasureTheory.integrable_const C;
    exact ⟨ by have := prob_law hpd hps hsum n; aesop ⟩;
  · exact hg.aestronglyMeasurable;
  · filter_upwards [ lawMeasure_support hpd hps hsum n ] with x hx using hC x hx

/-
A measurable function bounded on the box `[1,2^n]²` is integrable w.r.t. `law n × law n`.
-/
lemma integrable_prod_law (n : ℕ) (g : ℝ × ℝ → ℝ) (hg : Measurable g) (C : ℝ)
    (hC : ∀ q : ℝ × ℝ, q.1 ∈ Set.Icc (1 : ℝ) (2 ^ n) → q.2 ∈ Set.Icc (1 : ℝ) (2 ^ n) →
      |g q| ≤ C) :
    Integrable g ((lawMeasure pd ps n).prod (lawMeasure pd ps n)) := by
  have h_prod_support : ∀ᵐ q ∂(lawMeasure pd ps n).prod (lawMeasure pd ps n), q.1 ∈ Set.Icc (1 : ℝ) (2 ^ n) ∧ q.2 ∈ Set.Icc (1 : ℝ) (2 ^ n) := by
    apply_rules [ ae_prod_box, lawMeasure_support ];
    · exact measurableSet_Icc;
    · exact measurableSet_Icc;
    · have := prob_law hpd hps hsum n;
      infer_instance;
    · have := prob_law hpd hps hsum n;
      infer_instance;
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun q => C;
  · have := prob_law hpd hps hsum n;
    exact MeasureTheory.integrable_const _;
  · exact hg.aestronglyMeasurable;
  · filter_upwards [ h_prod_support ] with q hq using hC q hq.1 hq.2

/-
A measurable function bounded on the box `[1,2^n]⁴` is integrable w.r.t. `prod4 (law n)`.
-/
lemma integrable_prod4_law (n : ℕ) (g : ℝ × ℝ × ℝ × ℝ → ℝ) (hg : Measurable g) (C : ℝ)
    (hC : ∀ q : ℝ × ℝ × ℝ × ℝ, q.1 ∈ Set.Icc (1 : ℝ) (2 ^ n) → q.2.1 ∈ Set.Icc (1 : ℝ) (2 ^ n) →
      q.2.2.1 ∈ Set.Icc (1 : ℝ) (2 ^ n) → q.2.2.2 ∈ Set.Icc (1 : ℝ) (2 ^ n) → |g q| ≤ C) :
    Integrable g (prod4 (lawMeasure pd ps n)) := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun q => C + |g q| * ( 0 : ℝ ) + ( 0 : ℝ );
  · simp +decide [ prod4 ];
    have := prob_law hpd hps hsum n;
    fun_prop;
  · exact hg.aestronglyMeasurable;
  · have h_prob : IsProbabilityMeasure (lawMeasure pd ps n) := prob_law hpd hps hsum n
    filter_upwards [ ae_prod4_box ( measurableSet_Icc ) ( lawMeasure_support hpd hps hsum n ) ] with q hq using by simpa using hC q hq.1 hq.2.1 hq.2.2.1 hq.2.2.2;

/-
One-step integral identity: integrating against `law (n+1)` splits into the series and
diamond contributions, weighted by `ps` and `pd`.
-/
lemma integral_succ (n : ℕ) (g : ℝ → ℝ) (hg : Measurable g)
    (hs : Integrable (fun q : ℝ × ℝ => g (q.1 + q.2))
        ((lawMeasure pd ps n).prod (lawMeasure pd ps n)))
    (hd : Integrable (fun q : ℝ × ℝ × ℝ × ℝ => g (diamondMap q)) (prod4 (lawMeasure pd ps n))) :
    ∫ x, g x ∂(lawMeasure pd ps (n + 1)) =
      ps * (∫ q : ℝ × ℝ, g (q.1 + q.2) ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n)))
      + pd * (∫ q : ℝ × ℝ × ℝ × ℝ, g (diamondMap q) ∂(prod4 (lawMeasure pd ps n))) := by
  rw [ lawMeasure_succ, MeasureTheory.integral_add_measure ];
  · congr! 1;
    · rw [ MeasureTheory.integral_smul_measure ];
      rw [ ENNReal.toReal_ofReal hps, MeasureTheory.integral_map ];
      · rfl;
      · exact measurable_seriesMap.aemeasurable;
      · exact hg.aestronglyMeasurable;
    · convert MeasureTheory.integral_smul_measure _ _ using 1;
      rw [ MeasureTheory.integral_map ];
      · rw [ ENNReal.toReal_ofReal hpd ] ; norm_num;
      · exact measurable_diamondMap.aemeasurable;
      · exact hg.aestronglyMeasurable;
  · refine' MeasureTheory.Integrable.smul_measure _ _;
    · rwa [ MeasureTheory.integrable_map_measure ];
      · exact hg.aestronglyMeasurable;
      · exact measurable_seriesMap.aemeasurable;
    · norm_num;
  · refine' MeasureTheory.Integrable.smul_measure _ _;
    · rwa [ MeasureTheory.integrable_map_measure ];
      · exact hg.aestronglyMeasurable;
      · exact measurable_diamondMap.aemeasurable;
    · norm_num

/-- A.e. box membership for the 2-fold product law (instances resolved). -/
lemma ae_box_prod (n : ℕ) :
    ∀ᵐ q ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n)),
      q.1 ∈ Set.Icc (1 : ℝ) (2 ^ n) ∧ q.2 ∈ Set.Icc (1 : ℝ) (2 ^ n) := by
  haveI := prob_law hpd hps hsum n
  exact ae_prod_box measurableSet_Icc measurableSet_Icc
    (lawMeasure_support hpd hps hsum n) (lawMeasure_support hpd hps hsum n)

/-- A.e. box membership for the 4-fold product law (instances resolved). -/
lemma ae_box_prod4 (n : ℕ) :
    ∀ᵐ q ∂(prod4 (lawMeasure pd ps n)),
      q.1 ∈ Set.Icc (1 : ℝ) (2 ^ n) ∧ q.2.1 ∈ Set.Icc (1 : ℝ) (2 ^ n) ∧
        q.2.2.1 ∈ Set.Icc (1 : ℝ) (2 ^ n) ∧ q.2.2.2 ∈ Set.Icc (1 : ℝ) (2 ^ n) := by
  haveI := prob_law hpd hps hsum n
  exact ae_prod4_box measurableSet_Icc (lawMeasure_support hpd hps hsum n)

end Foundation

/-! ## Intermediate one-step quantities -/

/-- `E[ par(X₁+X₂, X₃+X₄) ]` (the diamond mean). -/
noncomputable def Dmean (pd ps : ℝ) (n : ℕ) : ℝ :=
  ∫ q : ℝ × ℝ × ℝ × ℝ, diamondMap q ∂(prod4 (lawMeasure pd ps n))
/-- `E[ par(X₁+X₂, X₃+X₄)² ]`. -/
noncomputable def Dsq (pd ps : ℝ) (n : ℕ) : ℝ :=
  ∫ q : ℝ × ℝ × ℝ × ℝ, (diamondMap q) ^ 2 ∂(prod4 (lawMeasure pd ps n))
/-- `E[ 1/(X+Y) ]` for independent copies `X, Y`. -/
noncomputable def Sinv (pd ps : ℝ) (n : ℕ) : ℝ :=
  ∫ q : ℝ × ℝ, (q.1 + q.2)⁻¹ ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n))
/-- `Δ_n = E[(X-Y)²/(XY(X+Y))]`. -/
noncomputable def Delta (pd ps : ℝ) (n : ℕ) : ℝ :=
  ∫ q : ℝ × ℝ, (q.1 - q.2) ^ 2 / (q.1 * q.2 * (q.1 + q.2))
    ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n))
/-- `E[W]` where `W = (X-Y)²/(XY)`. -/
noncomputable def Wmean (pd ps : ℝ) (n : ℕ) : ℝ :=
  ∫ q : ℝ × ℝ, (q.1 - q.2) ^ 2 / (q.1 * q.2) ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n))
/-- `E[W·(X+Y)]`. -/
noncomputable def WSmean (pd ps : ℝ) (n : ℕ) : ℝ :=
  ∫ q : ℝ × ℝ, (q.1 - q.2) ^ 2 * (q.1 + q.2) / (q.1 * q.2)
    ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n))

section Recursions

variable (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1)

include hpd hps hsum

/-! ### Basic positivity and bounds -/

lemma E1_ge_one (n : ℕ) : 1 ≤ E1 pd ps n := by
  refine' le_trans _ ( MeasureTheory.integral_mono_of_nonneg _ _ _ );
  case refine'_2 => exact fun _ => 1;
  · norm_num [ prob_law hpd hps hsum n ];
  · exact Filter.Eventually.of_forall fun x => zero_le_one;
  · apply integrable_law;
    exacts [ hpd, hps, hsum, measurable_id, fun x hx => by rw [ abs_of_nonneg ( by linarith [ hx.1 ] ) ] ; exact hx.2 ];
  · filter_upwards [ lawMeasure_support hpd hps hsum n ] with x hx using hx.1

lemma Einv_pos (n : ℕ) : 0 < Einv pd ps n := by
  refine' ( lt_of_lt_of_le _ ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) );
  case refine'_2 => exact fun x => 1 / 2 ^ n;
  · norm_num [ isProb_lawMeasure hpd hps hsum ];
  · exact Filter.Eventually.of_forall fun x => by positivity;
  · apply integrable_law;
    exacts [ hpd, hps, hsum, measurable_id.inv, fun x hx => by rw [ abs_of_nonneg ( inv_nonneg.2 ( by linarith [ hx.1 ] ) ) ] ; exact inv_le_one_of_one_le₀ ( by linarith [ hx.1 ] ) ];
  · filter_upwards [ lawMeasure_support hpd hps hsum n ] with x hx using by simpa using inv_anti₀ ( by linarith [ hx.1 ] ) hx.2;

lemma Einv_le_one (n : ℕ) : Einv pd ps n ≤ 1 := by
  convert MeasureTheory.integral_mono_ae _ _ _;
  rotate_left;
  all_goals try infer_instance;
  exact fun _ => 1;
  · refine' integrable_law hpd hps hsum n _ _ _ _;
    exacts [ measurable_id.inv, 1, fun x hx => by rw [ abs_of_nonneg ( inv_nonneg.2 ( by linarith [ hx.1 ] ) ) ] ; exact inv_le_one_of_one_le₀ ( by linarith [ hx.1 ] ) ];
  · have := prob_law hpd hps hsum n; exact MeasureTheory.integrable_const _;
  · filter_upwards [ lawMeasure_support hpd hps hsum n ] with x hx using inv_le_one_of_one_le₀ hx.1;
  · norm_num [ prob_law hpd hps hsum n ]

/-! ### Product-integral value helpers -/

/-
`∫ (x+y) ∂(law n × law n) = 2·E[R n]`.
-/
lemma int_prod_sum (n : ℕ) :
    (∫ q : ℝ × ℝ, (q.1 + q.2) ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n)))
      = 2 * E1 pd ps n := by
        rw [ MeasureTheory.integral_add ];
        · have h_integrable : MeasureTheory.Integrable (fun q : ℝ × ℝ => q.1) ((lawMeasure pd ps n).prod (lawMeasure pd ps n)) ∧ MeasureTheory.Integrable (fun q : ℝ × ℝ => q.2) ((lawMeasure pd ps n).prod (lawMeasure pd ps n)) := by
            constructor <;> refine' MeasureTheory.Integrable.mono' _ _ _ <;> norm_num [ integrable_law, integrable_prod_law ];
            any_goals exact fun q => 2 ^ n;
            any_goals exact measurable_fst.aestronglyMeasurable;
            · have := prob_law hpd hps hsum n; aesop;
            · filter_upwards [ ae_box_prod hpd hps hsum n ] with q hq using by rw [ abs_of_nonneg ( by linarith [ hq.1.1 ] ) ] ; exact hq.1.2;
            · have := prob_law hpd hps hsum n; aesop;
            · exact measurable_snd.aestronglyMeasurable;
            · filter_upwards [ ae_box_prod hpd hps hsum n ] with q hq using by rw [ abs_of_nonneg ( by linarith [ hq.2.1 ] ) ] ; exact hq.2.2;
          convert congr_arg₂ ( · + · ) ( MeasureTheory.integral_prod_mul ( fun x => x ) ( fun _ => ( 1 : ℝ ) ) ) ( MeasureTheory.integral_prod_mul ( fun _ => ( 1 : ℝ ) ) ( fun x => x ) ) using 1 <;> norm_num [ E1 ] ; ring;
          · rw [ MeasureTheory.measureReal_def ] ; ring;
            rw [ prob_law hpd hps hsum n |> fun h => h.measure_univ ] ; norm_num;
          · have := prob_law hpd hps hsum n; exact inferInstance;
          · have := prob_law hpd hps hsum n; infer_instance;
          · have := prob_law hpd hps hsum n; exact inferInstance;
          · have := prob_law hpd hps hsum n;
            infer_instance;
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun q => 2 ^ n;
          · have := prob_law hpd hps hsum n; aesop;
          · exact measurable_fst.aestronglyMeasurable;
          · filter_upwards [ ae_box_prod hpd hps hsum n ] with q hq using by rw [ Real.norm_of_nonneg ( by linarith [ hq.1.1 ] ) ] ; exact hq.1.2;
        · have h_integrable : Integrable (fun q : ℝ × ℝ => q.2) ((lawMeasure pd ps n).prod (lawMeasure pd ps n)) := by
            have := integrable_prod_law hpd hps hsum n (fun q : ℝ × ℝ => q.2) (by
            exact measurable_snd) (2^n) (by
            exact fun q hq₁ hq₂ => by rw [ abs_of_nonneg ( by linarith [ hq₂.1 ] ) ] ; exact hq₂.2;)
            exact this;
          exact h_integrable

/-
`∫ (x+y)² ∂(law n × law n) = 2·E[R² n] + 2·E[R n]²`.
-/
lemma int_prod_sum_sq (n : ℕ) :
    (∫ q : ℝ × ℝ, (q.1 + q.2) ^ 2 ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n)))
      = 2 * E2 pd ps n + 2 * (E1 pd ps n) ^ 2 := by
        have h_integrable : MeasureTheory.Integrable (fun q : ℝ × ℝ => q.1^2) ((lawMeasure pd ps n).prod (lawMeasure pd ps n)) ∧ MeasureTheory.Integrable (fun q : ℝ × ℝ => q.2^2) ((lawMeasure pd ps n).prod (lawMeasure pd ps n)) ∧ MeasureTheory.Integrable (fun q : ℝ × ℝ => q.1 * q.2) ((lawMeasure pd ps n).prod (lawMeasure pd ps n)) := by
          refine' ⟨ _, _, _ ⟩;
          · refine' integrable_prod_law hpd hps hsum n _ _ _ _;
            exacts [ measurable_fst.pow_const 2, ( 2 ^ n ) ^ 2, fun q hq₁ hq₂ => by rw [ abs_of_nonneg ( sq_nonneg _ ) ] ; exact pow_le_pow_left₀ ( by linarith [ hq₁.1 ] ) hq₁.2 2 ];
          · have h_integrable : ∀ x ∈ Set.Icc (1 : ℝ) (2 ^ n), |x ^ 2| ≤ (2 ^ n) ^ 2 := by
              exact fun x hx => by rw [ abs_of_nonneg ( sq_nonneg x ) ] ; exact pow_le_pow_left₀ ( by linarith [ hx.1 ] ) hx.2 2;
            refine' integrable_prod_law hpd hps hsum n _ _ _ _;
            exacts [ measurable_snd.pow_const 2, ( 2 ^ n ) ^ 2, fun q hq₁ hq₂ => h_integrable q.2 hq₂ ];
          · refine' integrable_prod_law hpd hps hsum n _ _ _ _ <;> norm_num;
            exacts [ measurable_fst.mul measurable_snd, ( 2 ^ n ) ^ 2, fun a b ha hb ha' hb' => by rw [ abs_of_nonneg ( by positivity ), abs_of_nonneg ( by positivity ) ] ; nlinarith ];
        simp +decide only [add_sq];
        rw [ MeasureTheory.integral_add, MeasureTheory.integral_add ] <;> norm_num [ mul_assoc, MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const, h_integrable ];
        · rw [ show ( ∫ q : ℝ × ℝ, q.1 ^ 2 ∂ ( lawMeasure pd ps n ).prod ( lawMeasure pd ps n ) ) = ( ∫ x : ℝ, x ^ 2 ∂ ( lawMeasure pd ps n ) ) * ( ∫ y : ℝ, 1 ∂ ( lawMeasure pd ps n ) ) from ?_, show ( ∫ q : ℝ × ℝ, q.2 ^ 2 ∂ ( lawMeasure pd ps n ).prod ( lawMeasure pd ps n ) ) = ( ∫ x : ℝ, 1 ∂ ( lawMeasure pd ps n ) ) * ( ∫ y : ℝ, y ^ 2 ∂ ( lawMeasure pd ps n ) ) from ?_ ];
          · rw [ show ( ∫ q : ℝ × ℝ, q.1 * q.2 ∂ ( lawMeasure pd ps n ).prod ( lawMeasure pd ps n ) ) = ( ∫ x : ℝ, x ∂ ( lawMeasure pd ps n ) ) * ( ∫ y : ℝ, y ∂ ( lawMeasure pd ps n ) ) from ?_ ];
            · norm_num [ E1, E2 ] ; ring;
              rw [ MeasureTheory.measureReal_def ];
              rw [ prob_law hpd hps hsum n |> fun h => h.measure_univ ] ; norm_num;
            · convert MeasureTheory.integral_prod_mul _ _ using 1;
              · rfl;
              · have := prob_law hpd hps hsum n; infer_instance;
              · have := prob_law hpd hps hsum n;
                infer_instance;
          · convert MeasureTheory.integral_prod_mul _ _ using 1;
            · norm_num;
            · have := prob_law hpd hps hsum n; infer_instance;
            · have := prob_law hpd hps hsum n;
              infer_instance;
          · convert MeasureTheory.integral_prod_mul _ _ using 1;
            · norm_num;
            · have := prob_law hpd hps hsum n; infer_instance;
            · have := prob_law hpd hps hsum n;
              infer_instance;
        · exact h_integrable.2.2.const_mul _;
        · exact h_integrable.2.2.const_mul _

/-
Marginalisation: the integral over `prod4` of a function of the first two coordinates
reduces to the 2-fold product integral.
-/
lemma int_prod4_first (n : ℕ) :
    (∫ q : ℝ × ℝ × ℝ × ℝ, (q.1 + q.2.1)⁻¹ ∂(prod4 (lawMeasure pd ps n)))
      = Sinv pd ps n := by
        convert ( integral_map ?_ ?_ ) using 1;
        any_goals try infer_instance;
        · rw [ MeasureTheory.integral_map ];
          · convert ( congr_arg ( fun m : MeasureTheory.Measure ( ℝ × ℝ ) => ∫ q : ℝ × ℝ, ( q.1 + q.2 ) ⁻¹ ∂m ) ( prod4_map12 ( lawMeasure pd ps n ) ) ) using 1;
            · rw [ MeasureTheory.integral_map ];
              · exact measurable_fst.aemeasurable.prodMk measurable_snd.fst.aemeasurable;
              · exact Measurable.aestronglyMeasurable ( by exact Measurable.inv ( measurable_fst.add measurable_snd ) );
            · grind +suggestions;
          · exact measurable_fst.add measurable_snd |> Measurable.aemeasurable;
          · exact measurable_inv.aestronglyMeasurable;
        · exact measurable_fst.add measurable_snd |> Measurable.aemeasurable;
        · exact measurable_inv.aestronglyMeasurable

/-
Marginalisation: the integral over `prod4` of a function of the last two coordinates
reduces to the 2-fold product integral.
-/
lemma int_prod4_last (n : ℕ) :
    (∫ q : ℝ × ℝ × ℝ × ℝ, (q.2.2.1 + q.2.2.2)⁻¹ ∂(prod4 (lawMeasure pd ps n)))
      = Sinv pd ps n := by
        have h_map : (prod4 (lawMeasure pd ps n)).map (fun q => (q.2.2.1, q.2.2.2)) = (lawMeasure pd ps n).prod (lawMeasure pd ps n) := by
          convert prod4_map34 ( lawMeasure pd ps n ) using 1;
          grind +suggestions;
        convert congr_arg ( fun μ => ∫ q : ℝ × ℝ, ( q.1 + q.2 ) ⁻¹ ∂μ ) h_map using 1;
        rw [ MeasureTheory.integral_map ];
        · exact measurable_snd.snd.aemeasurable;
        · exact Measurable.aestronglyMeasurable ( by exact Measurable.inv ( measurable_fst.add measurable_snd ) )

/-
`∫ (diamondMap q)⁻¹ ∂(prod4 (law n)) = 2·Sinv n` (via `inv_par`).
-/
lemma int_prod4_diamond_inv (n : ℕ) :
    (∫ q : ℝ × ℝ × ℝ × ℝ, (diamondMap q)⁻¹ ∂(prod4 (lawMeasure pd ps n)))
      = 2 * Sinv pd ps n := by
        convert congr_arg₂ ( · + · ) ( int_prod4_first hpd hps hsum n ) ( int_prod4_last hpd hps hsum n ) using 1;
        · rw [ ← MeasureTheory.integral_add ];
          · refine' MeasureTheory.integral_congr_ae _;
            filter_upwards [ ae_box_prod4 hpd hps hsum n ] with q hq;
            convert inv_par _ _ _ _ using 1;
            · linarith [ hq.1.1, hq.2.1.1 ];
            · linarith [ hq.2.2.1.1, hq.2.2.2.1 ];
          · refine' integrable_prod4_law hpd hps hsum n _ _ _ _;
            exact Measurable.inv ( measurable_fst.add measurable_snd.fst );
            exacts [ 1, fun q hq₁ hq₂ hq₃ hq₄ => by rw [ abs_of_nonneg ( inv_nonneg.2 ( add_nonneg ( zero_le_one.trans hq₁.1 ) ( zero_le_one.trans hq₂.1 ) ) ) ] ; exact inv_le_one_of_one_le₀ ( by linarith [ hq₁.1, hq₂.1 ] ) ];
          · apply integrable_prod4_law;
            lia;
            grind;
            exact hsum;
            fun_prop;
            exact fun q hq₁ hq₂ hq₃ hq₄ => by rw [ abs_of_nonneg ( inv_nonneg.2 ( add_nonneg ( by linarith [ Set.mem_Icc.1 hq₃ ] ) ( by linarith [ Set.mem_Icc.1 hq₄ ] ) ) ) ] ; exact inv_le_one_of_one_le₀ ( by linarith [ Set.mem_Icc.1 hq₃, Set.mem_Icc.1 hq₄ ] ) ;
        · ring

/-! ### Mixed product-integral value helpers (via independence) -/

lemma int_prod_fst_inv (n : ℕ) :
    (∫ q : ℝ × ℝ, q.1⁻¹ ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n))) = Einv pd ps n := by
  haveI := prob_law hpd hps hsum n
  have h := MeasureTheory.integral_prod_mul (μ := lawMeasure pd ps n) (ν := lawMeasure pd ps n)
    (fun x => x⁻¹) (fun _ => (1 : ℝ))
  simpa [Einv] using h

lemma int_prod_snd_inv (n : ℕ) :
    (∫ q : ℝ × ℝ, q.2⁻¹ ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n))) = Einv pd ps n := by
  haveI := prob_law hpd hps hsum n
  have h := MeasureTheory.integral_prod_mul (μ := lawMeasure pd ps n) (ν := lawMeasure pd ps n)
    (fun _ => (1 : ℝ)) (fun y => y⁻¹)
  simpa [Einv] using h

lemma int_prod_fst' (n : ℕ) :
    (∫ q : ℝ × ℝ, q.1 ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n))) = E1 pd ps n := by
  haveI := prob_law hpd hps hsum n
  have h := MeasureTheory.integral_prod_mul (μ := lawMeasure pd ps n) (ν := lawMeasure pd ps n)
    (fun x => x) (fun _ => (1 : ℝ))
  simpa [E1] using h

lemma int_prod_snd' (n : ℕ) :
    (∫ q : ℝ × ℝ, q.2 ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n))) = E1 pd ps n := by
  haveI := prob_law hpd hps hsum n
  have h := MeasureTheory.integral_prod_mul (μ := lawMeasure pd ps n) (ν := lawMeasure pd ps n)
    (fun _ => (1 : ℝ)) (fun y => y)
  simpa [E1] using h

lemma int_prod_mul_inv (n : ℕ) :
    (∫ q : ℝ × ℝ, q.1 * q.2⁻¹ ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n)))
      = E1 pd ps n * Einv pd ps n := by
  haveI := prob_law hpd hps hsum n
  rw [E1, Einv, MeasureTheory.integral_prod_mul (fun x => x) (fun y => y⁻¹)]

lemma int_prod_snd_mul_inv (n : ℕ) :
    (∫ q : ℝ × ℝ, q.2 * q.1⁻¹ ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n)))
      = E1 pd ps n * Einv pd ps n := by
  haveI := prob_law hpd hps hsum n
  rw [show (fun q : ℝ × ℝ => q.2 * q.1⁻¹) = (fun q : ℝ × ℝ => q.1⁻¹ * q.2) from by funext q; ring]
  rw [MeasureTheory.integral_prod_mul (fun x => x⁻¹) (fun y => y), E1, Einv, mul_comm]

lemma int_prod_sq_mul_inv (n : ℕ) :
    (∫ q : ℝ × ℝ, q.1 ^ 2 * q.2⁻¹ ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n)))
      = E2 pd ps n * Einv pd ps n := by
  haveI := prob_law hpd hps hsum n
  rw [E2, Einv, MeasureTheory.integral_prod_mul (fun x => x ^ 2) (fun y => y⁻¹)]

lemma int_prod_snd_sq_mul_inv (n : ℕ) :
    (∫ q : ℝ × ℝ, q.2 ^ 2 * q.1⁻¹ ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n)))
      = E2 pd ps n * Einv pd ps n := by
  haveI := prob_law hpd hps hsum n
  rw [show (fun q : ℝ × ℝ => q.2 ^ 2 * q.1⁻¹) = (fun q : ℝ × ℝ => q.1⁻¹ * q.2 ^ 2) from by
    funext q; ring]
  rw [MeasureTheory.integral_prod_mul (fun x => x⁻¹) (fun y => y ^ 2), E2, Einv, mul_comm]

/-- Integrability over the 2-fold product of a function of the form `f q.1 * g q.2` with `f, g`
bounded on the support box. -/
lemma integrable_prod_mul_law (n : ℕ) (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (Cf Cg : ℝ) (hCf : ∀ x ∈ Set.Icc (1 : ℝ) (2 ^ n), |f x| ≤ Cf)
    (hCg : ∀ x ∈ Set.Icc (1 : ℝ) (2 ^ n), |g x| ≤ Cg) :
    Integrable (fun q : ℝ × ℝ => f q.1 * g q.2) ((lawMeasure pd ps n).prod (lawMeasure pd ps n)) := by
  have hmem : (1 : ℝ) ∈ Set.Icc (1 : ℝ) (2 ^ n) := ⟨le_refl 1, one_le_pow₀ (by norm_num)⟩
  have hCf0 : 0 ≤ Cf := le_trans (abs_nonneg _) (hCf 1 hmem)
  refine integrable_prod_law hpd hps hsum n (fun q => f q.1 * g q.2)
    ((hf.comp measurable_fst).mul (hg.comp measurable_snd)) (Cf * Cg) ?_
  intro q hq1 hq2
  calc |f q.1 * g q.2| = |f q.1| * |g q.2| := abs_mul _ _
    _ ≤ Cf * Cg := mul_le_mul (hCf q.1 hq1) (hCg q.2 hq2) (abs_nonneg _) hCf0

lemma E2_ge_E1sq (n : ℕ) : (E1 pd ps n) ^ 2 ≤ E2 pd ps n := by
  haveI := prob_law hpd hps hsum n
  set μ := lawMeasure pd ps n with hμ
  set c := ∫ x, x ∂μ with hc
  have hint : Integrable (fun x : ℝ => x) μ :=
    integrable_law hpd hps hsum n (fun x => x) measurable_id (2 ^ n)
      (fun x hx => by rw [abs_of_nonneg (by linarith [hx.1] : (0 : ℝ) ≤ x)]; exact hx.2)
  have hint2 : Integrable (fun x : ℝ => x ^ 2) μ :=
    integrable_law hpd hps hsum n (fun x => x ^ 2) (by fun_prop) ((2 ^ n) ^ 2)
      (fun x hx => by rw [abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (by linarith [hx.1]) hx.2 2)
  have hintmul : Integrable (fun x : ℝ => (2 * c) * x) μ := hint.const_mul _
  have h0 : 0 ≤ ∫ x, (x - c) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have expand : ∫ x, (x - c) ^ 2 ∂μ = (∫ x, x ^ 2 ∂μ) - c ^ 2 := by
    have e1 : (fun x : ℝ => (x - c) ^ 2) = (fun x => (x ^ 2 - (2 * c) * x) + c ^ 2) := by
      funext x; ring
    rw [e1, integral_add (f := fun x => x ^ 2 - (2 * c) * x) (g := fun _ => c ^ 2)
          (hint2.sub hintmul) (integrable_const _),
        integral_sub (f := fun x => x ^ 2) (g := fun x => (2 * c) * x) hint2 hintmul,
        integral_const_mul, integral_const]
    simp only [smul_eq_mul, probReal_univ]
    rw [← hc]; ring
  rw [E1, E2, ← hc]
  linarith [h0, expand]

lemma E1Einv_ge_one (n : ℕ) : 1 ≤ E1 pd ps n * Einv pd ps n := by
  haveI := prob_law hpd hps hsum n
  set μ := (lawMeasure pd ps n).prod (lawMeasure pd ps n) with hμ
  have i1 : Integrable (fun q : ℝ × ℝ => q.1 * q.2⁻¹) μ :=
    integrable_prod_mul_law hpd hps hsum n (fun x => x) (fun y => y⁻¹) measurable_id
      measurable_id.inv (2 ^ n) 1 (fun x hx => by rw [abs_of_nonneg (by linarith [hx.1])]; exact hx.2)
      (fun x hx => by rw [abs_of_nonneg (inv_nonneg.2 (by linarith [hx.1]))]; exact inv_le_one_of_one_le₀ hx.1)
  have i2 : Integrable (fun q : ℝ × ℝ => q.2 * q.1⁻¹) μ := by
    rw [show (fun q : ℝ × ℝ => q.2 * q.1⁻¹) = (fun q : ℝ × ℝ => q.1⁻¹ * q.2) from by funext q; ring]
    exact integrable_prod_mul_law hpd hps hsum n (fun x => x⁻¹) (fun y => y) measurable_id.inv
      measurable_id 1 (2 ^ n)
      (fun x hx => by rw [abs_of_nonneg (inv_nonneg.2 (by linarith [hx.1]))]; exact inv_le_one_of_one_le₀ hx.1)
      (fun x hx => by rw [abs_of_nonneg (by linarith [hx.1])]; exact hx.2)
  have h2 : 2 * (E1 pd ps n * Einv pd ps n)
      = ∫ q : ℝ × ℝ, (q.1 * q.2⁻¹ + q.2 * q.1⁻¹) ∂μ := by
    rw [integral_add i1 i2, int_prod_mul_inv hpd hps hsum, int_prod_snd_mul_inv hpd hps hsum]; ring
  have hge : (2 : ℝ) ≤ ∫ q : ℝ × ℝ, (q.1 * q.2⁻¹ + q.2 * q.1⁻¹) ∂μ := by
    have hconst : ∫ _q : ℝ × ℝ, (2 : ℝ) ∂μ = 2 := by simp
    rw [← hconst]
    apply integral_mono_ae (integrable_const _) (i1.add i2)
    filter_upwards [ae_box_prod hpd hps hsum n] with q hq
    simp only [Pi.add_apply]
    have hq1 : (0 : ℝ) < q.1 := by linarith [hq.1.1]
    have hq2 : (0 : ℝ) < q.2 := by linarith [hq.2.1]
    have key : q.1 * q.2⁻¹ + q.2 * q.1⁻¹ - 2 = (q.1 - q.2) ^ 2 / (q.1 * q.2) := by
      field_simp; ring
    nlinarith [div_nonneg (sq_nonneg (q.1 - q.2)) (le_of_lt (mul_pos hq1 hq2)), key]
  linarith [h2, hge]

/-! ### Moment recursions -/

lemma E1_succ (n : ℕ) : E1 pd ps (n + 1) = 2 * ps * E1 pd ps n + pd * Dmean pd ps n := by
  unfold E1 Dmean;
  rw [ integral_succ ];
  rw [ int_prod_sum ] ; ring;
  all_goals norm_cast;
  · exact measurable_id;
  · refine' integrable_prod_law hpd hps hsum n _ _ _ _;
    exacts [ measurable_fst.add measurable_snd, 2 ^ n + 2 ^ n, fun q hq₁ hq₂ => abs_le.mpr ⟨ by linarith [ hq₁.1, hq₁.2, hq₂.1, hq₂.2 ], by linarith [ hq₁.1, hq₁.2, hq₂.1, hq₂.2 ] ⟩ ];
  · -- The function diamondMap is bounded on the box [1, 2^n]^4.
    have h_diamondMap_bounded : ∀ q : ℝ × ℝ × ℝ × ℝ, q.1 ∈ Set.Icc (1 : ℝ) (2 ^ n) → q.2.1 ∈ Set.Icc (1 : ℝ) (2 ^ n) → q.2.2.1 ∈ Set.Icc (1 : ℝ) (2 ^ n) → q.2.2.2 ∈ Set.Icc (1 : ℝ) (2 ^ n) → |diamondMap q| ≤ 2 ^ n := by
      intros q hq1 hq2 hq3 hq4
      have h_diamond_bound : 1 ≤ diamondMap q ∧ diamondMap q ≤ 2 ^ n := by
        apply diamond_bounds; exact hq1.1; exact hq1.2; exact hq2.1; exact hq2.2; exact hq3.1; exact hq3.2; exact hq4.1; exact hq4.2;
      exact abs_le.mpr ⟨ by linarith, by linarith ⟩;
    apply integrable_prod4_law;
    exacts [ hpd, hps, hsum, measurable_diamondMap, h_diamondMap_bounded ]

lemma E2_succ (n : ℕ) :
    E2 pd ps (n + 1) = ps * (2 * E2 pd ps n + 2 * (E1 pd ps n) ^ 2) + pd * Dsq pd ps n := by
      convert integral_succ _ _ _ _ _ using 3;
      any_goals exact n;
      any_goals exact fun x => x ^ 2;
      case convert_1 => exact pd;
      any_goals assumption;
      constructor <;> intro h;
      · intro h1 h2 h3; exact integral_succ hpd hps hsum n ( fun x => x ^ 2 ) ( by measurability ) h2 h3;
      · convert h ( measurable_id.pow_const 2 ) _ _ using 1;
        · rw [ int_prod_sum_sq ];
          · rfl;
          · linarith;
          · linarith;
          · linarith;
        · apply integrable_prod_law;
          any_goals exact ( 2 * 2 ^ n ) ^ 2;
          · linarith;
          · linarith;
          · bv_omega;
          · exact Measurable.pow_const ( measurable_fst.add measurable_snd ) _;
          · exact fun q hq₁ hq₂ => by rw [ abs_of_nonneg ( sq_nonneg _ ) ] ; nlinarith only [ hq₁.1, hq₁.2, hq₂.1, hq₂.2 ] ;
        · apply integrable_prod4_law;
          any_goals exact ( 2 ^ n ) ^ 2;
          · linarith;
          · linarith;
          · linarith;
          · exact Measurable.pow_const ( measurable_diamondMap ) _;
          · intro q hq1 hq2 hq3 hq4; rw [ abs_of_nonneg ( sq_nonneg _ ) ] ; exact pow_le_pow_left₀ ( by exact div_nonneg ( mul_nonneg ( by linarith [ Set.mem_Icc.mp hq1, Set.mem_Icc.mp hq2 ] ) ( by linarith [ Set.mem_Icc.mp hq3, Set.mem_Icc.mp hq4 ] ) ) ( by linarith [ Set.mem_Icc.mp hq1, Set.mem_Icc.mp hq2, Set.mem_Icc.mp hq3, Set.mem_Icc.mp hq4 ] ) ) ( diamond_bounds hq1.1 hq1.2 hq2.1 hq2.2 hq3.1 hq3.2 hq4.1 hq4.2 |>.2 ) 2;

lemma Einv_succ (n : ℕ) : Einv pd ps (n + 1) = (1 + pd) * Sinv pd ps n := by
  convert integral_succ hpd hps hsum n ( fun x => x⁻¹ ) measurable_id.inv _ _ using 1;
  · rw [ show ( 1 + pd ) = ps + 2 * pd by linarith ] ; rw [ int_prod4_diamond_inv ] ; ring!;
    · grind;
    · linarith;
    · exact hsum;
  · refine' integrable_prod_law hpd hps hsum n _ _ _ _;
    exacts [ Measurable.inv ( measurable_fst.add measurable_snd ), 1, fun q hq₁ hq₂ => by rw [ abs_of_nonneg ( inv_nonneg.2 ( add_nonneg ( zero_le_one.trans hq₁.1 ) ( zero_le_one.trans hq₂.1 ) ) ) ] ; exact inv_le_one_of_one_le₀ ( by linarith [ hq₁.1, hq₂.1 ] ) ];
  · refine' integrable_prod4_law hpd hps hsum n _ _ 1 _;
    · exact Measurable.inv ( measurable_diamondMap );
    · intro q hq1 hq2 hq3 hq4; rw [ abs_of_nonneg ( inv_nonneg.2 <| show 0 ≤ diamondMap q from ?_ ) ] ; exact inv_le_one_of_one_le₀ <| by
                                                                      exact Reduced.diamond_bounds hq1.1 hq1.2 hq2.1 hq2.2 hq3.1 hq3.2 hq4.1 hq4.2 |>.1;
      exact div_nonneg ( mul_nonneg ( add_nonneg ( le_trans zero_le_one hq1.1 ) ( le_trans zero_le_one hq2.1 ) ) ( add_nonneg ( le_trans zero_le_one hq3.1 ) ( le_trans zero_le_one hq4.1 ) ) ) ( add_nonneg ( add_nonneg ( le_trans zero_le_one hq1.1 ) ( le_trans zero_le_one hq2.1 ) ) ( add_nonneg ( le_trans zero_le_one hq3.1 ) ( le_trans zero_le_one hq4.1 ) ) )

/-! ### One-step inequalities -/

/-- `Sinv = Einv/2 - Δ/4` (reciprocal identity). -/
lemma Sinv_eq (n : ℕ) : Sinv pd ps n = Einv pd ps n / 2 - Delta pd ps n / 4 := by
  haveI := prob_law hpd hps hsum n
  set μ := (lawMeasure pd ps n).prod (lawMeasure pd ps n) with hμ
  have j1 : Integrable (fun q : ℝ × ℝ => q.1⁻¹) μ :=
    integrable_prod_law hpd hps hsum n (fun q => q.1⁻¹) measurable_fst.inv 1
      (fun q hq1 hq2 => by rw [abs_of_nonneg (inv_nonneg.2 (by linarith [hq1.1]))]; exact inv_le_one_of_one_le₀ hq1.1)
  have j2 : Integrable (fun q : ℝ × ℝ => q.2⁻¹) μ :=
    integrable_prod_law hpd hps hsum n (fun q => q.2⁻¹) measurable_snd.inv 1
      (fun q hq1 hq2 => by rw [abs_of_nonneg (inv_nonneg.2 (by linarith [hq2.1]))]; exact inv_le_one_of_one_le₀ hq2.1)
  have jd : Integrable (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2 / (q.1 * q.2 * (q.1 + q.2))) μ :=
    integrable_prod_law hpd hps hsum n _ (by fun_prop) ((2 ^ n) ^ 2)
      (fun q hq1 hq2 => by
        have h1 : (1 : ℝ) ≤ q.1 := hq1.1
        have h2 : (1 : ℝ) ≤ q.2 := hq2.1
        rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity)), div_le_iff₀ (by positivity)]
        have hp : (1 : ℝ) ≤ q.1 * q.2 := by
          nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
        have hden1 : (1 : ℝ) ≤ q.1 * q.2 * (q.1 + q.2) := by
          nlinarith [mul_le_mul_of_nonneg_right hp (by linarith : (0 : ℝ) ≤ q.1 + q.2), h1, h2]
        have hnum : (q.1 - q.2) ^ 2 ≤ ((2 : ℝ) ^ n) ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.2 hq1.2) (sub_nonneg.2 hq2.2),
            mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2), h1, h2, hq1.2, hq2.2]
        calc (q.1 - q.2) ^ 2 ≤ ((2 : ℝ) ^ n) ^ 2 := hnum
          _ ≤ ((2 : ℝ) ^ n) ^ 2 * (q.1 * q.2 * (q.1 + q.2)) :=
              le_mul_of_one_le_right (by positivity) hden1)
  have hcong : (fun q : ℝ × ℝ => (q.1 + q.2)⁻¹)
      =ᵐ[μ] (fun q : ℝ × ℝ => (1 / 4) * (q.1⁻¹ + q.2⁻¹)
        - (1 / 4) * ((q.1 - q.2) ^ 2 / (q.1 * q.2 * (q.1 + q.2)))) := by
    filter_upwards [ae_box_prod hpd hps hsum n] with q hq
    exact inv_add_eq q.1 q.2 (by linarith [hq.1.1]) (by linarith [hq.2.1])
  rw [Sinv, integral_congr_ae hcong,
      integral_sub (f := fun q : ℝ × ℝ => (1 / 4) * (q.1⁻¹ + q.2⁻¹))
        (g := fun q : ℝ × ℝ => (1 / 4) * ((q.1 - q.2) ^ 2 / (q.1 * q.2 * (q.1 + q.2))))
        ((j1.add j2).const_mul _) (jd.const_mul _),
      integral_const_mul, integral_const_mul,
      integral_add (f := fun q : ℝ × ℝ => q.1⁻¹) (g := fun q : ℝ × ℝ => q.2⁻¹) j1 j2,
      int_prod_fst_inv hpd hps hsum, int_prod_snd_inv hpd hps hsum]
  show (1 / 4) * (Einv pd ps n + Einv pd ps n) - (1 / 4) * Delta pd ps n = _
  ring

lemma Delta_nonneg (n : ℕ) : 0 ≤ Delta pd ps n := by
  refine' MeasureTheory.integral_nonneg_of_ae _;
  filter_upwards [ Reduced.ae_box_prod hpd hps hsum n ] with q hq using div_nonneg ( sq_nonneg _ ) ( mul_nonneg ( mul_nonneg ( by linarith [ hq.1.1 ] ) ( by linarith [ hq.2.1 ] ) ) ( by linarith [ hq.1.1, hq.2.1 ] ) )

lemma Sinv_nonneg (n : ℕ) : 0 ≤ Sinv pd ps n := by
  refine' MeasureTheory.integral_nonneg_of_ae _;
  filter_upwards [ ae_box_prod hpd hps hsum n ] with q hq using inv_nonneg.2 ( add_nonneg ( le_trans zero_le_one hq.1.1 ) ( le_trans zero_le_one hq.2.1 ) )

lemma Delta_le (n : ℕ) : Delta pd ps n ≤ 2 * Einv pd ps n := by
  have hs := Sinv_eq hpd hps hsum n
  have hn := Sinv_nonneg hpd hps hsum n
  linarith

/-- The diamond mean is at most `E[R]` (concavity of `par`). -/
lemma Dmean_le_E1 (n : ℕ) : Dmean pd ps n ≤ E1 pd ps n := by
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
  have idm : Integrable (fun q : ℝ × ℝ × ℝ × ℝ => diamondMap q) (prod4 μ) :=
    integrable_prod4_law hpd hps hsum n diamondMap measurable_diamondMap (2 ^ n)
      (fun q h1 h2 h3 h4 => by
        have hb := diamond_bounds h1.1 h1.2 h2.1 h2.2 h3.1 h3.2 h4.1 h4.2
        rw [show diamondMap q = diamondVal q.1 q.2.1 q.2.2.1 q.2.2.2 from rfl,
          abs_of_nonneg (le_trans zero_le_one hb.1)]
        exact hb.2)
  have iab : Integrable (fun q : ℝ × ℝ × ℝ × ℝ => q.1 + q.2.1) (prod4 μ) :=
    integrable_prod4_law hpd hps hsum n _ (by fun_prop) (2 ^ n + 2 ^ n)
      (fun q h1 h2 h3 h4 => by rw [abs_of_nonneg (by linarith [h1.1, h2.1])]; linarith [h1.2, h2.2])
  have icd : Integrable (fun q : ℝ × ℝ × ℝ × ℝ => q.2.2.1 + q.2.2.2) (prod4 μ) :=
    integrable_prod4_law hpd hps hsum n _ (by fun_prop) (2 ^ n + 2 ^ n)
      (fun q h1 h2 h3 h4 => by rw [abs_of_nonneg (by linarith [h3.1, h4.1])]; linarith [h3.2, h4.2])
  have hbound : Dmean pd ps n
      ≤ ∫ q : ℝ × ℝ × ℝ × ℝ, ((q.1 + q.2.1) + (q.2.2.1 + q.2.2.2)) / 4 ∂(prod4 μ) := by
    apply integral_mono_ae idm ((iab.add icd).div_const 4)
    filter_upwards [ae_box_prod4 hpd hps hsum n] with q hq
    have e : diamondMap q = par (q.1 + q.2.1) (q.2.2.1 + q.2.2.2) := rfl
    rw [e]
    exact par_le_quarter _ _ (by linarith [hq.1.1, hq.2.1.1]) (by linarith [hq.2.2.1.1, hq.2.2.2.1])
  have hval : ∫ q : ℝ × ℝ × ℝ × ℝ, ((q.1 + q.2.1) + (q.2.2.1 + q.2.2.2)) / 4 ∂(prod4 μ)
      = E1 pd ps n := by
    rw [show (fun q : ℝ × ℝ × ℝ × ℝ => ((q.1 + q.2.1) + (q.2.2.1 + q.2.2.2)) / 4)
        = (fun q : ℝ × ℝ × ℝ × ℝ => (1 / 4) * ((q.1 + q.2.1) + (q.2.2.1 + q.2.2.2))) from by
          funext q; ring]
    rw [integral_const_mul,
        integral_add (f := fun q : ℝ × ℝ × ℝ × ℝ => q.1 + q.2.1)
          (g := fun q : ℝ × ℝ × ℝ × ℝ => q.2.2.1 + q.2.2.2) iab icd, hab, hcd]
    ring
  rw [hval] at hbound
  exact hbound

/-- Regrouping the 4-fold product into a product of two 2-fold products via `prodAssoc`. -/
lemma int_prod4_eq_assoc (n : ℕ) (g : ℝ × ℝ × ℝ × ℝ → ℝ) (hg : Measurable g) :
    ∫ q, g q ∂(prod4 (lawMeasure pd ps n))
      = ∫ z : (ℝ × ℝ) × (ℝ × ℝ), g (MeasurableEquiv.prodAssoc z)
          ∂(((lawMeasure pd ps n).prod (lawMeasure pd ps n)).prod
              ((lawMeasure pd ps n).prod (lawMeasure pd ps n))) := by
  haveI := prob_law hpd hps hsum n
  have h : prod4 (lawMeasure pd ps n)
      = (((lawMeasure pd ps n).prod (lawMeasure pd ps n)).prod
          ((lawMeasure pd ps n).prod (lawMeasure pd ps n))).map MeasurableEquiv.prodAssoc := by
    rw [Measure.prodAssoc_prod]; rfl
  rw [h, integral_map (by fun_prop) (hg.aestronglyMeasurable)]

/-- `∫ a·b ∂prod4 = (2E1)²` where `a = X₁+X₂`, `b = X₃+X₄` (independence of the two blocks). -/
lemma int_prod4_ab (n : ℕ) :
    ∫ q : ℝ × ℝ × ℝ × ℝ, (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2) ∂(prod4 (lawMeasure pd ps n))
      = (2 * E1 pd ps n) * (2 * E1 pd ps n) := by
  haveI := prob_law hpd hps hsum n
  rw [int_prod4_eq_assoc hpd hps hsum n _ (by fun_prop),
    show (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        ((MeasurableEquiv.prodAssoc z).1 + (MeasurableEquiv.prodAssoc z).2.1) *
          ((MeasurableEquiv.prodAssoc z).2.2.1 + (MeasurableEquiv.prodAssoc z).2.2.2))
        = (fun z : (ℝ × ℝ) × (ℝ × ℝ) => (z.1.1 + z.1.2) * (z.2.1 + z.2.2)) from rfl,
    MeasureTheory.integral_prod_mul (fun p : ℝ × ℝ => p.1 + p.2) (fun p : ℝ × ℝ => p.1 + p.2),
    int_prod_sum hpd hps hsum n]

/-- `∫ a²·b ∂prod4 = (2E2+2E1²)·(2E1)`. -/
lemma int_prod4_a2b (n : ℕ) :
    ∫ q : ℝ × ℝ × ℝ × ℝ, (q.1 + q.2.1) ^ 2 * (q.2.2.1 + q.2.2.2) ∂(prod4 (lawMeasure pd ps n))
      = (2 * E2 pd ps n + 2 * (E1 pd ps n) ^ 2) * (2 * E1 pd ps n) := by
  haveI := prob_law hpd hps hsum n
  rw [int_prod4_eq_assoc hpd hps hsum n _ (by fun_prop),
    show (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        ((MeasurableEquiv.prodAssoc z).1 + (MeasurableEquiv.prodAssoc z).2.1) ^ 2 *
          ((MeasurableEquiv.prodAssoc z).2.2.1 + (MeasurableEquiv.prodAssoc z).2.2.2))
        = (fun z : (ℝ × ℝ) × (ℝ × ℝ) => (z.1.1 + z.1.2) ^ 2 * (z.2.1 + z.2.2)) from rfl,
    MeasureTheory.integral_prod_mul (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2) (fun p : ℝ × ℝ => p.1 + p.2),
    int_prod_sum_sq hpd hps hsum n, int_prod_sum hpd hps hsum n]

/-- `∫ a·b² ∂prod4 = (2E1)·(2E2+2E1²)`. -/
lemma int_prod4_ab2 (n : ℕ) :
    ∫ q : ℝ × ℝ × ℝ × ℝ, (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2) ^ 2 ∂(prod4 (lawMeasure pd ps n))
      = (2 * E1 pd ps n) * (2 * E2 pd ps n + 2 * (E1 pd ps n) ^ 2) := by
  haveI := prob_law hpd hps hsum n
  rw [int_prod4_eq_assoc hpd hps hsum n _ (by fun_prop),
    show (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        ((MeasurableEquiv.prodAssoc z).1 + (MeasurableEquiv.prodAssoc z).2.1) *
          ((MeasurableEquiv.prodAssoc z).2.2.1 + (MeasurableEquiv.prodAssoc z).2.2.2) ^ 2)
        = (fun z : (ℝ × ℝ) × (ℝ × ℝ) => (z.1.1 + z.1.2) * (z.2.1 + z.2.2) ^ 2) from rfl,
    MeasureTheory.integral_prod_mul (fun p : ℝ × ℝ => p.1 + p.2) (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2),
    int_prod_sum hpd hps hsum n, int_prod_sum_sq hpd hps hsum n]

/-- The diamond second moment is at most `E[R]²` (since `par(a,b) ≤ √(ab)/2`). -/
lemma Dsq_le_E1sq (n : ℕ) : Dsq pd ps n ≤ (E1 pd ps n) ^ 2 := by
  haveI := prob_law hpd hps hsum n
  have idsq : Integrable (fun q : ℝ × ℝ × ℝ × ℝ => diamondMap q ^ 2) (prod4 (lawMeasure pd ps n)) :=
    integrable_prod4_law hpd hps hsum n _ (measurable_diamondMap.pow_const 2) ((2 ^ n) ^ 2)
      (fun q h1 h2 h3 h4 => by
        have hb := diamond_bounds h1.1 h1.2 h2.1 h2.2 h3.1 h3.2 h4.1 h4.2
        rw [show diamondMap q ^ 2 = (diamondVal q.1 q.2.1 q.2.2.1 q.2.2.2) ^ 2 from rfl,
          abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (le_trans zero_le_one hb.1) hb.2 2)
  have iab : Integrable (fun q : ℝ × ℝ × ℝ × ℝ => (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2))
      (prod4 (lawMeasure pd ps n)) :=
    integrable_prod4_law hpd hps hsum n _ (by fun_prop) ((2 ^ n + 2 ^ n) * (2 ^ n + 2 ^ n))
      (fun q h1 h2 h3 h4 => by
        rw [abs_of_nonneg (mul_nonneg (by linarith [h1.1, h2.1]) (by linarith [h3.1, h4.1]))]
        exact mul_le_mul (by linarith [h1.2, h2.2]) (by linarith [h3.2, h4.2])
          (by linarith [h3.1, h4.1]) (by positivity))
  have hbound : Dsq pd ps n
      ≤ ∫ q : ℝ × ℝ × ℝ × ℝ, (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2) / 4 ∂(prod4 (lawMeasure pd ps n)) := by
    apply integral_mono_ae idsq (iab.div_const 4)
    filter_upwards [ae_box_prod4 hpd hps hsum n] with q hq
    have ha : (0 : ℝ) < q.1 + q.2.1 := by linarith [hq.1.1, hq.2.1.1]
    have hbpos : (0 : ℝ) < q.2.2.1 + q.2.2.2 := by linarith [hq.2.2.1.1, hq.2.2.2.1]
    have hps2 := par_le_sqrt (q.1 + q.2.1) (q.2.2.1 + q.2.2.2) ha hbpos
    have hsqrt : Real.sqrt ((q.1 + q.2.1) * (q.2.2.1 + q.2.2.2)) ^ 2
        = (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2) := Real.sq_sqrt (by positivity)
    have hpar0 : (0 : ℝ) ≤ par (q.1 + q.2.1) (q.2.2.1 + q.2.2.2) := by
      rw [par]; positivity
    have e : diamondMap q ^ 2 = par (q.1 + q.2.1) (q.2.2.1 + q.2.2.2) ^ 2 := rfl
    rw [e]
    nlinarith [hps2, hsqrt, hpar0, Real.sqrt_nonneg ((q.1 + q.2.1) * (q.2.2.1 + q.2.2.2))]
  have hval : ∫ q : ℝ × ℝ × ℝ × ℝ, (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2) / 4 ∂(prod4 (lawMeasure pd ps n))
      = (E1 pd ps n) ^ 2 := by
    rw [show (fun q : ℝ × ℝ × ℝ × ℝ => (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2) / 4)
        = (fun q : ℝ × ℝ × ℝ × ℝ => (1 / 4) * ((q.1 + q.2.1) * (q.2.2.1 + q.2.2.2))) from by
          funext q; ring,
      integral_const_mul, int_prod4_ab hpd hps hsum]
    ring
  rw [hval] at hbound
  exact hbound

omit hpd hps hsum in
/-- A general Cauchy–Schwarz inequality in squared form, proved from the nonnegativity of a
quadratic via `discrim_le_zero`. -/
lemma integral_cauchy_schwarz_sq {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (w d s : Ω → ℝ)
    (hd : Integrable d ν) (hs : Integrable s ν) (hw : Integrable w ν)
    (hint : ∀ t : ℝ, 0 ≤ᵐ[ν] fun q => d q - 2 * t * w q + t ^ 2 * s q) :
    (∫ q, w q ∂ν) ^ 2 ≤ (∫ q, d q ∂ν) * (∫ q, s q ∂ν) := by
  have key : ∀ t : ℝ, 0 ≤ (∫ q, s q ∂ν) * t ^ 2 + (-2 * (∫ q, w q ∂ν)) * t + (∫ q, d q ∂ν) := by
    intro t
    have hnn : 0 ≤ ∫ q, (d q - 2 * t * w q + t ^ 2 * s q) ∂ν := integral_nonneg_of_ae (hint t)
    have hexp : ∫ q, (d q - 2 * t * w q + t ^ 2 * s q) ∂ν
        = (∫ q, s q ∂ν) * t ^ 2 + (-2 * (∫ q, w q ∂ν)) * t + (∫ q, d q ∂ν) := by
      rw [integral_add (f := fun q => d q - 2 * t * w q) (g := fun q => t ^ 2 * s q)
            (hd.sub (hw.const_mul (2 * t))) (hs.const_mul (t ^ 2)),
          integral_sub hd (hw.const_mul (2 * t)), integral_const_mul, integral_const_mul]
      ring
    linarith [hnn, hexp]
  have hdisc := discrim_le_zero (a := ∫ q, s q ∂ν) (b := -2 * (∫ q, w q ∂ν)) (c := ∫ q, d q ∂ν)
    (fun t => by have := key t; nlinarith [this])
  simp only [discrim] at hdisc
  nlinarith [hdisc]

/-- Cauchy–Schwarz lower bound for the diamond mean:
`2·E[R]³ ≤ E[par]·(E[R²] + E[R]²)`. -/
lemma Dmean_lower (n : ℕ) : 2 * (E1 pd ps n) ^ 3 ≤ Dmean pd ps n * (E2 pd ps n + (E1 pd ps n) ^ 2) := by
  haveI := prob_law hpd hps hsum n
  set μ := lawMeasure pd ps n with hμ
  have iw : Integrable (fun q : ℝ × ℝ × ℝ × ℝ => (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2)) (prod4 μ) :=
    integrable_prod4_law hpd hps hsum n _ (by fun_prop) ((2 ^ n + 2 ^ n) * (2 ^ n + 2 ^ n))
      (fun q h1 h2 h3 h4 => by
        rw [abs_of_nonneg (mul_nonneg (by linarith [h1.1, h2.1]) (by linarith [h3.1, h4.1]))]
        exact mul_le_mul (by linarith [h1.2, h2.2]) (by linarith [h3.2, h4.2])
          (by linarith [h3.1, h4.1]) (by positivity))
  have idd : Integrable (fun q : ℝ × ℝ × ℝ × ℝ => diamondMap q) (prod4 μ) :=
    integrable_prod4_law hpd hps hsum n diamondMap measurable_diamondMap (2 ^ n)
      (fun q h1 h2 h3 h4 => by
        have hb := diamond_bounds h1.1 h1.2 h2.1 h2.2 h3.1 h3.2 h4.1 h4.2
        rw [show diamondMap q = diamondVal q.1 q.2.1 q.2.2.1 q.2.2.2 from rfl,
          abs_of_nonneg (le_trans zero_le_one hb.1)]
        exact hb.2)
  have ia2b : Integrable (fun q : ℝ × ℝ × ℝ × ℝ => (q.1 + q.2.1) ^ 2 * (q.2.2.1 + q.2.2.2)) (prod4 μ) :=
    integrable_prod4_law hpd hps hsum n _ (by fun_prop) ((2 ^ n + 2 ^ n) ^ 2 * (2 ^ n + 2 ^ n))
      (fun q h1 h2 h3 h4 => by
        rw [abs_of_nonneg (mul_nonneg (by positivity) (by linarith [h3.1, h4.1]))]
        exact mul_le_mul (by nlinarith [h1.1, h1.2, h2.1, h2.2, pow_pos (show (0:ℝ) < 2 by norm_num) n])
          (by linarith [h3.2, h4.2]) (by linarith [h3.1, h4.1]) (by positivity))
  have iab2 : Integrable (fun q : ℝ × ℝ × ℝ × ℝ => (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2) ^ 2) (prod4 μ) :=
    integrable_prod4_law hpd hps hsum n _ (by fun_prop) ((2 ^ n + 2 ^ n) * (2 ^ n + 2 ^ n) ^ 2)
      (fun q h1 h2 h3 h4 => by
        rw [abs_of_nonneg (mul_nonneg (by linarith [h1.1, h2.1]) (by positivity))]
        exact mul_le_mul (by linarith [h1.2, h2.2])
          (by nlinarith [h3.1, h3.2, h4.1, h4.2, pow_pos (show (0:ℝ) < 2 by norm_num) n])
          (by positivity) (by positivity))
  have hsrw : (fun q : ℝ × ℝ × ℝ × ℝ =>
      (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2) * ((q.1 + q.2.1) + (q.2.2.1 + q.2.2.2)))
      = (fun q : ℝ × ℝ × ℝ × ℝ =>
          (q.1 + q.2.1) ^ 2 * (q.2.2.1 + q.2.2.2) + (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2) ^ 2) := by
    funext q; ring
  have is : Integrable (fun q : ℝ × ℝ × ℝ × ℝ =>
      (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2) * ((q.1 + q.2.1) + (q.2.2.1 + q.2.2.2))) (prod4 μ) := by
    rw [hsrw]; exact ia2b.add iab2
  have hint : ∀ t : ℝ, 0 ≤ᵐ[prod4 μ]
      fun q => diamondMap q - 2 * t * ((q.1 + q.2.1) * (q.2.2.1 + q.2.2.2))
        + t ^ 2 * ((q.1 + q.2.1) * (q.2.2.1 + q.2.2.2) * ((q.1 + q.2.1) + (q.2.2.1 + q.2.2.2))) := by
    intro t
    filter_upwards [ae_box_prod4 hpd hps hsum n] with q hq
    have ha : (0 : ℝ) < q.1 + q.2.1 := by linarith [hq.1.1, hq.2.1.1]
    have hb : (0 : ℝ) < q.2.2.1 + q.2.2.2 := by linarith [hq.2.2.1.1, hq.2.2.2.1]
    have hdval : diamondMap q = (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2) / ((q.1 + q.2.1) + (q.2.2.1 + q.2.2.2)) := rfl
    rw [hdval]
    have heq : (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2) / ((q.1 + q.2.1) + (q.2.2.1 + q.2.2.2))
          - 2 * t * ((q.1 + q.2.1) * (q.2.2.1 + q.2.2.2))
          + t ^ 2 * ((q.1 + q.2.1) * (q.2.2.1 + q.2.2.2) * ((q.1 + q.2.1) + (q.2.2.1 + q.2.2.2)))
        = (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2) * (1 - t * ((q.1 + q.2.1) + (q.2.2.1 + q.2.2.2))) ^ 2
            / ((q.1 + q.2.1) + (q.2.2.1 + q.2.2.2)) := by
      field_simp; ring
    rw [heq]
    exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)) (by linarith)
  have hcs := integral_cauchy_schwarz_sq (prod4 μ)
    (fun q => (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2)) (fun q => diamondMap q)
    (fun q => (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2) * ((q.1 + q.2.1) + (q.2.2.1 + q.2.2.2)))
    idd is iw hint
  rw [int_prod4_ab hpd hps hsum] at hcs
  have hsval : (∫ q : ℝ × ℝ × ℝ × ℝ,
      (q.1 + q.2.1) * (q.2.2.1 + q.2.2.2) * ((q.1 + q.2.1) + (q.2.2.1 + q.2.2.2)) ∂(prod4 μ))
      = (2 * E2 pd ps n + 2 * (E1 pd ps n) ^ 2) * (2 * E1 pd ps n)
        + (2 * E1 pd ps n) * (2 * E2 pd ps n + 2 * (E1 pd ps n) ^ 2) := by
    rw [hsrw, integral_add ia2b iab2, int_prod4_a2b hpd hps hsum, int_prod4_ab2 hpd hps hsum]
  rw [hsval] at hcs
  have hE1 : 1 ≤ E1 pd ps n := E1_ge_one hpd hps hsum n
  have hDmean : (∫ q : ℝ × ℝ × ℝ × ℝ, diamondMap q ∂(prod4 μ)) = Dmean pd ps n := rfl
  rw [hDmean] at hcs
  nlinarith [hcs, hE1]

/-! ### The `W`-quantities and their Cauchy–Schwarz bound -/

lemma Wmean_eq (n : ℕ) : Wmean pd ps n = 2 * (E1 pd ps n * Einv pd ps n - 1) := by
  haveI := prob_law hpd hps hsum n
  set μ := (lawMeasure pd ps n).prod (lawMeasure pd ps n) with hμ
  have i1 : Integrable (fun q : ℝ × ℝ => q.1 * q.2⁻¹) μ :=
    integrable_prod_mul_law hpd hps hsum n (fun x => x) (fun y => y⁻¹) measurable_id
      measurable_id.inv (2 ^ n) 1 (fun x hx => by rw [abs_of_nonneg (by linarith [hx.1])]; exact hx.2)
      (fun x hx => by rw [abs_of_nonneg (inv_nonneg.2 (by linarith [hx.1]))]; exact inv_le_one_of_one_le₀ hx.1)
  have i2 : Integrable (fun q : ℝ × ℝ => q.2 * q.1⁻¹) μ := by
    rw [show (fun q : ℝ × ℝ => q.2 * q.1⁻¹) = (fun q : ℝ × ℝ => q.1⁻¹ * q.2) from by funext q; ring]
    exact integrable_prod_mul_law hpd hps hsum n (fun x => x⁻¹) (fun y => y) measurable_id.inv
      measurable_id 1 (2 ^ n)
      (fun x hx => by rw [abs_of_nonneg (inv_nonneg.2 (by linarith [hx.1]))]; exact inv_le_one_of_one_le₀ hx.1)
      (fun x hx => by rw [abs_of_nonneg (by linarith [hx.1])]; exact hx.2)
  have hcong : (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2 / (q.1 * q.2))
      =ᵐ[μ] (fun q : ℝ × ℝ => (q.1 * q.2⁻¹ + q.2 * q.1⁻¹) - 2) := by
    filter_upwards [ae_box_prod hpd hps hsum n] with q hq
    have hq1 : (0 : ℝ) < q.1 := by linarith [hq.1.1]
    have hq2 : (0 : ℝ) < q.2 := by linarith [hq.2.1]
    field_simp; ring
  rw [Wmean, integral_congr_ae hcong,
      integral_sub (f := fun q : ℝ × ℝ => q.1 * q.2⁻¹ + q.2 * q.1⁻¹) (g := fun _ => (2 : ℝ))
        (i1.add i2) (integrable_const _),
      integral_add (f := fun q : ℝ × ℝ => q.1 * q.2⁻¹) (g := fun q : ℝ × ℝ => q.2 * q.1⁻¹) i1 i2,
      integral_const, int_prod_mul_inv hpd hps hsum, int_prod_snd_mul_inv hpd hps hsum]
  simp only [smul_eq_mul, probReal_univ]
  ring

lemma WSmean_eq (n : ℕ) : WSmean pd ps n = 2 * (E2 pd ps n * Einv pd ps n - E1 pd ps n) := by
  haveI := prob_law hpd hps hsum n
  set μ := (lawMeasure pd ps n).prod (lawMeasure pd ps n) with hμ
  have i3 : Integrable (fun q : ℝ × ℝ => q.1 ^ 2 * q.2⁻¹) μ :=
    integrable_prod_mul_law hpd hps hsum n (fun x => x ^ 2) (fun y => y⁻¹) (by fun_prop)
      measurable_id.inv ((2 ^ n) ^ 2) 1
      (fun x hx => by rw [abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (by linarith [hx.1]) hx.2 2)
      (fun x hx => by rw [abs_of_nonneg (inv_nonneg.2 (by linarith [hx.1]))]; exact inv_le_one_of_one_le₀ hx.1)
  have i4 : Integrable (fun q : ℝ × ℝ => q.2 ^ 2 * q.1⁻¹) μ := by
    rw [show (fun q : ℝ × ℝ => q.2 ^ 2 * q.1⁻¹) = (fun q : ℝ × ℝ => q.1⁻¹ * q.2 ^ 2) from by funext q; ring]
    exact integrable_prod_mul_law hpd hps hsum n (fun x => x⁻¹) (fun y => y ^ 2) measurable_id.inv
      (by fun_prop) 1 ((2 ^ n) ^ 2)
      (fun x hx => by rw [abs_of_nonneg (inv_nonneg.2 (by linarith [hx.1]))]; exact inv_le_one_of_one_le₀ hx.1)
      (fun x hx => by rw [abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (by linarith [hx.1]) hx.2 2)
  have i5 : Integrable (fun q : ℝ × ℝ => q.1) μ :=
    integrable_prod_law hpd hps hsum n (fun q => q.1) measurable_fst (2 ^ n)
      (fun q hq1 hq2 => by rw [abs_of_nonneg (by linarith [hq1.1])]; exact hq1.2)
  have i6 : Integrable (fun q : ℝ × ℝ => q.2) μ :=
    integrable_prod_law hpd hps hsum n (fun q => q.2) measurable_snd (2 ^ n)
      (fun q hq1 hq2 => by rw [abs_of_nonneg (by linarith [hq2.1])]; exact hq2.2)
  have hcong : (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2 * (q.1 + q.2) / (q.1 * q.2))
      =ᵐ[μ] (fun q : ℝ × ℝ => (q.1 ^ 2 * q.2⁻¹ + q.2 ^ 2 * q.1⁻¹) - (q.1 + q.2)) := by
    filter_upwards [ae_box_prod hpd hps hsum n] with q hq
    have hq1 : (0 : ℝ) < q.1 := by linarith [hq.1.1]
    have hq2 : (0 : ℝ) < q.2 := by linarith [hq.2.1]
    field_simp; ring
  rw [WSmean, integral_congr_ae hcong,
      integral_sub (f := fun q : ℝ × ℝ => q.1 ^ 2 * q.2⁻¹ + q.2 ^ 2 * q.1⁻¹)
        (g := fun q : ℝ × ℝ => q.1 + q.2) (i3.add i4) (i5.add i6),
      integral_add (f := fun q : ℝ × ℝ => q.1 ^ 2 * q.2⁻¹) (g := fun q : ℝ × ℝ => q.2 ^ 2 * q.1⁻¹) i3 i4,
      integral_add (f := fun q : ℝ × ℝ => q.1) (g := fun q : ℝ × ℝ => q.2) i5 i6,
      int_prod_sq_mul_inv hpd hps hsum, int_prod_snd_sq_mul_inv hpd hps hsum,
      int_prod_fst' hpd hps hsum, int_prod_snd' hpd hps hsum]
  ring

/-- Cauchy–Schwarz: `E[W]² ≤ Δ · E[W(X+Y)]`. -/
lemma WCS_raw (n : ℕ) : (Wmean pd ps n) ^ 2 ≤ Delta pd ps n * WSmean pd ps n := by
  haveI := prob_law hpd hps hsum n
  set μ := (lawMeasure pd ps n).prod (lawMeasure pd ps n) with hμ
  -- numerator bound helper
  have hnumsq : ∀ q : ℝ × ℝ, q.1 ∈ Set.Icc (1 : ℝ) (2 ^ n) → q.2 ∈ Set.Icc (1 : ℝ) (2 ^ n) →
      (q.1 - q.2) ^ 2 ≤ ((2 : ℝ) ^ n) ^ 2 := by
    intro q hq1 hq2
    nlinarith [mul_nonneg (sub_nonneg.2 hq1.2) (sub_nonneg.2 hq2.2),
      mul_nonneg (sub_nonneg.2 hq1.1) (sub_nonneg.2 hq2.1), hq1.1, hq2.1, hq1.2, hq2.2]
  have hd : Integrable (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2 / (q.1 * q.2 * (q.1 + q.2))) μ :=
    integrable_prod_law hpd hps hsum n _ (by fun_prop) (((2 : ℝ) ^ n) ^ 2)
      (fun q hq1 hq2 => by
        have h1 : (1 : ℝ) ≤ q.1 := hq1.1
        have h2 : (1 : ℝ) ≤ q.2 := hq2.1
        rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity)), div_le_iff₀ (by positivity)]
        have hp' : (1 : ℝ) ≤ q.1 * q.2 := by
          nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
        have hp : (1 : ℝ) ≤ q.1 * q.2 * (q.1 + q.2) := by
          nlinarith [mul_le_mul_of_nonneg_right hp' (by linarith : (0 : ℝ) ≤ q.1 + q.2), h1, h2]
        calc (q.1 - q.2) ^ 2 ≤ ((2 : ℝ) ^ n) ^ 2 := hnumsq q hq1 hq2
          _ ≤ ((2 : ℝ) ^ n) ^ 2 * (q.1 * q.2 * (q.1 + q.2)) := le_mul_of_one_le_right (by positivity) hp)
  have hw : Integrable (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2 / (q.1 * q.2)) μ :=
    integrable_prod_law hpd hps hsum n _ (by fun_prop) (((2 : ℝ) ^ n) ^ 2)
      (fun q hq1 hq2 => by
        have h1 : (1 : ℝ) ≤ q.1 := hq1.1
        have h2 : (1 : ℝ) ≤ q.2 := hq2.1
        rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity)), div_le_iff₀ (by positivity)]
        have hp : (1 : ℝ) ≤ q.1 * q.2 := by
          nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
        calc (q.1 - q.2) ^ 2 ≤ ((2 : ℝ) ^ n) ^ 2 := hnumsq q hq1 hq2
          _ ≤ ((2 : ℝ) ^ n) ^ 2 * (q.1 * q.2) := le_mul_of_one_le_right (by positivity) hp)
  have hs : Integrable (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2 * (q.1 + q.2) / (q.1 * q.2)) μ :=
    integrable_prod_law hpd hps hsum n _ (by fun_prop) (2 * ((2 : ℝ) ^ n) ^ 3)
      (fun q hq1 hq2 => by
        have h1 : (1 : ℝ) ≤ q.1 := hq1.1
        have h2 : (1 : ℝ) ≤ q.2 := hq2.1
        rw [abs_of_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by positivity)),
          div_le_iff₀ (by positivity)]
        have hp : (1 : ℝ) ≤ q.1 * q.2 := by
          nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
        have hsum2 : q.1 + q.2 ≤ 2 * (2 : ℝ) ^ n := by linarith [hq1.2, hq2.2]
        calc (q.1 - q.2) ^ 2 * (q.1 + q.2)
            ≤ ((2 : ℝ) ^ n) ^ 2 * (2 * (2 : ℝ) ^ n) := by
              apply mul_le_mul (hnumsq q hq1 hq2) hsum2 (by linarith) (by positivity)
          _ = 2 * ((2 : ℝ) ^ n) ^ 3 := by ring
          _ ≤ 2 * ((2 : ℝ) ^ n) ^ 3 * (q.1 * q.2) := le_mul_of_one_le_right (by positivity) hp)
  have hint : ∀ t : ℝ, 0 ≤ᵐ[μ]
      fun q => (q.1 - q.2) ^ 2 / (q.1 * q.2 * (q.1 + q.2)) - 2 * t * ((q.1 - q.2) ^ 2 / (q.1 * q.2))
        + t ^ 2 * ((q.1 - q.2) ^ 2 * (q.1 + q.2) / (q.1 * q.2)) := by
    intro t
    filter_upwards [ae_box_prod hpd hps hsum n] with q hq
    have h1 : (0 : ℝ) < q.1 := by linarith [hq.1.1]
    have h2 : (0 : ℝ) < q.2 := by linarith [hq.2.1]
    have hs2 : (0 : ℝ) < q.1 + q.2 := by linarith
    have heq : (q.1 - q.2) ^ 2 / (q.1 * q.2 * (q.1 + q.2)) - 2 * t * ((q.1 - q.2) ^ 2 / (q.1 * q.2))
        + t ^ 2 * ((q.1 - q.2) ^ 2 * (q.1 + q.2) / (q.1 * q.2))
        = (q.1 - q.2) ^ 2 * (1 - t * (q.1 + q.2)) ^ 2 / (q.1 * q.2 * (q.1 + q.2)) := by
      field_simp; ring
    rw [heq]
    exact div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity)
  have hcs := integral_cauchy_schwarz_sq μ (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2 / (q.1 * q.2))
    (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2 / (q.1 * q.2 * (q.1 + q.2)))
    (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2 * (q.1 + q.2) / (q.1 * q.2)) hd hs hw hint
  rw [Wmean, Delta, WSmean]
  exact hcs

/-- Clean form: `2(E[R]E[1/R] − 1)² ≤ Δ·(E[R²]E[1/R] − E[R])`. -/
lemma WCS (n : ℕ) :
    2 * (E1 pd ps n * Einv pd ps n - 1) ^ 2 ≤
      Delta pd ps n * (E2 pd ps n * Einv pd ps n - E1 pd ps n) := by
  have hraw := WCS_raw hpd hps hsum n
  rw [Wmean_eq hpd hps hsum, WSmean_eq hpd hps hsum] at hraw
  nlinarith [hraw]

/-! ### The relative second moment bound and the uniform product-moment bound -/

/-- **Relative second-moment bound (paper Lemma 4.5, Case 1).** In the regime `pd ≤ 1/2`
the relative second moment stays bounded: `E[R²] ≤ 2·E[R]²`. -/
lemma E2_le_two_E1sq (hhalf : pd ≤ 1 / 2) (n : ℕ) :
    E2 pd ps n ≤ 2 * (E1 pd ps n) ^ 2 := by
  induction n with
  | zero => norm_num [E1, E2, integral_dirac]
  | succ n ih =>
    have ha : 1 ≤ E1 pd ps n := E1_ge_one hpd hps hsum n
    have hapos : 0 < E1 pd ps n := by linarith
    have hcge : (E1 pd ps n) ^ 2 ≤ E2 pd ps n := E2_ge_E1sq hpd hps hsum n
    have hlower := Dmean_lower hpd hps hsum n
    have hDsq := Dsq_le_E1sq hpd hps hsum n
    have hE2s := E2_succ hpd hps hsum n
    have hE1s := E1_succ hpd hps hsum n
    -- lower bound on the diamond mean
    have hca : 0 < E2 pd ps n + (E1 pd ps n) ^ 2 := by nlinarith [hcge, sq_nonneg (E1 pd ps n), hapos]
    have hDmean_pos : 0 < Dmean pd ps n := by nlinarith [hlower, hca, ha, hapos]
    have h3a2 : E2 pd ps n + (E1 pd ps n) ^ 2 ≤ 3 * (E1 pd ps n) ^ 2 := by nlinarith [ih]
    have hkey : Dmean pd ps n * (E2 pd ps n + (E1 pd ps n) ^ 2)
        ≤ Dmean pd ps n * (3 * (E1 pd ps n) ^ 2) :=
      mul_le_mul_of_nonneg_left h3a2 hDmean_pos.le
    have hD_lb : 2 * E1 pd ps n / 3 ≤ Dmean pd ps n := by
      nlinarith [hlower, hkey, hapos, mul_pos hapos hapos]
    have hE1s_lb : 2 * E1 pd ps n * (ps + pd / 3) ≤ E1 pd ps (n + 1) := by
      rw [hE1s]; nlinarith [hD_lb, hpd, hps, hapos]
    have hpos_lb : 0 ≤ 2 * E1 pd ps n * (ps + pd / 3) := by
      have : 0 ≤ ps + pd / 3 := by linarith
      positivity
    have hE2s_ub : E2 pd ps (n + 1) ≤ (6 * ps + pd) * (E1 pd ps n) ^ 2 := by
      rw [hE2s]; nlinarith [ih, hDsq, hps, hpd]
    have hpoly : 6 * ps + pd ≤ 8 * (ps + pd / 3) ^ 2 := by
      nlinarith [hpd, hhalf, hsum, mul_nonneg (sub_nonneg.2 hhalf) hpd, sq_nonneg pd]
    have hchain : (6 * ps + pd) * (E1 pd ps n) ^ 2 ≤ 2 * (E1 pd ps (n + 1)) ^ 2 := by
      have h1 : (6 * ps + pd) * (E1 pd ps n) ^ 2 ≤ 8 * (ps + pd / 3) ^ 2 * (E1 pd ps n) ^ 2 := by
        nlinarith [hpoly, sq_nonneg (E1 pd ps n)]
      have h3 : 2 * (2 * E1 pd ps n * (ps + pd / 3)) ^ 2 ≤ 2 * (E1 pd ps (n + 1)) ^ 2 := by
        nlinarith [hE1s_lb, hpos_lb]
      nlinarith [h1, h3]
    linarith [hE2s_ub, hchain]

/-- **Uniform product-moment bound (paper Lemma 4.4).** In the regime `pd ≤ 1/2` we have
`E[R n]·E[1/R n] ≤ 11/5` for every `n`. -/
lemma E1Einv_le (hhalf : pd ≤ 1 / 2) (n : ℕ) :
    E1 pd ps n * Einv pd ps n ≤ 11 / 5 := by
  induction n with
  | zero => norm_num [E1, Einv, integral_dirac]
  | succ n ih =>
    have ha : 1 ≤ E1 pd ps n := E1_ge_one hpd hps hsum n
    have hb : 0 < Einv pd ps n := Einv_pos hpd hps hsum n
    have hP1 : 1 ≤ E1 pd ps n * Einv pd ps n := E1Einv_ge_one hpd hps hsum n
    have hc2 : E2 pd ps n ≤ 2 * (E1 pd ps n) ^ 2 := E2_le_two_E1sq hpd hps hsum hhalf n
    have hWCS := WCS hpd hps hsum n
    have hDnn : 0 ≤ Delta pd ps n := Delta_nonneg hpd hps hsum n
    have hDmean := Dmean_le_E1 hpd hps hsum n
    have hE1s := E1_succ hpd hps hsum n
    have hEinvval : Einv pd ps (n + 1) = (1 + pd) * (Einv pd ps n / 2 - Delta pd ps n / 4) := by
      rw [Einv_succ hpd hps hsum n, Sinv_eq hpd hps hsum n]
    have hE1pos : 0 ≤ E1 pd ps (n + 1) := le_trans zero_le_one (E1_ge_one hpd hps hsum (n + 1))
    have hEinvpos : 0 ≤ Einv pd ps (n + 1) := (Einv_pos hpd hps hsum (n + 1)).le
    have hE1ub : E1 pd ps (n + 1) ≤ (1 + ps) * E1 pd ps n := by
      rw [hE1s]; nlinarith [hDmean, hpd, hsum, ha]
    -- one-step product bound
    have hmul1 : E1 pd ps (n + 1) * Einv pd ps (n + 1)
        ≤ (1 + ps) * E1 pd ps n * ((1 + pd) * (Einv pd ps n / 2 - Delta pd ps n / 4)) := by
      calc E1 pd ps (n + 1) * Einv pd ps (n + 1)
          ≤ (1 + ps) * E1 pd ps n * Einv pd ps (n + 1) :=
            mul_le_mul_of_nonneg_right hE1ub hEinvpos
        _ = (1 + ps) * E1 pd ps n * ((1 + pd) * (Einv pd ps n / 2 - Delta pd ps n / 4)) := by
            rw [hEinvval]
    -- the WCS-based lower bound on Delta, in cleared (division-free) form
    have hcble : E2 pd ps n * Einv pd ps n - E1 pd ps n
        ≤ E1 pd ps n * (2 * (E1 pd ps n * Einv pd ps n) - 1) := by nlinarith [hc2, hb.le, ha]
    have hΔmul : 2 * (E1 pd ps n * Einv pd ps n - 1) ^ 2
        ≤ Delta pd ps n * (E1 pd ps n * (2 * (E1 pd ps n * Einv pd ps n) - 1)) := by
      calc 2 * (E1 pd ps n * Einv pd ps n - 1) ^ 2
          ≤ Delta pd ps n * (E2 pd ps n * Einv pd ps n - E1 pd ps n) := hWCS
        _ ≤ Delta pd ps n * (E1 pd ps n * (2 * (E1 pd ps n * Einv pd ps n) - 1)) :=
            mul_le_mul_of_nonneg_left hcble hDnn
    have h2ab : 0 < 2 * (E1 pd ps n * Einv pd ps n) - 1 := by linarith [hP1]
    have hKpos : 0 ≤ (1 + ps) * (1 + pd) / 2 := by positivity
    have hKbound : (1 + ps) * (1 + pd) / 2 ≤ 9 / 8 := by nlinarith [hpd, hhalf, hsum, sq_nonneg (2 * pd - 1)]
    -- abbreviation: the (cleared) one-step inequality multiplied through by (2ab-1)
    have hRHS : (E1 pd ps n * Einv pd ps n - E1 pd ps n * Delta pd ps n / 2)
          * (2 * (E1 pd ps n * Einv pd ps n) - 1)
        ≤ (E1 pd ps n * Einv pd ps n) ^ 2 + E1 pd ps n * Einv pd ps n - 1 := by
      nlinarith [hΔmul]
    have hstep : E1 pd ps (n + 1) * Einv pd ps (n + 1) * (2 * (E1 pd ps n * Einv pd ps n) - 1)
        ≤ ((1 + ps) * (1 + pd) / 2)
            * ((E1 pd ps n * Einv pd ps n) ^ 2 + E1 pd ps n * Einv pd ps n - 1) := by
      calc E1 pd ps (n + 1) * Einv pd ps (n + 1) * (2 * (E1 pd ps n * Einv pd ps n) - 1)
          ≤ ((1 + ps) * E1 pd ps n * ((1 + pd) * (Einv pd ps n / 2 - Delta pd ps n / 4)))
              * (2 * (E1 pd ps n * Einv pd ps n) - 1) :=
            mul_le_mul_of_nonneg_right hmul1 h2ab.le
        _ = ((1 + ps) * (1 + pd) / 2)
              * ((E1 pd ps n * Einv pd ps n - E1 pd ps n * Delta pd ps n / 2)
                  * (2 * (E1 pd ps n * Einv pd ps n) - 1)) := by ring
        _ ≤ ((1 + ps) * (1 + pd) / 2)
              * ((E1 pd ps n * Einv pd ps n) ^ 2 + E1 pd ps n * Einv pd ps n - 1) :=
            mul_le_mul_of_nonneg_left hRHS hKpos
    -- the polynomial logistic bound
    have hquad : ((1 + ps) * (1 + pd) / 2)
          * ((E1 pd ps n * Einv pd ps n) ^ 2 + E1 pd ps n * Einv pd ps n - 1)
        ≤ 11 / 5 * (2 * (E1 pd ps n * Einv pd ps n) - 1) := by
      nlinarith [hKbound, hKpos, hP1, ih,
        mul_nonneg (sub_nonneg.2 ih) (sub_nonneg.2 hP1), sq_nonneg (E1 pd ps n * Einv pd ps n)]
    -- conclude
    nlinarith [hstep, hquad, h2ab]

end Recursions

/-- The uniform product-moment bound, packaged as existence of a constant `M`. -/
lemma uniform_product (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) (hhalf : pd ≤ 1 / 2) :
    ∃ M : ℝ, ∀ n, E1 pd ps n * Einv pd ps n ≤ M :=
  ⟨11 / 5, fun n => E1Einv_le hpd hps hsum hhalf n⟩

end

end Reduced