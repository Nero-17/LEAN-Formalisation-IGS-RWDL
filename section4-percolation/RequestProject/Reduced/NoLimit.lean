import RequestProject.Reduced.Process
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# No deterministic limit (Proposition 4.8)

This file formalises the proposition of Subsection 4.1 giving a partial negative answer to the
Hambly–Kumagai question "if there is exponential growth, is there a limit distribution such that
`R_n λ^n → c`?".

**Statement.** Assume `p_series, p_diamond ∈ (0,1)`.  For `λ > 0` put `Z_n = λ^n R_n`.  If `Z_n`
converges in distribution to a deterministic constant `c ≥ 0`, then `c = 0`.

We model "convergence in distribution to the constant `c`" by its defining property: the integral
of every bounded continuous function `f` against the law of `Z_n` converges to `f c`
(`= ∫ f d δ_c`).

The proof follows the paper.  Writing `ν_n` for the law of `Z_n`, the one-step distributional
recursion gives, for every bounded continuous `f`,
`∫ f dν_{n+1} = p_series · ∫ f(λ(a+b)) d(ν_n ⊗ ν_n) + p_diamond · ∫ f(λ·diamond) d(ν_n^{⊗4})`.
If `ν_n → δ_c` weakly with `c > 0`, the series term tends to `f(2λc)` and the diamond term tends
to `f(λc)` (continuous–mapping theorem, with a truncation argument handling the singularity of the
parallel map at the origin, valid since `c > 0`).  Hence
`f c = p_series · f(2λc) + p_diamond · f(λc)` for every bounded continuous `f`.  Choosing a tent
function that is `1` at `c` and `0` at whichever of `2λc`, `λc` differs from `c` (one of them does,
since `2λc ≠ λc` for `c > 0`) contradicts `p_series, p_diamond > 0` unless `c = 0`.
-/

namespace Reduced

open MeasureTheory Measure Real Set Filter Topology BoundedContinuousFunction

noncomputable section

/-! ## A point mass as a probability measure, and weak-convergence helpers -/

/-- A Dirac point mass packaged as a `ProbabilityMeasure`. -/
noncomputable def diracProb (a : ℝ) : ProbabilityMeasure ℝ := ⟨Measure.dirac a, inferInstance⟩

@[simp] lemma diracProb_toMeasure (a : ℝ) : (diracProb a).toMeasure = Measure.dirac a := rfl

/-- The four-fold product of a probability measure on `ℝ`. -/
noncomputable def Prob4 (μ : ProbabilityMeasure ℝ) : ProbabilityMeasure (ℝ × ℝ × ℝ × ℝ) :=
  μ.prod (μ.prod (μ.prod μ))

lemma Prob4_toMeasure (μ : ProbabilityMeasure ℝ) :
    (Prob4 μ).toMeasure = prod4 μ.toMeasure := by
  simp [Prob4, prod4, ProbabilityMeasure.toMeasure_prod]

/-- Weak convergence to `δ_a`: integral of a bounded continuous function converges to `f a`. -/
lemma weak_int_tendsto {μ : ℕ → ProbabilityMeasure ℝ} {a : ℝ}
    (h : Tendsto μ atTop (𝓝 (diracProb a))) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, f x ∂(μ n).toMeasure) atTop (𝓝 (f a)) := by
  have hh := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h) f
  simpa [diracProb, integral_dirac] using hh

/-- If `μ_n → δ_a` weakly then `μ_n ⊗ μ_n → δ_{(a,a)}` weakly. -/
lemma prod_tendsto {μ : ℕ → ProbabilityMeasure ℝ} {a : ℝ}
    (h : Tendsto μ atTop (𝓝 (diracProb a))) :
    Tendsto (fun n => (μ n).prod (μ n)) atTop (𝓝 (diracProb a |>.prod (diracProb a))) := by
  exact (ProbabilityMeasure.continuous_prod.tendsto _).comp (h.prodMk_nhds h)

/-
If `μ_n → δ_a` weakly then `Prob4 μ_n → δ_{(a,a,a,a)}` weakly.
-/
lemma prob4_tendsto {μ : ℕ → ProbabilityMeasure ℝ} {a : ℝ}
    (h : Tendsto μ atTop (𝓝 (diracProb a))) :
    Tendsto (fun n => Prob4 (μ n)) atTop
      (𝓝 (Prob4 (diracProb a))) := by
  convert ( ProbabilityMeasure.continuous_prod.tendsto _ ).comp ( h.prodMk_nhds <| ?_ ) using 1;
  all_goals try infer_instance;
  convert ( ProbabilityMeasure.continuous_prod.tendsto _ ).comp ( h.prodMk_nhds ( ( ProbabilityMeasure.continuous_prod.tendsto _ ).comp ( h.prodMk_nhds h ) ) ) using 1

/-
Weak convergence on the 4-fold product: integral of a bounded continuous function on `ℝ⁴`
converges to its value at `(a,a,a,a)`.
-/
lemma weak4_int_tendsto {μ : ℕ → ProbabilityMeasure ℝ} {a : ℝ}
    (h : Tendsto μ atTop (𝓝 (diracProb a))) (g : (ℝ × ℝ × ℝ × ℝ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ q, g q ∂(prod4 (μ n).toMeasure)) atTop (𝓝 (g (a, a, a, a))) := by
  have := @prob4_tendsto;
  specialize @this μ a h;
  have h_weak_conv : ∫ q, g q ∂(Prob4 (diracProb a)).toMeasure = g (a, a, a, a) := by
    unfold Prob4 diracProb; simp +decide [ MeasureTheory.Measure.dirac_prod_dirac ] ;
  convert h_weak_conv ▸ ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp this g using 1

/-
Weak convergence on the 2-fold product.
-/
lemma weak2_int_tendsto {μ : ℕ → ProbabilityMeasure ℝ} {a : ℝ}
    (h : Tendsto μ atTop (𝓝 (diracProb a))) (g : (ℝ × ℝ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ q, g q ∂((μ n).toMeasure.prod (μ n).toMeasure)) atTop
      (𝓝 (g (a, a))) := by
  have := @prod_tendsto;
  convert ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp ( this h ) g using 1;
  simp +decide [ diracProb, MeasureTheory.Measure.dirac_prod_dirac ]

/-! ## The series and diamond limits -/

/-- The scaled series map `(a,b) ↦ λ(a+b)`. -/
def seriesScaled (lam : ℝ) (q : ℝ × ℝ) : ℝ := lam * (q.1 + q.2)

/-- The scaled diamond map `q ↦ λ · diamondVal q`. -/
noncomputable def diamondScaled (lam : ℝ) (q : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  lam * diamondVal q.1 q.2.1 q.2.2.1 q.2.2.2

lemma continuous_seriesScaled (lam : ℝ) : Continuous (seriesScaled lam) := by
  unfold seriesScaled; fun_prop

/-- Homogeneity of the parallel map: `par (t a) (t b) = t · par a b` for `0 ≤ t`. -/
lemma par_smul (t a b : ℝ) : par (t * a) (t * b) = t * par a b := by
  unfold par
  by_cases ht : t = 0
  · simp [ht]
  · by_cases hab : a + b = 0
    · have h2 : t * a + t * b = 0 := by rw [← mul_add, hab, mul_zero]
      rw [h2, hab]; simp
    · have h2 : t * a + t * b ≠ 0 := by rw [← mul_add]; exact mul_ne_zero ht hab
      rw [show t * a + t * b = t * (a + b) by ring]
      field_simp

/-
The **series limit**: if `ν_n → δ_c`, then `∫ f(λ(a+b)) d(ν_n⊗ν_n) → f(2λc)`.
-/
lemma series_limit {μ : ℕ → ProbabilityMeasure ℝ} {c lam : ℝ}
    (h : Tendsto μ atTop (𝓝 (diracProb c))) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ q, f (seriesScaled lam q) ∂((μ n).toMeasure.prod (μ n).toMeasure)) atTop
      (𝓝 (f (2 * lam * c))) := by
  convert weak2_int_tendsto h ( f.compContinuous ⟨ seriesScaled lam, continuous_seriesScaled lam ⟩ ) using 1;
  unfold seriesScaled; ring;
  norm_num [ mul_two, mul_add ]

/-- A globally continuous truncation of the scaled diamond map, replacing the denominator
`s + t` by `max (s + t) thr` so that there is no singularity. -/
noncomputable def diamondSafe (lam thr : ℝ) (q : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  lam * ((q.1 + q.2.1) * (q.2.2.1 + q.2.2.2))
    / max (q.1 + q.2.1 + q.2.2.1 + q.2.2.2) thr

lemma continuous_diamondSafe (lam : ℝ) {thr : ℝ} (hthr : 0 < thr) :
    Continuous (diamondSafe lam thr) := by
  unfold diamondSafe
  have hden : ∀ q : ℝ × ℝ × ℝ × ℝ,
      max (q.1 + q.2.1 + q.2.2.1 + q.2.2.2) thr ≠ 0 := by
    intro q; exact ne_of_gt (lt_of_lt_of_le hthr (le_max_right _ _))
  fun_prop (disch := assumption)

/-- On the region `thr ≤ s + t`, the safe map agrees with the genuine scaled diamond map. -/
lemma diamondSafe_eq (lam thr : ℝ) {q : ℝ × ℝ × ℝ × ℝ}
    (h : thr ≤ q.1 + q.2.1 + q.2.2.1 + q.2.2.2) :
    diamondSafe lam thr q = diamondScaled lam q := by
  unfold diamondSafe diamondScaled diamondVal par
  rw [max_eq_left h]
  ring

/-- The value of the safe map at the diagonal point `(c,c,c,c)` is `λc`, provided `thr ≤ 4c` and
`0 < c`. -/
lemma diamondSafe_at (lam : ℝ) {c thr : ℝ} (hc : 0 < c) (h4 : thr ≤ 4 * c) :
    diamondSafe lam thr (c, c, c, c) = lam * c := by
  unfold diamondSafe
  have : max (c + c + c + c) thr = 4 * c := by
    rw [max_eq_left (by linarith)]; ring
  rw [this]
  field_simp
  ring

/-
A bump function on `ℝ⁴` (depending only on the coordinate sum): values in `[0,1]`, equal to
`1` where the sum is `< thr`, and `0` where the sum is `≥ 2·thr`.
-/
lemma exists_bump4 {thr : ℝ} (hthr : 0 < thr) :
    ∃ φ : (ℝ × ℝ × ℝ × ℝ) →ᵇ ℝ,
      (∀ q, 0 ≤ φ q) ∧ (∀ q, φ q ≤ 1) ∧
      (∀ q, q.1 + q.2.1 + q.2.2.1 + q.2.2.2 < thr → (1 : ℝ) ≤ φ q) ∧
      (∀ q, 2 * thr ≤ q.1 + q.2.1 + q.2.2.1 + q.2.2.2 → φ q = 0) := by
  refine' ⟨ _, _, _, _, _ ⟩;
  refine' ⟨ _, _ ⟩;
  refine' ⟨ fun q => Max.max 0 ( Min.min 1 ( ( 2 * thr - ( q.1 + q.2.1 + q.2.2.1 + q.2.2.2 ) ) / thr ) ), _ ⟩;
  fun_prop;
  refine' ⟨ 1, fun x y => _ ⟩;
  all_goals norm_num [ dist_eq_norm ];
  · grind;
  · exact fun a b c d h => by rw [ le_div_iff₀ hthr ] ; linarith;
  · exact fun a b c d h => div_nonpos_of_nonpos_of_nonneg ( by linarith ) hthr.le

/-
The **diamond limit**: if `ν_n → δ_c` with `c > 0`, then
`∫ f(λ·diamond) d(ν_n^{⊗4}) → f(λc)`.  (`diamondVal c c c c = c`.)
-/
lemma diamond_limit {μ : ℕ → ProbabilityMeasure ℝ} {c lam : ℝ}
    (hc : 0 < c) (h : Tendsto μ atTop (𝓝 (diracProb c))) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ q, f (diamondScaled lam q) ∂(prod4 (μ n).toMeasure)) atTop
      (𝓝 (f (lam * c))) := by
  obtain ⟨ φ, hφ0, hφ1, hφlt, hφge ⟩ := exists_bump4 hc;
  -- Apply the weak convergence result to the integral of the difference.
  have h_diff : Filter.Tendsto (fun n => ∫ q, (f (diamondScaled lam q) - f (diamondSafe lam c q)) ∂(prod4 (μ n).toMeasure)) Filter.atTop (nhds 0) := by
    have h_diff : ∀ q, |f (diamondScaled lam q) - f (diamondSafe lam c q)| ≤ 2 * ‖f‖ * φ q := by
      intro q
      by_cases hq : q.1 + q.2.1 + q.2.2.1 + q.2.2.2 < c;
      · refine' le_trans ( abs_sub _ _ ) _;
        exact le_trans ( add_le_add ( f.norm_coe_le_norm _ ) ( f.norm_coe_le_norm _ ) ) ( by nlinarith [ hφ0 q, hφ1 q, hφlt q hq, norm_nonneg f ] );
      · rw [ show diamondScaled lam q = diamondSafe lam c q from _ ];
        · norm_num;
          exact mul_nonneg ( mul_nonneg zero_le_two ( norm_nonneg _ ) ) ( hφ0 q );
        · exact Eq.symm ( diamondSafe_eq lam c ( by linarith ) );
    have h_diff : Filter.Tendsto (fun n => ∫ q, 2 * ‖f‖ * φ q ∂(prod4 (μ n).toMeasure)) Filter.atTop (nhds 0) := by
      convert Tendsto.const_mul ( 2 * ‖f‖ ) ( weak4_int_tendsto h φ ) using 2;
      · rw [ MeasureTheory.integral_const_mul ];
      · grind +splitImp;
    refine' squeeze_zero_norm ( fun n => MeasureTheory.norm_integral_le_integral_norm _ |> le_trans <| MeasureTheory.integral_mono_of_nonneg _ _ _ ) h_diff;
    · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
    · refine' MeasureTheory.Integrable.const_mul _ _;
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun q => 1;
      · unfold prod4; norm_num;
      · exact φ.continuous.aestronglyMeasurable;
      · exact Filter.Eventually.of_forall fun q => abs_le.mpr ⟨ by linarith [ hφ0 q ], by linarith [ hφ1 q ] ⟩;
    · filter_upwards [ ] using by assumption;
  convert h_diff.add ( weak4_int_tendsto h ( f.compContinuous ⟨ diamondSafe lam c, continuous_diamondSafe lam hc ⟩ ) ) using 2 <;> norm_num;
  · rw [ MeasureTheory.integral_sub ];
    · ring;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun q => ‖f‖;
      · simp +decide [ prod4 ];
      · exact f.continuous.comp_aestronglyMeasurable ( measurable_diamondMap.const_mul _ |> Measurable.aestronglyMeasurable );
      · exact Filter.Eventually.of_forall fun x => f.norm_coe_le_norm _;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun q => ‖f‖;
      · simp +decide [ prod4 ];
      · exact f.continuous.comp_aestronglyMeasurable ( continuous_diamondSafe lam hc |> Continuous.aestronglyMeasurable );
      · exact Filter.Eventually.of_forall fun x => f.norm_coe_le_norm _;
  · rw [ diamondSafe_at lam hc ( by linarith ) ]

/-! ## The law of `Z_n` and the one-step recursion -/

variable {pd ps : ℝ}

/-- The law of `Z_n = λ^n R_n`. -/
noncomputable def zMeasure (pd ps lam : ℝ) (n : ℕ) : Measure ℝ :=
  (lawMeasure pd ps n).map (fun x => lam ^ n * x)

lemma isProb_zMeasure (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) (lam : ℝ) (n : ℕ) :
    IsProbabilityMeasure (zMeasure pd ps lam n) := by
  haveI := isProb_lawMeasure hpd hps hsum n
  unfold zMeasure
  exact isProbabilityMeasure_map (by fun_prop)

/-- `Z_n` packaged as a `ProbabilityMeasure`. -/
noncomputable def zProb (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) (lam : ℝ) (n : ℕ) :
    ProbabilityMeasure ℝ :=
  ⟨zMeasure pd ps lam n, isProb_zMeasure hpd hps hsum lam n⟩

/-
The two-fold product of `zMeasure` is the scaled product of `lawMeasure`.
-/
lemma prod_zMeasure_eq (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) (lam : ℝ) (n : ℕ) :
    (zMeasure pd ps lam n).prod (zMeasure pd ps lam n)
      = ((lawMeasure pd ps n).prod (lawMeasure pd ps n)).map
          (fun q : ℝ × ℝ => (lam ^ n * q.1, lam ^ n * q.2)) := by
  convert MeasureTheory.Measure.map_prod_map _ _ _ _ using 1;
  · have := isProb_lawMeasure hpd hps hsum n;
    infer_instance;
  · have := isProb_lawMeasure hpd hps hsum n;
    infer_instance;
  · exact measurable_const.mul measurable_id;
  · exact measurable_const.mul measurable_id

/-
The four-fold product of `zMeasure` is the scaled four-fold product of `lawMeasure`.
-/
lemma prod4_zMeasure_eq (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) (lam : ℝ) (n : ℕ) :
    prod4 (zMeasure pd ps lam n)
      = (prod4 (lawMeasure pd ps n)).map
          (fun q : ℝ × ℝ × ℝ × ℝ =>
            (lam ^ n * q.1, lam ^ n * q.2.1, lam ^ n * q.2.2.1, lam ^ n * q.2.2.2)) := by
  haveI := isProb_lawMeasure hpd hps hsum n;
  unfold prod4 zMeasure; rw [ MeasureTheory.Measure.map_prod_map ] ;
  · rw [ MeasureTheory.Measure.map_prod_map ];
    · rw [ MeasureTheory.Measure.map_prod_map ];
      · rfl;
      · exact measurable_const.mul measurable_id;
      · fun_prop;
    · exact measurable_const.mul measurable_id;
    · exact measurable_fst.const_mul _ |> Measurable.prodMk <| measurable_snd.const_mul _;
  · exact measurable_const.mul measurable_id;
  · exact measurable_const.mul measurable_id

/-
Series term: rewrite the scaled-product integral over `zMeasure` as an integral over the
product of `lawMeasure` with the integrand at scale `lam ^ (n+1)`.
-/
lemma zMeasure_succ_series (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1)
    (lam : ℝ) (n : ℕ) (f : ℝ →ᵇ ℝ) :
    (∫ q, f (seriesScaled lam q) ∂((zMeasure pd ps lam n).prod (zMeasure pd ps lam n)))
      = ∫ q, f (lam ^ (n + 1) * (q.1 + q.2))
            ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n)) := by
  rw [ prod_zMeasure_eq hpd hps hsum lam n, MeasureTheory.integral_map ];
  · congr; ext; rw [ seriesScaled ] ; ring;
  · fun_prop;
  · exact Continuous.aestronglyMeasurable ( f.continuous.comp ( continuous_seriesScaled lam ) )

/-
Diamond term: rewrite the scaled four-fold-product integral over `zMeasure` as an integral
over the four-fold product of `lawMeasure` with the integrand at scale `lam ^ (n+1)`.
-/
lemma zMeasure_succ_diamond (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1)
    (lam : ℝ) (n : ℕ) (f : ℝ →ᵇ ℝ) :
    (∫ q, f (diamondScaled lam q) ∂(prod4 (zMeasure pd ps lam n)))
      = ∫ q, f (lam ^ (n + 1) * diamondMap q) ∂(prod4 (lawMeasure pd ps n)) := by
  rw [ prod4_zMeasure_eq hpd hps hsum lam n, MeasureTheory.integral_map ];
  · unfold diamondScaled diamondMap;
    unfold diamondVal; ring;
    simp +decide only [← mul_add, par_smul, mul_assoc];
  · fun_prop;
  · refine' Measurable.aestronglyMeasurable _;
    exact f.continuous.measurable.comp ( measurable_diamondMap.const_mul _ )

/-
The LHS one-step recursion at scale `lam ^ (n+1)`, in terms of `lawMeasure`.
-/
lemma zMeasure_succ_lhs (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1)
    (lam : ℝ) (n : ℕ) (f : ℝ →ᵇ ℝ) :
    ∫ x, f x ∂(zMeasure pd ps lam (n + 1))
      = ps * (∫ q, f (lam ^ (n + 1) * (q.1 + q.2))
            ∂((lawMeasure pd ps n).prod (lawMeasure pd ps n)))
        + pd * (∫ q, f (lam ^ (n + 1) * diamondMap q) ∂(prod4 (lawMeasure pd ps n))) := by
  have h_eq : ∫ x, f x ∂(zMeasure pd ps lam (n + 1)) = ∫ y, f (lam ^ (n + 1) * y) ∂(lawMeasure pd ps (n + 1)) := by
    erw [ MeasureTheory.integral_map ];
    · exact measurable_const.mul measurable_id |> Measurable.aemeasurable;
    · exact f.continuous.aestronglyMeasurable;
  rw [ h_eq, lawMeasure_succ, MeasureTheory.integral_add_measure, MeasureTheory.integral_smul_measure, MeasureTheory.integral_smul_measure ];
  · rw [ ENNReal.toReal_ofReal hps, ENNReal.toReal_ofReal hpd, MeasureTheory.integral_map, MeasureTheory.integral_map ];
    · rfl;
    · exact measurable_diamondMap.aemeasurable;
    · exact Continuous.aestronglyMeasurable ( f.continuous.comp ( continuous_const.mul continuous_id' ) );
    · exact measurable_seriesMap.aemeasurable;
    · exact Continuous.aestronglyMeasurable ( f.continuous.comp ( continuous_const.mul continuous_id' ) );
  · refine' MeasureTheory.Integrable.smul_measure _ _;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun x => ‖f‖;
      · have := isProb_lawMeasure hpd hps hsum n;
        simp +decide [ this.measure_univ ];
      · exact Continuous.aestronglyMeasurable ( f.continuous.comp ( continuous_const.mul continuous_id' ) );
      · exact Filter.Eventually.of_forall fun x => f.norm_coe_le_norm _;
    · norm_num;
  · refine' MeasureTheory.Integrable.smul_measure _ _;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun x => ‖f‖;
      · simp +decide [ prod4 ];
        have := isProb_lawMeasure hpd hps hsum n;
        simp +decide [ MeasureTheory.Measure.prod_apply, this.measure_univ ];
      · exact f.continuous.comp_aestronglyMeasurable ( measurable_const.mul measurable_id' |> Measurable.aestronglyMeasurable );
      · exact Filter.Eventually.of_forall fun x => f.norm_coe_le_norm _;
    · norm_num

/-- **One-step recursion** for the law of `Z_n`, integrated against a bounded continuous function.
-/
lemma zMeasure_succ_integral (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1)
    (lam : ℝ) (n : ℕ) (f : ℝ →ᵇ ℝ) :
    ∫ x, f x ∂(zMeasure pd ps lam (n + 1))
      = ps * (∫ q, f (seriesScaled lam q)
            ∂((zMeasure pd ps lam n).prod (zMeasure pd ps lam n)))
        + pd * (∫ q, f (diamondScaled lam q) ∂(prod4 (zMeasure pd ps lam n))) := by
  rw [zMeasure_succ_series hpd hps hsum, zMeasure_succ_diamond hpd hps hsum,
    zMeasure_succ_lhs hpd hps hsum]

/-! ## The limiting functional identity and the conclusion -/

/-
The assembled identity: if `ν_n → δ_c` weakly with `c > 0`, then for every bounded continuous
`f`, `f c = p_series · f(2λc) + p_diamond · f(λc)`.
-/
lemma limit_identity (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1)
    (lam : ℝ) (c : ℝ) (hc : 0 < c)
    (hP : Tendsto (fun n => zProb hpd hps hsum lam n) atTop (𝓝 (diracProb c)))
    (f : ℝ →ᵇ ℝ) :
    f c = ps * f (2 * lam * c) + pd * f (lam * c) := by
  -- Apply the weak_int_tendsto lemma to get the limit of the integral.
  have h_int_tendsto : Filter.Tendsto (fun n => ∫ x, f (x) ∂(zMeasure pd ps lam (n + 1))) Filter.atTop (nhds (f c)) := by
    convert weak_int_tendsto ( hP.comp ( Filter.tendsto_add_atTop_nat 1 ) ) f using 1;
  refine' tendsto_nhds_unique h_int_tendsto _;
  rw [ Filter.tendsto_congr fun n => zMeasure_succ_integral hpd hps hsum lam n f ];
  refine' Filter.Tendsto.add ( tendsto_const_nhds.mul _ ) ( tendsto_const_nhds.mul _ );
  · convert series_limit hP f using 1;
  · convert diamond_limit hc hP f using 1

/-- For `0 < c` and `0 < lam`, the two points `2λc` and `λc` are distinct, so at least one of them
differs from `c`. -/
lemma exists_ne_of_pos {c lam : ℝ} (hc : 0 < c) :
    2 * lam * c ≠ c ∨ lam * c ≠ c := by
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  rw [show 2 * lam * c = 2 * (lam * c) by ring, h2] at h1
  linarith

/-
A tent function: for `z ≠ c` there is a bounded continuous `f` with `f c = 1`, `f z = 0`,
and `0 ≤ f ≤ 1`.
-/
lemma exists_tent (c z : ℝ) (h : z ≠ c) :
    ∃ f : ℝ →ᵇ ℝ, f c = 1 ∧ f z = 0 ∧ ∀ x, 0 ≤ f x ∧ f x ≤ 1 := by
  -- Define thetent function $g(x) = \max(0, 1 - |x - c| / d)$ where $d = |z - c|$.
  set d := |z - c| with hd
  have hd_pos : 0 < d := by
    exact abs_pos.mpr ( sub_ne_zero.mpr h )
  set g : ℝ → ℝ := fun x => max 0 (1 - |x - c| / d) with hg_def
  have hg_cont : Continuous g := by
    fun_prop
  have hg_bound : ∀ x, 0 ≤ g x ∧ g x ≤ 1 := by
    exact fun x => ⟨ le_max_left _ _, max_le ( by norm_num ) ( sub_le_self _ ( by positivity ) ) ⟩
  exact ⟨BoundedContinuousFunction.ofNormedAddCommGroup g (by
  exact hg_cont) 1 (fun x => by
    exact abs_le.mpr ⟨ by linarith [ hg_bound x ], by linarith [ hg_bound x ] ⟩), by
    simp +zetaDelta at *, by
    norm_num +zetaDelta at *;
    rw [ div_self ( ne_of_gt ( abs_pos.mpr hd_pos ) ) ], by
    exact hg_bound⟩

/-- **Proposition 4.8 (no deterministic limit).**

Assume `p_series, p_diamond ∈ (0,1)`.  For `λ > 0` put `Z_n = λ^n R_n`.  If `Z_n` converges in
distribution to a deterministic constant `c ≥ 0` (i.e. `∫ f dν_n → f c` for every bounded
continuous `f`), then `c = 0`.

(The hypothesis `hlam : 0 < lam` is kept because the paper states the result for `λ > 0`; the
formal proof does not actually use it.) -/
theorem no_deterministic_limit
    (hpd0 : 0 < pd) (hpd1 : pd < 1) (hps0 : 0 < ps) (hps1 : ps < 1) (hsum : ps + pd = 1)
    (lam : ℝ) (hlam : 0 < lam) (c : ℝ) (hc : 0 ≤ c)
    (hconv : ∀ f : ℝ →ᵇ ℝ,
        Tendsto (fun n => ∫ x, f x ∂(zMeasure pd ps lam n)) atTop (𝓝 (f c))) :
    c = 0 := by
  by_contra hcne
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hcne)
  have hP : Tendsto (fun n => zProb hpd0.le hps0.le hsum lam n) atTop (𝓝 (diracProb c)) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    simpa [zProb, diracProb, integral_dirac] using hconv f
  have hid : ∀ f : ℝ →ᵇ ℝ, f c = ps * f (2 * lam * c) + pd * f (lam * c) :=
    fun f => limit_identity hpd0.le hps0.le hsum lam c hcpos hP f
  rcases exists_ne_of_pos (lam := lam) hcpos with h1 | h2
  · obtain ⟨f, hfc, hfz, hfb⟩ := exists_tent c (2 * lam * c) h1
    have heq := hid f
    rw [hfc, hfz] at heq
    have hle : pd * f (lam * c) ≤ pd := mul_le_of_le_one_right hpd0.le (hfb (lam * c)).2
    linarith
  · obtain ⟨f, hfc, hfz, hfb⟩ := exists_tent c (lam * c) h2
    have heq := hid f
    rw [hfc, hfz] at heq
    have hle : ps * f (2 * lam * c) ≤ ps := mul_le_of_le_one_right hps0.le (hfb (2 * lam * c)).2
    linarith

end

end Reduced
