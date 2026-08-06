import RequestProject.Reduced.Params
import RequestProject.Reduced.RealAux

/-!
# The law of the reduced two-terminal resistance process

We construct, for parameters `pd, ps ≥ 0` with `pd + ps = 1`, the sequence of probability
measures `lawMeasure pd ps n` on `ℝ` describing the law of the reduced resistance `R_n` from
Subsection 4.1.

* `lawMeasure pd ps 0 = δ₁` (`R₀ = 1`).
* one step: with probability `ps` the cell is a *series* of two i.i.d. copies (`x + y`), and with
  probability `pd` it is a *diamond* of four i.i.d. copies (`par (x₁+x₂) (x₃+x₄)`).

We prove that each `lawMeasure pd ps n` is a probability measure supported on `[1, 2ⁿ]`.
-/

namespace Reduced

open MeasureTheory Measure Real

/-- The series combination map `(x, y) ↦ x + y`. -/
def seriesMap (q : ℝ × ℝ) : ℝ := q.1 + q.2

/-- The diamond combination map on four coordinates. -/
noncomputable def diamondMap (q : ℝ × ℝ × ℝ × ℝ) : ℝ := diamondVal q.1 q.2.1 q.2.2.1 q.2.2.2

/-- Fourfold product of a measure on `ℝ`. -/
noncomputable def prod4 (μ : Measure ℝ) : Measure (ℝ × ℝ × ℝ × ℝ) := μ.prod (μ.prod (μ.prod μ))

lemma measurable_seriesMap : Measurable seriesMap := by
  unfold seriesMap; fun_prop

lemma measurable_diamondMap : Measurable diamondMap := by
  unfold diamondMap diamondVal par
  fun_prop

/-- The law of `R_n`. -/
noncomputable def lawMeasure (pd ps : ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 1
  | (n + 1) =>
      (ENNReal.ofReal ps) • Measure.map seriesMap
          ((lawMeasure pd ps n).prod (lawMeasure pd ps n))
      + (ENNReal.ofReal pd) • Measure.map diamondMap (prod4 (lawMeasure pd ps n))

@[simp] lemma lawMeasure_zero (pd ps : ℝ) : lawMeasure pd ps 0 = Measure.dirac 1 := rfl

lemma lawMeasure_succ (pd ps : ℝ) (n : ℕ) :
    lawMeasure pd ps (n + 1) =
      (ENNReal.ofReal ps) • Measure.map seriesMap
          ((lawMeasure pd ps n).prod (lawMeasure pd ps n))
      + (ENNReal.ofReal pd) • Measure.map diamondMap (prod4 (lawMeasure pd ps n)) := rfl

variable {pd ps : ℝ}

/-
Each `lawMeasure pd ps n` is a probability measure (given `pd, ps ≥ 0`, `ps + pd = 1`).
-/
lemma isProb_lawMeasure (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) (n : ℕ) :
    IsProbabilityMeasure (lawMeasure pd ps n) := by
  induction' n with n ih;
  · constructor ; aesop;
  · constructor ; simp +decide [ *, lawMeasure_succ ];
    rw [ Measure.map_apply, Measure.map_apply ] <;> norm_num [ measurable_seriesMap, measurable_diamondMap ];
    simp +decide [ ← ENNReal.ofReal_add hps hpd, hsum, prod4 ]

/-
A.e. membership in a box for a product of two measures.
-/
lemma ae_prod_box {μ ν : Measure ℝ} [SFinite μ] [SFinite ν] {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hμ : ∀ᵐ x ∂μ, x ∈ S) (hν : ∀ᵐ y ∂ν, y ∈ T) :
    ∀ᵐ q ∂(μ.prod ν), q.1 ∈ S ∧ q.2 ∈ T := by
  simp_all +decide [ Filter.eventually_all, Set.setOf_and ];
  constructor <;> rw [ MeasureTheory.ae_iff ] at *;
  · rw [ show { a : ℝ × ℝ | a.1 ∉ S } = ( Sᶜ ×ˢ Set.univ ) by ext ; aesop, MeasureTheory.Measure.prod_prod ] ; aesop;
  · erw [ show { a : ℝ × ℝ | a.2 ∉ T } = ( Set.univ : Set ℝ ) ×ˢ Tᶜ by ext ; aesop, MeasureTheory.Measure.prod_prod ] ; aesop

/-
A.e. membership in a box for the fourfold product.
-/
lemma ae_prod4_box {μ : Measure ℝ} [IsProbabilityMeasure μ] {S : Set ℝ} (hS : MeasurableSet S)
    (hμ : ∀ᵐ x ∂μ, x ∈ S) :
    ∀ᵐ q ∂(prod4 μ), q.1 ∈ S ∧ q.2.1 ∈ S ∧ q.2.2.1 ∈ S ∧ q.2.2.2 ∈ S := by
  have h_ae_prod : ∀ᵐ x ∂μ, x ∈ S := by
    exact hμ
  have h_ae_prod2 : ∀ᵐ q ∂(μ.prod μ), q.1 ∈ S ∧ q.2 ∈ S :=
    ae_prod_box hS hS hμ hμ
  have h_ae_prod3 : ∀ᵐ q ∂(μ.prod (μ.prod μ)), q.1 ∈ S ∧ q.2.1 ∈ S ∧ q.2.2 ∈ S := by
    rw [ MeasureTheory.ae_iff ] at *;
    rw [ MeasureTheory.Measure.prod_apply ];
    · rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_zero ];
      filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h_ae_prod ] with x hx;
      simp_all +decide [ Set.preimage ];
    · exact MeasurableSet.compl ( MeasurableSet.inter ( measurable_fst hS ) ( MeasurableSet.inter ( measurable_snd.fst hS ) ( measurable_snd.snd hS ) ) )
  have h_ae_prod4 : ∀ᵐ q ∂(μ.prod (μ.prod (μ.prod μ))), q.1 ∈ S ∧ q.2.1 ∈ S ∧ q.2.2.1 ∈ S ∧ q.2.2.2 ∈ S := by
    rw [ MeasureTheory.ae_iff ] at *;
    rw [ show { a : ℝ × ℝ × ℝ × ℝ | ¬ ( a.1 ∈ S ∧ a.2.1 ∈ S ∧ a.2.2.1 ∈ S ∧ a.2.2.2 ∈ S ) } = ( { a : ℝ | ¬ ( a ∈ S ) } ×ˢ Set.univ ) ∪ ( Set.univ ×ˢ { a : ℝ × ℝ × ℝ | ¬ ( a.1 ∈ S ∧ a.2.1 ∈ S ∧ a.2.2 ∈ S ) } ) from ?_ ];
    · refine' MeasureTheory.measure_union_null _ _ <;> simp_all +decide [ MeasureTheory.Measure.prod_prod ];
    · grind
  exact h_ae_prod4

/-
The law of `R_n` is supported on `[1, 2ⁿ]`.
-/
lemma lawMeasure_support (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) (n : ℕ) :
    ∀ᵐ x ∂(lawMeasure pd ps n), x ∈ Set.Icc (1 : ℝ) (2 ^ n) := by
  induction' n with n ih <;> norm_num at *;
  -- Apply the induction hypothesis to the series and diamond cases.
  have h_series : ∀ᵐ x ∂(Measure.map seriesMap ((lawMeasure pd ps n).prod (lawMeasure pd ps n))), x ∈ Set.Icc 1 (2^(n+1)) := by
    rw [ MeasureTheory.ae_map_iff ];
    · have h_series : ∀ᵐ (q : ℝ × ℝ) ∂(lawMeasure pd ps n).prod (lawMeasure pd ps n), q.1 ∈ Set.Icc 1 (2^n) ∧ q.2 ∈ Set.Icc 1 (2^n) := by
        apply_rules [ ae_prod_box, ih.1, ih.2 ];
        all_goals norm_num [ ih.1, ih.2 ]; all_goals have := isProb_lawMeasure hpd hps hsum n; infer_instance;
      filter_upwards [ h_series ] with q hq using ⟨ by norm_num [ seriesMap ] ; linarith [ hq.1.1, hq.2.1 ], by norm_num [ seriesMap, pow_succ' ] ; linarith [ hq.1.2, hq.2.2 ] ⟩ ;
    · exact measurable_seriesMap.aemeasurable;
    · exact measurableSet_Icc
  have h_diamond : ∀ᵐ x ∂(Measure.map diamondMap (prod4 (lawMeasure pd ps n))), x ∈ Set.Icc 1 (2^(n+1)) := by
    rw [ MeasureTheory.ae_map_iff ];
    · have h_diamond : ∀ᵐ q ∂(prod4 (lawMeasure pd ps n)), q.1 ∈ Set.Icc 1 (2^n) ∧ q.2.1 ∈ Set.Icc 1 (2^n) ∧ q.2.2.1 ∈ Set.Icc 1 (2^n) ∧ q.2.2.2 ∈ Set.Icc 1 (2^n) := by
        convert ae_prod4_box ( measurableSet_Icc ) _ using 1;
        · exact isProb_lawMeasure hpd hps hsum n;
        · exact ih.1.and ih.2;
      filter_upwards [ h_diamond ] with q hq using diamond_bounds hq.1.1 hq.1.2 hq.2.1.1 hq.2.1.2 hq.2.2.1.1 hq.2.2.1.2 hq.2.2.2.1 hq.2.2.2.2 |> fun h => ⟨ h.1, h.2.trans <| by norm_num [ pow_succ' ] ⟩;
    · exact measurable_diamondMap.aemeasurable;
    · exact measurableSet_Icc;
  simp_all +decide [ MeasureTheory.ae_add_measure_iff ];
  rw [ lawMeasure_succ ];
  simp_all +decide [ MeasureTheory.ae_iff ]

end Reduced