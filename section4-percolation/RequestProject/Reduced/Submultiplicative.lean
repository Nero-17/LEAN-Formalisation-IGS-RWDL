import RequestProject.Reduced.Moments

/-!
# Submultiplicativity of the mean resistance (self-similarity / concavity argument)

This file constructs the **concavity / Jensen argument on random series–parallel networks** that
underlies the submultiplicativity of the mean reduced resistance
`E[R_{a+b}] ≤ E[R_a] · E[R_b]` (the "self-similarity" input of the capstone in `Limit.lean`).

The strategy is purely measure-theoretic, working with the laws `lawMeasure` directly:

* `genLaw ν n`: the same one–step recursion as `lawMeasure` but with an arbitrary *leaf law* `ν`
  at the base (`genLaw ν 0 = ν`).  We have `lawMeasure n = genLaw (δ₁) n` and the **composition
  identity** `genLaw ν (a+b) = genLaw (genLaw ν b) a` (substitution of the bottom `b` levels).

* `IcvLEon L`: the *increasing–concave order* on probability measures supported on `[L,∞)`
  (`∫ f dμ ≤ ∫ f dν` for every increasing concave continuous `f`).  Effective resistance of a
  series–parallel network is an increasing concave function of its leaf resistances, so this order
  is preserved by the one–step `combineM` and hence by `genLaw`.

* Replacing the leaf law by the point mass at its mean only increases the mean resistance
  (Jensen, `jensen_le_dirac`), and rescaling the leaf law rescales the mean resistance
  (homogeneity, `mean_genLaw_dirac`).

Combining these gives `E1_submultiplicative`.
-/

namespace Reduced

open MeasureTheory Measure Real Set

noncomputable section

/-! ## The one–step operator and the generalised law -/

/-- Law of the series combination of two i.i.d. copies of `μ`. -/
noncomputable def seriesLawM (μ : Measure ℝ) : Measure ℝ :=
  Measure.map seriesMap (μ.prod μ)

/-- Law of the parallel (`par`) combination of two i.i.d. copies of `μ`. -/
noncomputable def parPair (p : ℝ × ℝ) : ℝ := par p.1 p.2

noncomputable def parLawM (μ : Measure ℝ) : Measure ℝ :=
  Measure.map parPair (μ.prod μ)

lemma measurable_parPair : Measurable parPair := by
  unfold parPair par; fun_prop

/-- One step of the reduced–resistance recursion, as an operator on laws. -/
noncomputable def combineM (pd ps : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  (ENNReal.ofReal ps) • Measure.map seriesMap (μ.prod μ)
  + (ENNReal.ofReal pd) • Measure.map diamondMap (prod4 μ)

/-- The generalised law with an arbitrary leaf law `ν` at the base. -/
noncomputable def genLaw (pd ps : ℝ) (ν : Measure ℝ) : ℕ → Measure ℝ
  | 0 => ν
  | (n + 1) => combineM pd ps (genLaw pd ps ν n)

@[simp] lemma genLaw_zero (pd ps : ℝ) (ν : Measure ℝ) : genLaw pd ps ν 0 = ν := rfl

lemma genLaw_succ (pd ps : ℝ) (ν : Measure ℝ) (n : ℕ) :
    genLaw pd ps ν (n + 1) = combineM pd ps (genLaw pd ps ν n) := rfl

variable {pd ps : ℝ}

/-- `lawMeasure n+1 = combineM (lawMeasure n)` (definitional repackaging). -/
lemma lawMeasure_succ_combineM (n : ℕ) :
    lawMeasure pd ps (n + 1) = combineM pd ps (lawMeasure pd ps n) := rfl

/-- `lawMeasure` is `genLaw` started from the point mass `δ₁`. -/
lemma lawMeasure_eq_genLaw (n : ℕ) :
    lawMeasure pd ps n = genLaw pd ps (Measure.dirac 1) n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [lawMeasure_succ_combineM, genLaw_succ, ih]

/-- **Composition / self-similarity identity**: building `a+b` levels equals building `a` levels on
top of the law obtained from `b` levels. -/
lemma genLaw_comp (ν : Measure ℝ) (a b : ℕ) :
    genLaw pd ps ν (a + b) = genLaw pd ps (genLaw pd ps ν b) a := by
  induction a with
  | zero => rw [Nat.zero_add, genLaw_zero]
  | succ k ih =>
      rw [Nat.succ_add, genLaw_succ, genLaw_succ, ih]

/-! ## The diamond term as a parallel combination of two series laws -/

/-
The diamond law is the parallel combination of two independent series laws.
-/
lemma diamond_eq_parLaw_series (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measure.map diamondMap (prod4 μ) = parLawM (seriesLawM μ) := by
  unfold parLawM seriesLawM;
  rw [ MeasureTheory.Measure.prod_eq ];
  rotate_right;
  exact μ.prod ( μ.prod ( μ.prod μ ) ) |> Measure.map ( fun x => ( x.1 + x.2.1, x.2.2.1 + x.2.2.2 ) );
  · rw [ MeasureTheory.Measure.map_map ];
    · congr;
    · exact measurable_parPair;
    · fun_prop;
  · intro s t hs ht; rw [ Measure.map_apply, Measure.map_apply, Measure.map_apply ] <;> norm_num [ hs, ht, measurable_seriesMap ] ;
    · erw [ MeasureTheory.Measure.prod_apply, MeasureTheory.Measure.prod_apply ];
      · rw [ ← MeasureTheory.lintegral_mul_const ];
        · congr with x ; simp +decide [ Set.preimage, seriesMap ];
          erw [ show { x_1 : ℝ × ℝ × ℝ | x + x_1.1 ∈ s ∧ x_1.2.1 + x_1.2.2 ∈ t } = ( { x_1 : ℝ | x + x_1 ∈ s } ×ˢ { x_1 : ℝ × ℝ | x_1.1 + x_1.2 ∈ t } ) by ext ; aesop ] ; erw [ MeasureTheory.Measure.prod_prod ] ;
        · convert measurable_measure_prodMk_left ( show MeasurableSet { p : ℝ × ℝ | p.1 + p.2 ∈ s } from measurableSet_preimage ( measurable_fst.add measurable_snd ) hs ) using 1;
          infer_instance;
      · exact measurable_seriesMap hs;
      · exact MeasurableSet.preimage ( hs.prod ht ) ( measurable_fst.add measurable_snd.fst |> Measurable.prodMk <| measurable_snd.snd.fst.add measurable_snd.snd.snd );
    · exact Measurable.prodMk ( measurable_fst.add measurable_snd.fst ) ( measurable_snd.snd.fst.add measurable_snd.snd.snd );
    · exact hs.prod ht

/-! ## Goodness: probability measure with compact support in `[L, B]` -/

/-- A probability measure supported on a compact subinterval `[L, B]` of `[L, ∞)`. -/
structure GoodM (L : ℝ) (μ : Measure ℝ) : Prop where
  isProb : IsProbabilityMeasure μ
  supp : ∃ B, L ≤ B ∧ ∀ᵐ x ∂μ, x ∈ Set.Icc L B

/-
A function continuous on `[L, ∞)` is integrable against a `GoodM L` measure.
-/
lemma integrable_of_continuousOn {L : ℝ} {μ : Measure ℝ} (hμ : GoodM L μ)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ici L)) : Integrable f μ := by
  obtain ⟨ B, hLB, hsupp ⟩ := hμ.supp;
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun x => ( SupSet.sSup ( Set.image ( fun y => |f y| ) ( Set.Icc L B ) ) );
  · cases hμ ; aesop;
  · have h_aestronglyMeasurable : AEStronglyMeasurable f (μ.restrict (Set.Icc L B)) := by
      exact ContinuousOn.aestronglyMeasurable ( hf.mono ( Set.Icc_subset_Ici_self ) ) measurableSet_Icc;
    rw [ Measure.restrict_eq_self_of_ae_mem hsupp ] at h_aestronglyMeasurable ; aesop;
  · filter_upwards [ hsupp ] with x hx using le_csSup ( IsCompact.bddAbove ( isCompact_Icc.image_of_continuousOn ( hf.abs.mono ( Set.Icc_subset_Ici_self ) ) ) ) ( Set.mem_image_of_mem _ hx )

/-
The mean of a `GoodM L` measure lies in `[L, ∞)`.
-/
lemma mean_mem_Ici {L : ℝ} {μ : Measure ℝ} (hμ : GoodM L μ) :
    L ≤ ∫ x, x ∂μ := by
  have h_integrable : Integrable (fun x => x) μ := by
    convert integrable_of_continuousOn hμ continuousOn_id;
  obtain ⟨ B, hLB, hsupp ⟩ := hμ.supp;
  convert MeasureTheory.integral_mono_ae _ _ ( hsupp.mono fun x hx => hx.1 );
  · cases hμ ; aesop;
  · cases hμ ; aesop;
  · exact h_integrable

/-! ## Goodness is preserved by the constructions -/

lemma GoodM_dirac {L c : ℝ} (hc : L ≤ c) : GoodM L (Measure.dirac c) := by
  constructor;
  · infer_instance;
  · exact ⟨ c, hc, by simp +decide [ hc ] ⟩

lemma GoodM_seriesLawM {μ : Measure ℝ} (hμ : GoodM 1 μ) : GoodM 2 (seriesLawM μ) := by
  obtain ⟨ B, hLB, hsupp ⟩ := hμ.supp;
  refine' ⟨ _, 2 * B, _, _ ⟩;
  · constructor;
    rw [ seriesLawM, Measure.map_apply ] <;> norm_num [ measurable_seriesMap ];
    have := hμ.isProb; aesop;
  · linarith;
  · -- By definition of $seriesLawM$, we know that $seriesLawM μ$ is the pushforward of $μ × μ$ under the map $(x, y) ↦ x + y$.
    have h_pushforward : ∀ᵐ q ∂(μ.prod μ), seriesMap q ∈ Set.Icc 2 (2 * B) := by
      have h_prod : ∀ᵐ q ∂(μ.prod μ), q.1 ∈ Set.Icc 1 B ∧ q.2 ∈ Set.Icc 1 B := by
        apply_rules [ ae_prod_box ];
        · norm_num;
        · norm_num;
        · have := hμ.isProb; exact inferInstance;
        · have := hμ.isProb; exact inferInstance;
      filter_upwards [ h_prod ] with q hq using ⟨ by linarith [ hq.1.1, hq.2.1, show seriesMap q = q.1 + q.2 from rfl ], by linarith [ hq.1.2, hq.2.2, show seriesMap q = q.1 + q.2 from rfl ] ⟩;
    convert MeasureTheory.ae_map_iff ( measurable_seriesMap.aemeasurable ) measurableSet_Icc |>.2 h_pushforward using 1

lemma GoodM_parLawM {ρ : Measure ℝ} (hρ : GoodM 2 ρ) : GoodM 1 (parLawM ρ) := by
  constructor;
  · refine' ⟨ _ ⟩;
    erw [ Measure.map_apply ] <;> norm_num [ measurable_parPair ];
    cases hρ ; aesop;
  · use hρ.supp.choose;
    refine' ⟨ by linarith [ hρ.supp.choose_spec.1 ], _ ⟩;
    refine' MeasureTheory.ae_map_iff ( measurable_parPair.aemeasurable ) measurableSet_Icc |>.2 _;
    have h_support : ∀ᵐ q : ℝ × ℝ ∂ρ.prod ρ, 2 ≤ q.1 ∧ q.1 ≤ hρ.supp.choose ∧ 2 ≤ q.2 ∧ q.2 ≤ hρ.supp.choose := by
      have h_support : ∀ᵐ x ∂ρ, 2 ≤ x ∧ x ≤ hρ.supp.choose := by
        exact hρ.supp.choose_spec.2;
      convert ae_prod_box _ _ h_support h_support using 1;
      · ext; simp [Set.mem_setOf_eq];
        exact ⟨ fun h => ⟨ ⟨ h.1, h.2.1 ⟩, ⟨ h.2.2.1, h.2.2.2 ⟩ ⟩, fun h => ⟨ h.1.1, h.1.2, h.2.1, h.2.2 ⟩ ⟩;
      · have := hρ.isProb;
        infer_instance;
      · have := hρ.isProb;
        infer_instance;
      · exact measurableSet_Icc;
      · exact measurableSet_Icc;
    filter_upwards [ h_support ] with q hq;
    unfold parPair;
    unfold par; constructor <;> nlinarith [ mul_div_cancel₀ ( q.1 * q.2 ) ( by linarith : ( q.1 + q.2 ) ≠ 0 ) ] ;

lemma GoodM_combineM (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1)
    {μ : Measure ℝ} (hμ : GoodM 1 μ) : GoodM 1 (combineM pd ps μ) := by
  constructor;
  · have h_series : IsProbabilityMeasure (seriesLawM μ) := by
      exact GoodM_seriesLawM hμ |>.isProb
    have h_diamond : IsProbabilityMeasure (parLawM (seriesLawM μ)) := by
      exact GoodM_parLawM ( GoodM_seriesLawM hμ ) |> fun h => h.isProb
    have h_sum : IsProbabilityMeasure (combineM pd ps μ) := by
      constructor;
      unfold combineM;
      rw [ show map diamondMap ( prod4 μ ) = parLawM ( seriesLawM μ ) from ?_ ];
      · convert congr_arg₂ ( · + · ) ( congr_arg ( fun x : ENNReal => ENNReal.ofReal ps * x ) h_series.measure_univ ) ( congr_arg ( fun x : ENNReal => ENNReal.ofReal pd * x ) h_diamond.measure_univ ) using 1 ; ring!;
        rw [ ← ENNReal.ofReal_add hps hpd, hsum, ENNReal.ofReal_one ];
      · convert diamond_eq_parLaw_series μ;
        exact hμ.isProb
    exact h_sum;
  · obtain ⟨ B₁, hB₁, hB₁' ⟩ := GoodM_seriesLawM hμ |>.supp
    obtain ⟨ B₂, hB₂, hB₂' ⟩ := GoodM_parLawM ( GoodM_seriesLawM hμ ) |>.supp
    use max B₁ B₂;
    simp_all +decide [ combineM ];
    simp_all +decide [ MeasureTheory.ae_iff, ENNReal.ofReal ];
    refine' ⟨ ⟨ Or.inr _, Or.inr _ ⟩, Or.inr _, Or.inr _ ⟩;
    · exact MeasureTheory.measure_mono_null ( fun x hx => by norm_num at hx ⊢; linarith ) hB₁'.1;
    · exact MeasureTheory.measure_mono_null ( fun x hx => hx.1 ) hB₁'.2;
    · convert hB₂'.1 using 1;
      convert congr_arg ( fun m => m { a | a < 1 } ) ( diamond_eq_parLaw_series μ ) using 1;
      exact hμ.isProb;
    · rw [ show ( map diamondMap ( prod4 μ ) ) = parLawM ( seriesLawM μ ) from ?_ ];
      · exact MeasureTheory.measure_mono_null ( fun x hx => by aesop ) hB₂'.2;
      · convert diamond_eq_parLaw_series μ using 1;
        exact hμ.isProb

lemma GoodM_genLaw (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1)
    {ν : Measure ℝ} (hν : GoodM 1 ν) (n : ℕ) : GoodM 1 (genLaw pd ps ν n) := by
  induction n with
  | zero => simpa using hν
  | succ k ih => simpa [genLaw_succ] using GoodM_combineM hpd hps hsum ih

lemma GoodM_lawMeasure (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) (n : ℕ) :
    GoodM 1 (lawMeasure pd ps n) := by
  rw [lawMeasure_eq_genLaw]
  exact GoodM_genLaw hpd hps hsum (GoodM_dirac le_rfl) n

/-! ## The increasing–concave order -/

/-- The increasing–concave order on measures supported on `[L, ∞)`. -/
def IcvLEon (L : ℝ) (μ ν : Measure ℝ) : Prop :=
  ∀ f : ℝ → ℝ, ConcaveOn ℝ (Set.Ici L) f → MonotoneOn f (Set.Ici L) →
    ContinuousOn f (Set.Ici L) → (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν

/-
Means are monotone for the increasing–concave order.
-/
lemma mean_mono_of_icv {L : ℝ} {μ ν : Measure ℝ} (h : IcvLEon L μ ν) :
    (∫ x, x ∂μ) ≤ ∫ x, x ∂ν := by
  convert h id _ _ _ <;> norm_num [ ConcaveOn, MonotoneOn, ContinuousOn ];
  · exact convex_Ici L;
  · exact fun x hx => continuousWithinAt_id

/-
**Jensen base case**: a law is dominated, in the increasing–concave order, by the point mass at
its mean.
-/
lemma jensen_le_dirac {L : ℝ} {μ : Measure ℝ} (hμ : GoodM L μ) :
    IcvLEon L μ (Measure.dirac (∫ x, x ∂μ)) := by
  intro f hf;
  intro h_mono h_cont
  have h_jensen : ∫ x, f x ∂μ ≤ f (∫ x, x ∂μ) := by
    obtain ⟨ B, hLB, hsupp ⟩ := hμ.supp;
    apply_rules [ hf.le_map_integral ];
    · exact isClosed_Ici;
    · exact hsupp.mono fun x hx => hx.1;
    · apply_rules [ integrable_of_continuousOn ];
      exact continuousOn_id;
    · apply_rules [ integrable_of_continuousOn ];
    · exact hμ.isProb;
  aesop

/-! ## The analytic core: increasing–concave order is preserved by a binary combination -/

section BinopCore

variable {op : ℝ → ℝ → ℝ} {Lin Lout : ℝ}

/-
Composition of a concave/monotone/continuous outer function with such an inner one (on the
appropriate rays).
-/
lemma test_comp {e : ℝ → ℝ}
    (hmap : ∀ x, Lin ≤ x → Lout ≤ e x)
    (hec : ConcaveOn ℝ (Set.Ici Lin) e) (hem : MonotoneOn e (Set.Ici Lin))
    (hek : ContinuousOn e (Set.Ici Lin))
    {f : ℝ → ℝ} (hfc : ConcaveOn ℝ (Set.Ici Lout) f) (hfm : MonotoneOn f (Set.Ici Lout))
    (hfk : ContinuousOn f (Set.Ici Lout)) :
    ConcaveOn ℝ (Set.Ici Lin) (fun x => f (e x)) ∧
    MonotoneOn (fun x => f (e x)) (Set.Ici Lin) ∧
    ContinuousOn (fun x => f (e x)) (Set.Ici Lin) := by
  refine' ⟨ ⟨ convex_Ici Lin, fun x hx y hy a b ha hb hab => _ ⟩, _, _ ⟩;
  · refine' le_trans _ ( hfm _ _ _ );
    exact hfc.2 ( hmap x hx ) ( hmap y hy ) ha hb hab;
    · simp_all +decide [ ← eq_sub_iff_add_eq' ];
      cases lt_or_ge a ( 1 / 2 ) <;> nlinarith [ hmap x hx, hmap y hy ];
    · exact hmap _ ( by exact convex_Ici Lin hx hy ha hb hab );
    · exact hec.2 hx hy ha hb hab;
  · exact fun x hx y hy hxy => hfm ( hmap x hx ) ( hmap y hy ) ( hem hx hy hxy );
  · exact hfk.comp hek fun x hx => hmap x hx

/-- For fixed `y ≥ Lin`, the map `x ↦ f (op x y)` is a valid test function. -/
lemma binop_section_test
    (hmap : ∀ x y, Lin ≤ x → Lin ≤ y → Lout ≤ op x y)
    (hcont : ∀ y, Lin ≤ y → ContinuousOn (fun x => op x y) (Set.Ici Lin))
    (hmono : ∀ y, Lin ≤ y → MonotoneOn (fun x => op x y) (Set.Ici Lin))
    (hconc : ∀ y, Lin ≤ y → ConcaveOn ℝ (Set.Ici Lin) (fun x => op x y))
    {f : ℝ → ℝ} (hfc : ConcaveOn ℝ (Set.Ici Lout) f) (hfm : MonotoneOn f (Set.Ici Lout))
    (hfk : ContinuousOn f (Set.Ici Lout)) {y : ℝ} (hy : Lin ≤ y) :
    ConcaveOn ℝ (Set.Ici Lin) (fun x => f (op x y)) ∧
    MonotoneOn (fun x => f (op x y)) (Set.Ici Lin) ∧
    ContinuousOn (fun x => f (op x y)) (Set.Ici Lin) :=
  test_comp (fun x hx => hmap x y hx hy) (hconc y hy) (hmono y hy) (hcont y hy) hfc hfm hfk

/-
The partial integral `y ↦ ∫ x, f (op x y) ∂ρ` is concave on `[Lin, ∞)`.
-/
lemma binop_phi_concave
    (hsymm : ∀ x y, op x y = op y x)
    (hmap : ∀ x y, Lin ≤ x → Lin ≤ y → Lout ≤ op x y)
    (hcont : ∀ y, Lin ≤ y → ContinuousOn (fun x => op x y) (Set.Ici Lin))
    (hmono : ∀ y, Lin ≤ y → MonotoneOn (fun x => op x y) (Set.Ici Lin))
    (hconc : ∀ y, Lin ≤ y → ConcaveOn ℝ (Set.Ici Lin) (fun x => op x y))
    {ρ : Measure ℝ} (hρ : GoodM Lin ρ)
    {f : ℝ → ℝ} (hfc : ConcaveOn ℝ (Set.Ici Lout) f) (hfm : MonotoneOn f (Set.Ici Lout))
    (hfk : ContinuousOn f (Set.Ici Lout)) :
    ConcaveOn ℝ (Set.Ici Lin) (fun y => ∫ x, f (op x y) ∂ρ) := by
  refine' ⟨convex_Ici Lin, fun y1 hy1 y2 hy2 a b ha hb hab => _⟩;
  obtain ⟨ B, hB, hsupp ⟩ := hρ.supp;
  have h_integrable : ∀ y ∈ Set.Ici Lin, Integrable (fun x => f (op x y)) ρ := by
    intro y hy;
    apply_rules [ integrable_of_continuousOn ];
    exact hfk.comp ( hcont y hy ) fun x hx => hmap x y hx hy;
  have h_integral_mono : ∀ᵐ x ∂ρ, x ∈ Set.Icc Lin B → a * f (op x y1) + b * f (op x y2) ≤ f (op x (a * y1 + b * y2)) := by
    filter_upwards [ hsupp ] with x hx hx';
    have h_concave : ConcaveOn ℝ (Set.Ici Lin) (fun y => f (op x y)) := by
      have := binop_section_test hmap hcont hmono hconc hfc hfm hfk hx.1; aesop;
    exact h_concave.2 hy1 hy2 ha hb hab;
  have h_integral_mono : ∫ x, (a * f (op x y1) + b * f (op x y2)) ∂ρ ≤ ∫ x, f (op x (a * y1 + b * y2)) ∂ρ := by
    refine' MeasureTheory.integral_mono_ae _ _ _;
    · exact MeasureTheory.Integrable.add ( MeasureTheory.Integrable.const_mul ( h_integrable y1 hy1 ) _ ) ( MeasureTheory.Integrable.const_mul ( h_integrable y2 hy2 ) _ );
    · exact h_integrable _ ( by rw [ show a * y1 + b * y2 = a * y1 + ( 1 - a ) * y2 by rw [ ← hab ] ; ring ] ; exact Set.mem_Ici.mpr ( by nlinarith [ Set.mem_Ici.mp hy1, Set.mem_Ici.mp hy2 ] ) );
    · filter_upwards [ hsupp, h_integral_mono ] with x hx₁ hx₂ using hx₂ hx₁;
  convert h_integral_mono using 1;
  rw [ MeasureTheory.integral_add, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul ];
  · norm_num;
  · exact MeasureTheory.Integrable.const_mul ( h_integrable y1 hy1 ) _;
  · exact MeasureTheory.Integrable.const_mul ( h_integrable y2 hy2 ) _

/-
The partial integral `y ↦ ∫ x, f (op x y) ∂ρ` is monotone on `[Lin, ∞)`.
-/
lemma binop_phi_monotone
    (hsymm : ∀ x y, op x y = op y x)
    (hmap : ∀ x y, Lin ≤ x → Lin ≤ y → Lout ≤ op x y)
    (hcont : ∀ y, Lin ≤ y → ContinuousOn (fun x => op x y) (Set.Ici Lin))
    (hmono : ∀ y, Lin ≤ y → MonotoneOn (fun x => op x y) (Set.Ici Lin))
    (hconc : ∀ y, Lin ≤ y → ConcaveOn ℝ (Set.Ici Lin) (fun x => op x y))
    {ρ : Measure ℝ} (hρ : GoodM Lin ρ)
    {f : ℝ → ℝ} (hfc : ConcaveOn ℝ (Set.Ici Lout) f) (hfm : MonotoneOn f (Set.Ici Lout))
    (hfk : ContinuousOn f (Set.Ici Lout)) :
    MonotoneOn (fun y => ∫ x, f (op x y) ∂ρ) (Set.Ici Lin) := by
  intro y1 hy1 y2 hy2 hy12
  have h_integrable : Integrable (fun x => f (op x y1)) ρ ∧ Integrable (fun x => f (op x y2)) ρ := by
    constructor <;> apply_rules [ integrable_of_continuousOn ];
    · exact hfk.comp ( hcont y1 hy1 ) fun x hx => hmap x y1 hx hy1;
    · exact hfk.comp ( hcont y2 hy2 ) fun x hx => hmap x y2 hx hy2;
  refine' MeasureTheory.integral_mono_ae h_integrable.1 h_integrable.2 _;
  obtain ⟨ B, hB, hsupp ⟩ := hρ.supp;
  filter_upwards [ hsupp ] with x hx using hfm ( hmap x y1 hx.1 hy1 ) ( hmap x y2 hx.1 hy2 ) ( by simpa only [ hsymm ] using hmono x hx.1 hy1 hy2 hy12 )

/-
The partial integral `y ↦ ∫ x, f (op x y) ∂ρ` is continuous on `[Lin, ∞)`.
-/
lemma binop_phi_continuous
    (hsymm : ∀ x y, op x y = op y x)
    (hmap : ∀ x y, Lin ≤ x → Lin ≤ y → Lout ≤ op x y)
    (hcont : ∀ y, Lin ≤ y → ContinuousOn (fun x => op x y) (Set.Ici Lin))
    (hmono : ∀ y, Lin ≤ y → MonotoneOn (fun x => op x y) (Set.Ici Lin))
    (hconc : ∀ y, Lin ≤ y → ConcaveOn ℝ (Set.Ici Lin) (fun x => op x y))
    {ρ : Measure ℝ} (hρ : GoodM Lin ρ)
    {f : ℝ → ℝ} (hfc : ConcaveOn ℝ (Set.Ici Lout) f) (hfm : MonotoneOn f (Set.Ici Lout))
    (hfk : ContinuousOn f (Set.Ici Lout)) :
    ContinuousOn (fun y => ∫ x, f (op x y) ∂ρ) (Set.Ici Lin) := by
  intros y hy;
  refine' MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
  use fun x => |f ( op x Lin )| + |f ( op x ( y + 1 ) )|;
  · refine' Filter.eventually_of_mem self_mem_nhdsWithin fun n hn => _;
    exact ( integrable_of_continuousOn hρ ( binop_section_test hmap hcont hmono hconc hfc hfm hfk hn |>.2.2 ) ) |> fun h => h.aestronglyMeasurable;
  · have h_bound : ∀ᶠ n in nhdsWithin y (Ici Lin), ∀ x ∈ Set.Ici Lin, Lin ≤ n ∧ n ≤ y + 1 → |f (op x n)| ≤ |f (op x Lin)| + |f (op x (y + 1))| := by
      filter_upwards [ self_mem_nhdsWithin ] with n hn x hx hnx;
      have h_monotone : MonotoneOn (fun z => f (op x z)) (Set.Ici Lin) := by
        intros z hz w hw hzw;
        exact hfm ( show Lout ≤ op x z from hmap x z hx hz ) ( show Lout ≤ op x w from hmap x w hx hw ) ( by simpa [ hsymm ] using hmono x hx hz hw hzw );
      cases abs_cases ( f ( op x n ) ) <;> cases abs_cases ( f ( op x Lin ) ) <;> cases abs_cases ( f ( op x ( y + 1 ) ) ) <;> linarith [ h_monotone ( show Lin ∈ Set.Ici Lin by norm_num ) ( show n ∈ Set.Ici Lin by assumption ) hnx.1, h_monotone ( show n ∈ Set.Ici Lin by assumption ) ( show y + 1 ∈ Set.Ici Lin by norm_num; linarith [ Set.mem_Ici.mp hy ] ) hnx.2 ];
    filter_upwards [ h_bound, self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds ( Metric.ball_mem_nhds _ zero_lt_one ) ] with n hn hn' hn'';
    filter_upwards [ hρ.supp.choose_spec.2 ] with x hx using hn x hx.1 ⟨ hn'.out, by linarith [ abs_lt.mp ( mem_ball_iff_norm.mp hn'' ) ] ⟩;
  · refine' MeasureTheory.Integrable.add _ _;
    · have h_cont : ContinuousOn (fun x => f (op x Lin)) (Set.Ici Lin) := by
        exact hfk.comp ( hcont Lin le_rfl ) fun x hx => hmap x Lin hx le_rfl;
      exact MeasureTheory.Integrable.abs ( integrable_of_continuousOn hρ h_cont );
    · refine' MeasureTheory.Integrable.abs _;
      apply_rules [ integrable_of_continuousOn ];
      exact hfk.comp ( hcont _ ( by linarith [ Set.mem_Ici.mp hy ] ) ) fun x hx => hmap _ _ hx ( by linarith [ Set.mem_Ici.mp hy ] );
  · filter_upwards [ hρ.supp.choose_spec.2 ] with x hx;
    have := binop_section_test hmap hcont hmono hconc hfc hfm hfk hx.1;
    have := this.2.2.continuousWithinAt hy; simp_all +decide [ MonotoneOn, ContinuousWithinAt ] ;

/-
The composed integrand is integrable against the product law.
-/
lemma binop_integrable_prod
    (hmap : ∀ x y, Lin ≤ x → Lin ≤ y → Lout ≤ op x y)
    (hmeas : Measurable (fun p : ℝ × ℝ => op p.1 p.2))
    (hjoint : ContinuousOn (fun p : ℝ × ℝ => op p.1 p.2) (Set.Ici Lin ×ˢ Set.Ici Lin))
    {ρ : Measure ℝ} (hρ : GoodM Lin ρ)
    {f : ℝ → ℝ} (hfk : ContinuousOn f (Set.Ici Lout)) :
    Integrable (fun p : ℝ × ℝ => f (op p.1 p.2)) (ρ.prod ρ) := by
  cases' hρ with hρ₁ hρ₂;
  cases' hρ₂ with B hB;
  -- Since $op$ is continuous on the box $[Lin, B] \times [Lin, B]$, and $f$ is continuous on $[Lout, \infty)$, their composition is continuous on the box.
  have h_cont : ContinuousOn (fun p : ℝ × ℝ => f (op p.1 p.2)) (Set.Icc Lin B ×ˢ Set.Icc Lin B) := by
    exact hfk.comp ( hjoint.mono <| Set.prod_mono ( Set.Icc_subset_Ici_self ) ( Set.Icc_subset_Ici_self ) ) fun p hp => hmap _ _ hp.1.1 hp.2.1;
  have h_integrable : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => f (op p.1 p.2)) (Set.Icc Lin B ×ˢ Set.Icc Lin B) (ρ.prod ρ) := by
    apply_rules [ ContinuousOn.integrableOn_compact, isCompact_Icc.prod CompactIccSpace.isCompact_Icc ];
  rwa [ MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_eq_self_of_ae_mem ] at h_integrable;
  convert ae_prod_box measurableSet_Icc measurableSet_Icc hB.2 hB.2 using 1

/-
Fubini: integrating `f ∘ op` against the law of `(op X Y)` for i.i.d. `X,Y ∼ ρ` equals the
iterated integral `∫ y, (∫ x, f (op x y) ∂ρ) ∂ρ`.
-/
lemma binop_fubini
    (hmap : ∀ x y, Lin ≤ x → Lin ≤ y → Lout ≤ op x y)
    (hmeas : Measurable (fun p : ℝ × ℝ => op p.1 p.2))
    (hjoint : ContinuousOn (fun p : ℝ × ℝ => op p.1 p.2) (Set.Ici Lin ×ˢ Set.Ici Lin))
    {ρ : Measure ℝ} (hρ : GoodM Lin ρ)
    {f : ℝ → ℝ} (hfk : ContinuousOn f (Set.Ici Lout)) :
    (∫ z, f z ∂(Measure.map (fun p : ℝ × ℝ => op p.1 p.2) (ρ.prod ρ)))
      = ∫ y, (∫ x, f (op x y) ∂ρ) ∂ρ := by
  convert MeasureTheory.integral_prod_symm ( fun p => f ( op p.1 p.2 ) ) _ using 1;
  · rw [ MeasureTheory.integral_map ];
    · exact hmeas.aemeasurable;
    · have h_aestronglyMeasurable : ∀ᵐ x ∂map (fun p => op p.1 p.2) (ρ.prod ρ), x ∈ Set.Ici Lout := by
        rw [ MeasureTheory.ae_map_iff ];
        · have h_ae_support : ∀ᵐ p ∂(ρ.prod ρ), p.1 ∈ Set.Ici Lin ∧ p.2 ∈ Set.Ici Lin := by
            have h_ae_support : ∀ᵐ x ∂ρ, x ∈ Set.Ici Lin := by
              have := hρ.supp;
              exact this.choose_spec.2.mono fun x hx => hx.1;
            convert ae_prod_box ( measurableSet_Ici ) ( measurableSet_Ici ) h_ae_support h_ae_support using 1;
            · have := hρ.isProb;
              infer_instance;
            · have := hρ.isProb;
              infer_instance;
          exact MeasureTheory.measure_mono_null ( fun x hx => by contrapose! hx; aesop ) h_ae_support;
        · exact hmeas.aemeasurable;
        · exact measurableSet_Ici;
      have h_aestronglyMeasurable : AEStronglyMeasurable f (Measure.restrict (map (fun p => op p.1 p.2) (ρ.prod ρ)) (Set.Ici Lout)) := by
        exact hfk.aestronglyMeasurable measurableSet_Ici;
      rw [ Measure.restrict_eq_self_of_ae_mem ] at h_aestronglyMeasurable <;> aesop;
  · have := hρ.isProb;
    infer_instance;
  · have := hρ.1;
    infer_instance;
  · apply_rules [ binop_integrable_prod ]

end BinopCore

/-- **Swap lemma.**  If `op` is, in each variable separately, increasing, concave and continuous on
`[Lin, ∞)`, is jointly continuous, maps `[Lin,∞)²` into `[Lout,∞)`, and is symmetric, then the
increasing–concave order is preserved when forming the law of `op` of two i.i.d. copies. -/
lemma binop_icv (op : ℝ → ℝ → ℝ) (Lin Lout : ℝ)
    (hsymm : ∀ x y, op x y = op y x)
    (hmap : ∀ x y, Lin ≤ x → Lin ≤ y → Lout ≤ op x y)
    (hmeas : Measurable (fun p : ℝ × ℝ => op p.1 p.2))
    (hjoint : ContinuousOn (fun p : ℝ × ℝ => op p.1 p.2) (Set.Ici Lin ×ˢ Set.Ici Lin))
    (hcont : ∀ y, Lin ≤ y → ContinuousOn (fun x => op x y) (Set.Ici Lin))
    (hmono : ∀ y, Lin ≤ y → MonotoneOn (fun x => op x y) (Set.Ici Lin))
    (hconc : ∀ y, Lin ≤ y → ConcaveOn ℝ (Set.Ici Lin) (fun x => op x y))
    {μ ν : Measure ℝ} (hμ : GoodM Lin μ) (hν : GoodM Lin ν) (h : IcvLEon Lin μ ν) :
    IcvLEon Lout (Measure.map (fun p : ℝ × ℝ => op p.1 p.2) (μ.prod μ))
                 (Measure.map (fun p : ℝ × ℝ => op p.1 p.2) (ν.prod ν)) := by
  intro f hfc hfm hfk
  haveI := hμ.isProb; haveI := hν.isProb
  -- Fubini on both sides
  rw [binop_fubini hmap hmeas hjoint hμ hfk, binop_fubini hmap hmeas hjoint hν hfk]
  -- the partial integral against ν, as a test function on [Lin, ∞)
  have hφνc : ConcaveOn ℝ (Set.Ici Lin) (fun y => ∫ x, f (op x y) ∂ν) :=
    binop_phi_concave hsymm hmap hcont hmono hconc hν hfc hfm hfk
  have hφνm : MonotoneOn (fun y => ∫ x, f (op x y) ∂ν) (Set.Ici Lin) :=
    binop_phi_monotone hsymm hmap hcont hmono hconc hν hfc hfm hfk
  have hφνk : ContinuousOn (fun y => ∫ x, f (op x y) ∂ν) (Set.Ici Lin) :=
    binop_phi_continuous hsymm hmap hcont hmono hconc hν hfc hfm hfk
  -- integrability of the partial integrals against μ
  have hφμint : Integrable (fun y => ∫ x, f (op x y) ∂μ) μ :=
    integrable_of_continuousOn hμ
      (binop_phi_continuous hsymm hmap hcont hmono hconc hμ hfc hfm hfk)
  have hφνintμ : Integrable (fun y => ∫ x, f (op x y) ∂ν) μ :=
    integrable_of_continuousOn hμ hφνk
  obtain ⟨B, hB, hsuppμ⟩ := hμ.supp
  -- step 1: pointwise comparison of the partial integrals on the support of μ
  have hstep12 : (∫ y, (∫ x, f (op x y) ∂μ) ∂μ) ≤ ∫ y, (∫ x, f (op x y) ∂ν) ∂μ := by
    refine MeasureTheory.integral_mono_ae hφμint hφνintμ ?_
    filter_upwards [hsuppμ] with y hy
    have hyge : Lin ≤ y := hy.1
    obtain ⟨hc, hm, hk⟩ := binop_section_test hmap hcont hmono hconc hfc hfm hfk hyge
    exact h (fun x => f (op x y)) hc hm hk
  -- step 3: apply the hypothesis h to the partial integral against ν
  have hstep3 : (∫ y, (∫ x, f (op x y) ∂ν) ∂μ) ≤ ∫ y, (∫ x, f (op x y) ∂ν) ∂ν :=
    h (fun y => ∫ x, f (op x y) ∂ν) hφνc hφνm hφνk
  exact le_trans hstep12 hstep3

/-! ### Properties of `par` as a function of one coordinate -/

/-
`x ↦ par x y` is continuous on `[0, ∞)` for `y > 0`.
-/
lemma par_continuousOn_left {y : ℝ} (hy : 0 < y) :
    ContinuousOn (fun x => par x y) (Set.Ici (0 : ℝ)) := by
  exact ContinuousOn.div ( continuousOn_id.mul continuousOn_const ) ( continuousOn_id.add continuousOn_const ) fun x hx => by linarith [ Set.mem_Ici.mp hx ] ;

/-
`x ↦ par x y` is monotone on `[0, ∞)` for `y > 0`.
-/
lemma par_monotoneOn_left {y : ℝ} (hy : 0 < y) :
    MonotoneOn (fun x => par x y) (Set.Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  unfold par
  field_simp [hy];
  rw [ div_le_div_iff₀ ] <;> nlinarith [ Set.mem_Ici.mp hx, Set.mem_Ici.mp hy ]

/-
`x ↦ par x y` is concave on `[0, ∞)` for `y > 0`.
-/
lemma par_concaveOn_left {y : ℝ} (hy : 0 < y) :
    ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun x => par x y) := by
  refine ⟨ convex_Ici 0, fun x hx y hy a b ha hb hab => ?_ ⟩;
  simp +decide [ par, mul_comm, mul_assoc, mul_left_comm, ← eq_sub_iff_add_eq' ] at *;
  field_simp;
  subst hab; nlinarith [ sq_nonneg ( x - y ), mul_nonneg ha ( mul_nonneg hb ( sq_nonneg ( x - y ) ) ) ] ;

/-
`par` is jointly continuous on `[2, ∞) × [2, ∞)`.
-/
lemma par_continuousOn_prod :
    ContinuousOn (fun p : ℝ × ℝ => par p.1 p.2) (Set.Ici (2 : ℝ) ×ˢ Set.Ici (2 : ℝ)) := by
  exact ContinuousOn.div ( continuousOn_fst.mul continuousOn_snd ) ( continuousOn_fst.add continuousOn_snd ) fun p hp => by linarith [ Set.mem_Ici.mp hp.1, Set.mem_Ici.mp hp.2 ] ;

/-! ### Instantiations: series (`+`) and parallel (`par`) -/

lemma seriesLawM_icv {μ ν : Measure ℝ} (hμ : GoodM 1 μ) (hν : GoodM 1 ν)
    (h : IcvLEon 1 μ ν) : IcvLEon 2 (seriesLawM μ) (seriesLawM ν) := by
  apply binop_icv;
  any_goals tauto;
  grobner;
  grind;
  · exact measurable_fst.add measurable_snd;
  · exact ContinuousOn.add continuousOn_fst continuousOn_snd;
  · exact fun y hy => continuousOn_id.add continuousOn_const;
  · exact fun y hy => fun x hx z hz hz' => by simpa using hz';
  · intro y hy; constructor <;> norm_num;
    · exact convex_Ici _;
    · intros; rw [ ← eq_sub_iff_add_eq' ] at *; subst_vars; nlinarith;

lemma parLawM_icv {ρ σ : Measure ℝ} (hρ : GoodM 2 ρ) (hσ : GoodM 2 σ)
    (h : IcvLEon 2 ρ σ) : IcvLEon 1 (parLawM ρ) (parLawM σ) := by
  apply binop_icv;
  any_goals tauto;
  any_goals intro x y hx hy; unfold par; rw [ le_div_iff₀ ] <;> nlinarith;
  exact fun x y => by unfold par; ring;
  · exact Measurable.mul ( measurable_fst ) ( measurable_snd ) |> Measurable.div <| measurable_fst.add measurable_snd;
  · exact par_continuousOn_prod;
  · exact fun y hy => ContinuousOn.mono ( par_continuousOn_left ( by linarith ) ) ( Set.Ici_subset_Ici.mpr ( by norm_num ) );
  · exact fun y hy => ( par_monotoneOn_left ( by linarith ) ).mono ( Set.Ici_subset_Ici.mpr ( by linarith ) );
  · intro y hy; exact (par_concaveOn_left (by linarith : 0 < y)).subset (Set.Ici_subset_Ici.mpr (by norm_num)) (convex_Ici 2);

/-
One step preserves the increasing–concave order.
-/
lemma combineM_icv (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1)
    {μ ν : Measure ℝ} (hμ : GoodM 1 μ) (hν : GoodM 1 ν) (h : IcvLEon 1 μ ν) :
    IcvLEon 1 (combineM pd ps μ) (combineM pd ps ν) := by
  intro f hf hf' hf'';
  convert add_le_add ( mul_le_mul_of_nonneg_left ( show ∫ x, f x ∂(seriesLawM μ) ≤ ∫ x, f x ∂(seriesLawM ν) from ?_ ) hps ) ( mul_le_mul_of_nonneg_left ( show ∫ x, f x ∂(parLawM (seriesLawM μ)) ≤ ∫ x, f x ∂(parLawM (seriesLawM ν)) from ?_ ) hpd ) using 1;
  · convert MeasureTheory.integral_add_measure ( ?_ ) ( ?_ ) using 1;
    · simp +decide [ MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal hps, ENNReal.toReal_ofReal hpd ];
      convert rfl;
      convert diamond_eq_parLaw_series μ;
      exact hμ.isProb;
    · refine' MeasureTheory.Integrable.smul_measure _ _;
      · refine' integrable_of_continuousOn _ _;
        exact 2;
        · exact GoodM_seriesLawM hμ;
        · exact hf''.mono ( Set.Ici_subset_Ici.mpr ( by norm_num ) );
      · norm_num;
    · refine' MeasureTheory.Integrable.smul_measure _ _;
      · apply_rules [ integrable_of_continuousOn ];
        convert GoodM_parLawM ( GoodM_seriesLawM hμ ) using 1;
        convert diamond_eq_parLaw_series μ using 1;
        exact hμ.isProb;
      · norm_num;
  · convert integral_add_measure ( ?_ ) ( ?_ ) using 1;
    · rw [ MeasureTheory.integral_smul_measure, MeasureTheory.integral_smul_measure ];
      rw [ ENNReal.toReal_ofReal hps, ENNReal.toReal_ofReal hpd ];
      congr! 2;
      convert rfl using 2;
      convert diamond_eq_parLaw_series ν;
      exact hν.isProb;
    · refine' MeasureTheory.Integrable.smul_measure _ _;
      · apply_rules [ integrable_of_continuousOn, GoodM_seriesLawM ];
        exact hf''.mono ( Set.Ici_subset_Ici.mpr ( by norm_num ) );
      · norm_num;
    · refine' MeasureTheory.Integrable.smul_measure _ _;
      · convert integrable_of_continuousOn ( GoodM_parLawM ( GoodM_seriesLawM hν ) ) hf'' using 1;
        convert diamond_eq_parLaw_series ν using 1;
        exact hν.isProb;
      · norm_num;
  · apply (seriesLawM_icv hμ hν h) f (hf.subset (Set.Ici_subset_Ici.mpr (by norm_num : (1:ℝ) ≤ 2)) (convex_Ici 2)) (hf'.mono (Set.Ici_subset_Ici.mpr (by norm_num : (1:ℝ) ≤ 2))) (hf''.mono (Set.Ici_subset_Ici.mpr (by norm_num : (1:ℝ) ≤ 2)));
  · convert parLawM_icv ( GoodM_seriesLawM hμ ) ( GoodM_seriesLawM hν ) ( seriesLawM_icv hμ hν h ) f _ _ _ using 1;
    · exact hf;
    · assumption;
    · exact hf''

/-- `genLaw` preserves the increasing–concave order. -/
lemma genLaw_icv (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1)
    {μ ν : Measure ℝ} (hμ : GoodM 1 μ) (hν : GoodM 1 ν) (h : IcvLEon 1 μ ν) (n : ℕ) :
    IcvLEon 1 (genLaw pd ps μ n) (genLaw pd ps ν n) := by
  induction n with
  | zero => simpa using h
  | succ k ih =>
      simpa [genLaw_succ] using
        combineM_icv hpd hps hsum (GoodM_genLaw hpd hps hsum hμ k)
          (GoodM_genLaw hpd hps hsum hν k) ih

/-! ## Homogeneity (scaling the leaf law scales the mean) -/

/-
`par` is positively homogeneous of degree one.
-/
lemma par_scale {c : ℝ} (hc : c ≠ 0) (s t : ℝ) :
    par (c * s) (c * t) = c * par s t := by
  unfold par; ring;
  grind

/-
The diamond map is positively homogeneous of degree one.
-/
lemma diamondMap_scale {c : ℝ} (hc : c ≠ 0) (q : ℝ × ℝ × ℝ × ℝ) :
    diamondMap (c * q.1, c * q.2.1, c * q.2.2.1, c * q.2.2.2) = c * diamondMap q := by
  show par (c * q.1 + c * q.2.1) (c * q.2.2.1 + c * q.2.2.2)
      = c * par (q.1 + q.2.1) (q.2.2.1 + q.2.2.2)
  rw [show c * q.1 + c * q.2.1 = c * (q.1 + q.2.1) by ring,
      show c * q.2.2.1 + c * q.2.2.2 = c * (q.2.2.1 + q.2.2.2) by ring, par_scale hc]

/-
The series law commutes with rescaling of the underlying measure.
-/
lemma seriesLaw_map_scale (c : ℝ) (μ : Measure ℝ) [SFinite μ] :
    Measure.map seriesMap ((Measure.map (fun x => c * x) μ).prod (Measure.map (fun x => c * x) μ))
      = Measure.map (fun x => c * x) (Measure.map seriesMap (μ.prod μ)) := by
  convert Measure.map_map ?_ ?_ using 1;
  any_goals try infer_instance;
  · rw [ Measure.map_map, Measure.map_prod_map ];
    · rw [ MeasureTheory.Measure.map_map, MeasureTheory.Measure.map_map ];
      · congr! 1;
        ext ⟨x, y⟩; simp [seriesMap];
        ring;
      · exact measurable_const.mul measurable_id;
      · exact measurable_fst.add measurable_snd;
      · exact measurable_fst.add measurable_snd;
      · exact measurable_fst.const_mul _ |> Measurable.prodMk <| measurable_snd.const_mul _;
    · exact measurable_const.mul measurable_id;
    · exact measurable_const.mul measurable_id;
    · exact measurable_const.mul measurable_id;
    · exact measurable_id;
  · exact measurable_const.mul measurable_id;
  · exact measurable_id

/-
The diamond law commutes with rescaling of the underlying measure (`c ≠ 0`).
-/
lemma diamondLaw_map_scale {c : ℝ} (hc : c ≠ 0) (μ : Measure ℝ) [SFinite μ] :
    Measure.map diamondMap (prod4 (Measure.map (fun x => c * x) μ))
      = Measure.map (fun x => c * x) (Measure.map diamondMap (prod4 μ)) := by
  rw [ show prod4 ( Measure.map ( fun x => c * x ) μ ) = Measure.map ( Prod.map ( fun x => c * x ) ( Prod.map ( fun x => c * x ) ( Prod.map ( fun x => c * x ) ( fun x => c * x ) ) ) ) ( prod4 μ ) from ?_ ];
  · rw [ Measure.map_map, Measure.map_map ];
    · congr! 1;
      ext ⟨x1, x2, x3, x4⟩; simp [diamondMap, par];
      convert diamondMap_scale hc ( x1, x2, x3, x4 ) using 1;
    · exact measurable_const.mul measurable_id;
    · exact measurable_diamondMap;
    · exact measurable_diamondMap;
    · fun_prop;
  · unfold prod4;
    rw [ MeasureTheory.Measure.map_prod_map ];
    · rw [ MeasureTheory.Measure.map_prod_map ];
      · rw [ MeasureTheory.Measure.map_prod_map ];
        · exact measurable_const.mul measurable_id;
        · exact Measurable.prodMap ( measurable_const.mul measurable_id' ) ( Measurable.prodMap ( measurable_const.mul measurable_id' ) ( measurable_const.mul measurable_id' ) );
      · exact measurable_const.mul measurable_id;
      · exact measurable_fst.const_mul _ |> Measurable.prodMk <| measurable_snd.const_mul _;
    · exact measurable_const.mul measurable_id;
    · exact measurable_const.mul measurable_id

/-- `genLaw` preserves `SFinite`. -/
lemma sFinite_genLaw (ν : Measure ℝ) [SFinite ν] (n : ℕ) : SFinite (genLaw pd ps ν n) := by
  induction n with
  | zero => simpa using (inferInstance : SFinite ν)
  | succ k ih =>
      haveI := ih
      rw [genLaw_succ, combineM]
      unfold prod4
      infer_instance

/-- Scaling commutes with one step of the recursion (`c > 0`). -/
lemma combineM_scale {c : ℝ} (hc : 0 < c) (μ : Measure ℝ) [SFinite μ] :
    combineM pd ps (Measure.map (fun x => c * x) μ)
      = Measure.map (fun x => c * x) (combineM pd ps μ) := by
  unfold combineM
  rw [Measure.map_add _ _ (by fun_prop), Measure.map_smul, Measure.map_smul,
    seriesLaw_map_scale, diamondLaw_map_scale hc.ne']

/-- Scaling commutes with `genLaw` (`c > 0`). -/
lemma genLaw_scale {c : ℝ} (hc : 0 < c) (ν : Measure ℝ) [SFinite ν] (n : ℕ) :
    genLaw pd ps (Measure.map (fun x => c * x) ν) n
      = Measure.map (fun x => c * x) (genLaw pd ps ν n) := by
  induction n with
  | zero => rfl
  | succ k ih =>
      haveI := sFinite_genLaw (pd := pd) (ps := ps) ν k
      rw [genLaw_succ, genLaw_succ, ih, combineM_scale hc]

/-
The mean scales linearly under rescaling of a `GoodM` law.
-/
lemma mean_scale {L c : ℝ} {μ : Measure ℝ} (hμ : GoodM L μ) :
    (∫ x, x ∂(Measure.map (fun x => c * x) μ)) = c * ∫ x, x ∂μ := by
  cases eq_or_ne c 0 <;> simp_all +decide [ MeasureTheory.integral_map, mul_comm c ];
  rw [ MeasureTheory.integral_map ];
  · rw [ MeasureTheory.integral_mul_const ];
  · exact measurable_id.mul_const _ |> Measurable.aemeasurable;
  · exact measurable_id.aestronglyMeasurable

/-- `δ_c` is the rescaling of `δ₁`. -/
lemma dirac_scale (c : ℝ) :
    Measure.dirac c = Measure.map (fun x => c * x) (Measure.dirac (1 : ℝ)) := by
  rw [Measure.map_dirac (by fun_prop)]
  simp

/-
**Homogeneity**: the mean of `genLaw (δ_c)` is `c` times the mean of `genLaw (δ₁) = lawMeasure`.
-/
lemma mean_genLaw_dirac (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1)
    {c : ℝ} (hc : 0 < c) (a : ℕ) :
    (∫ x, x ∂(genLaw pd ps (Measure.dirac c) a)) = c * E1 pd ps a := by
  rw [ dirac_scale c, genLaw_scale hc ];
  rw [ ← lawMeasure_eq_genLaw ];
  convert mean_scale _;
  exacts [ 1, GoodM_lawMeasure hpd hps hsum a ]

/-! ## The submultiplicativity theorem -/

/-- **Submultiplicativity of the mean resistance.**
`E[R_{a+b}] ≤ E[R_a] · E[R_b]`, established via the concavity/Jensen argument on the random
series–parallel network (no extra hypotheses beyond the parameter constraints). -/
theorem E1_submultiplicative (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) (a b : ℕ) :
    E1 pd ps (a + b) ≤ E1 pd ps a * E1 pd ps b := by
  have hb : GoodM 1 (lawMeasure pd ps b) := GoodM_lawMeasure hpd hps hsum b
  set mb := ∫ x, x ∂(lawMeasure pd ps b) with hmb
  have hE1b : E1 pd ps b = mb := rfl
  have hmb1 : (1 : ℝ) ≤ mb := mean_mem_Ici hb
  have hcomp : lawMeasure pd ps (a + b) = genLaw pd ps (lawMeasure pd ps b) a := by
    rw [lawMeasure_eq_genLaw, genLaw_comp, ← lawMeasure_eq_genLaw]
  have hjen : IcvLEon 1 (lawMeasure pd ps b) (Measure.dirac mb) := jensen_le_dirac hb
  have hlift : IcvLEon 1 (genLaw pd ps (lawMeasure pd ps b) a)
      (genLaw pd ps (Measure.dirac mb) a) :=
    genLaw_icv hpd hps hsum hb (GoodM_dirac hmb1) hjen a
  have hmean := mean_mono_of_icv hlift
  have hrhs : (∫ x, x ∂(genLaw pd ps (Measure.dirac mb) a)) = mb * E1 pd ps a :=
    mean_genLaw_dirac hpd hps hsum (lt_of_lt_of_le one_pos hmb1) a
  have hlhs : E1 pd ps (a + b) = ∫ x, x ∂(genLaw pd ps (lawMeasure pd ps b) a) := by
    rw [E1, hcomp]
  rw [hlhs, hE1b]
  calc ∫ x, x ∂(genLaw pd ps (lawMeasure pd ps b) a)
      ≤ ∫ x, x ∂(genLaw pd ps (Measure.dirac mb) a) := hmean
    _ = mb * E1 pd ps a := hrhs
    _ = E1 pd ps a * mb := by ring

end

end Reduced