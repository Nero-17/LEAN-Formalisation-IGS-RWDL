import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Formalisation of Section 2 of arXiv:2603.13798
  *Iterated Graph Systems (I): random walks and diffusion limits*

This file begins a step-by-step formalisation of Section 2 ("Random walks").

The first milestone is **Lemma 2.3**, which lists the structural properties of the
*resistance renormalisation map* `Ψ`.  In the paper, `Ψ` is built from effective
resistances of finite electrical networks.  The proof of Lemma 2.3 proceeds via
**Thomson's principle**, which represents each coordinate of `Ψ` as

  `[Ψ(x)]_i = inf_{θ ∈ ℱ_i}  ∑_{e ∈ E(R_i)}  x_{𝒞(e)} · θ(e)²`,

i.e. an infimum, over a nonempty family of "flows" `θ`, of a linear functional of
`x` whose coefficients are nonnegative.  All five properties of Lemma 2.3
(monotonicity, homogeneity, continuity/extension, concavity, superadditivity) are
purely consequences of this representation, except continuity on the interior,
which additionally uses the finite-linear-system structure of the network.

Accordingly we abstract the Thomson-principle representation into a structure
`EIGS.ThomsonData` and prove the algebraic part of Lemma 2.3 at this level of
generality.  Connecting this representation to a genuine Mathlib development of
graph effective resistance is left to a future step.
-/

namespace EIGS

open scoped BigOperators

/-- Abstract Thomson-principle data for **one coordinate** of the resistance
renormalisation map of an EIGS.

In the electrical-network setting of arXiv:2603.13798, `F` indexes the unit flows
`θ` from `β⁺` to `β⁻` on the rule graph `R_i`, and
`w θ j = ∑_{e : 𝒞(e) = j} θ(e)²` is the (nonnegative) coefficient of the colour-`j`
resistance `x j` in the energy of the flow `θ`.  Thomson's principle then says the
effective resistance is the infimum of these energies, see `ThomsonData.eval`. -/
structure ThomsonData (K : ℕ) where
  /-- index type of flows. -/
  F : Type
  /-- there is at least one flow (the network is connected). -/
  nonempty : Nonempty F
  /-- nonnegative coefficient of colour `j` in the energy of flow `θ`. -/
  w : F → Fin K → ℝ
  /-- the coefficients are nonnegative (they are sums of squares `θ(e)²`). -/
  w_nonneg : ∀ θ j, 0 ≤ w θ j

attribute [instance] ThomsonData.nonempty

namespace ThomsonData

variable {K : ℕ} (d : ThomsonData K)

/-- Energy of the flow `θ` at the resistance vector `x`: a linear functional of `x`
with nonnegative coefficients. -/
def energy (θ : d.F) (x : Fin K → ℝ) : ℝ := ∑ j, d.w θ j * x j

/-- The Thomson functional: effective resistance as the infimum of flow energies. -/
noncomputable def eval (x : Fin K → ℝ) : ℝ := ⨅ θ, d.energy θ x

/-
Each flow energy is nonnegative on the nonnegative orthant.
-/
lemma energy_nonneg {x : Fin K → ℝ} (hx : 0 ≤ x) (θ : d.F) : 0 ≤ d.energy θ x := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg ( d.w_nonneg θ i ) ( hx i )

/-
The set of flow energies is bounded below (by `0`) on the nonnegative orthant.
-/
lemma bddBelow_energy {x : Fin K → ℝ} (hx : 0 ≤ x) :
    BddBelow (Set.range (fun θ => d.energy θ x)) := by
  exact ⟨ 0, Set.forall_mem_range.mpr fun θ => d.energy_nonneg hx θ ⟩

/-
The Thomson functional is nonnegative on the nonnegative orthant.
-/
lemma eval_nonneg {x : Fin K → ℝ} (hx : 0 ≤ x) : 0 ≤ d.eval x := by
  exact le_ciInf fun θ => d.energy_nonneg hx θ

/-
**Lemma 2.3 (1), Monotonicity).**
-/
lemma eval_mono {x y : Fin K → ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    d.eval x ≤ d.eval y := by
  apply_rules [ ciInf_mono ];
  · exact d.bddBelow_energy hx;
  · exact fun θ => Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ( hxy i ) ( d.w_nonneg θ i )

/-
**Lemma 2.3 (2), Homogeneity).**
-/
lemma eval_smul (x : Fin K → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    d.eval (t • x) = t * d.eval x := by
  -- By definition of `eval`, we have `eval (t • x) = ⨅ θ, energy θ (t • x)`.
  have h_eval : d.eval (t • x) = ⨅ θ, d.energy θ (t • x) := by
    rfl;
  -- By definition of `energy`, we have `energy θ (t • x) = t * energy θ x`.
  have h_energy : ∀ θ, d.energy θ (t • x) = t * d.energy θ x := by
    simp +decide [ ThomsonData.energy, mul_left_comm, Finset.mul_sum _ _ _ ];
  rw [ h_eval, funext h_energy ];
  rw [ ← Real.mul_iInf_of_nonneg ht ];
  rfl

/-
**Lemma 2.3 (4), Concavity).**
-/
lemma eval_concave {x y : Fin K → ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    l * d.eval x + (1 - l) * d.eval y ≤ d.eval (l • x + (1 - l) • y) := by
  -- Since for any θ, we have d.energy θ (l • x + (1 - l) • y) ≥ l * d.eval x + (1 - l) * d.eval y, taking the infimum over θ gives us the desired inequality.
  have h_inf : ∀ θ, d.energy θ (l • x + (1 - l) • y) ≥ l * d.eval x + (1 - l) * d.eval y := by
    intro θ
    have h_inf : d.energy θ (l • x + (1 - l) • y) = l * d.energy θ x + (1 - l) * d.energy θ y := by
      unfold ThomsonData.energy; simp +decide [ Finset.mul_sum _ _ _, Finset.sum_add_distrib, add_mul, mul_assoc, mul_comm, mul_left_comm ] ;
    exact h_inf.symm ▸ add_le_add ( mul_le_mul_of_nonneg_left ( ciInf_le ( d.bddBelow_energy hx ) θ ) hl0 ) ( mul_le_mul_of_nonneg_left ( ciInf_le ( d.bddBelow_energy hy ) θ ) ( sub_nonneg.mpr hl1 ) );
  exact le_ciInf h_inf

/-
**Lemma 2.3 (5), Superadditivity).**
-/
lemma eval_superadditive {x y : Fin K → ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    d.eval x + d.eval y ≤ d.eval (x + y) := by
  refine' le_csInf _ _ <;> norm_num;
  · exact ⟨ _, ⟨ Classical.arbitrary _, rfl ⟩ ⟩;
  · intro a; simp +decide [ ThomsonData.energy ];
    simpa only [ mul_add, Finset.sum_add_distrib, ThomsonData.eval ] using add_le_add ( ciInf_le ( d.bddBelow_energy hx ) a ) ( ciInf_le ( d.bddBelow_energy hy ) a )

/-
**Lemma 2.3 (3), Continuity / extension).**
The purely order-theoretic part: for `x ≥ 0` the function `ε ↦ eval (x + ε • 1)` is
monotone (nondecreasing) in `ε` on `(0, ∞)` and bounded below by `0`, hence its
right limit as `ε ↓ 0` exists.  This is the part of Lemma 2.3 (3) that the paper
derives from monotonicity alone; it yields the extension of `Ψ` to `ℝ≥0^K`.
The genuine continuity on `(0,∞)^K` additionally needs the finite-linear-system
structure of the network and is not provable at this abstract level.
-/
lemma eval_extension_monotoneOn {x : Fin K → ℝ} (hx : 0 ≤ x) :
    MonotoneOn (fun ε : ℝ => d.eval (x + ε • (fun _ => 1 : Fin K → ℝ)))
      (Set.Ioi 0) := by
  intro ε hε ε' hε' hεε';
  apply d.eval_mono;
  · exact fun i => add_nonneg ( hx i ) ( mul_nonneg hε.out.le zero_le_one );
  · exact fun i => add_le_add le_rfl ( mul_le_mul_of_nonneg_right hεε' zero_le_one )

lemma eval_extension_exists {x : Fin K → ℝ} (hx : 0 ≤ x) :
    ∃ L : ℝ, Filter.Tendsto (fun ε : ℝ => d.eval (x + ε • (fun _ => 1 : Fin K → ℝ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  -- Let f := fun ε => d.eval (x + ε • 1). Use L := sInf (f '' Set.Ioi 0) and apply MonotoneOn.tendsto_nhdsGT (with x := 0).
  set f : ℝ → ℝ := fun ε => d.eval (x + ε • (fun _ => 1 : Fin K → ℝ))
  have h_monotone : MonotoneOn f (Set.Ioi 0) := by
    convert d.eval_extension_monotoneOn hx using 1
  have h_bdd_below : BddBelow (f '' Set.Ioi 0) := by
    exact ⟨ 0, Set.forall_mem_image.2 fun ε hε => d.eval_nonneg <| add_nonneg hx <| smul_nonneg hε.out.le <| fun _ => zero_le_one ⟩
  use sInf (f '' Set.Ioi 0);
  convert MonotoneOn.tendsto_nhdsGT h_monotone h_bdd_below using 1

/-! ### Lemma 2.3 (3): genuine continuity on the open positive orthant

The extension part of Lemma 2.3(3) (above) only used monotonicity.  The genuine
*continuity* of the effective resistance on the interior `(0,∞)^K` is in fact a
consequence of **concavity** (Lemma 2.3(4)): a concave real function on an open
convex subset of a finite-dimensional space is automatically continuous there
(`ConcaveOn.continuousOn`).  So the interior continuity is provable at this
abstract Thomson level after all, without unfolding the finite linear system. -/

/-- The open positive orthant `(0,∞)^K` is convex. -/
lemma convex_pos_orthant : Convex ℝ {x : Fin K → ℝ | ∀ i, 0 < x i} := by
  intro x hx y hy a b ha hb hab i
  have hxi := hx i
  have hyi := hy i
  simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1; simpa using hyi
  · have h1 : 0 < a * x i := mul_pos ha' hxi
    have h2 : 0 ≤ b * y i := mul_nonneg hb hyi.le
    linarith

/-- The open positive orthant `(0,∞)^K` is open. -/
lemma isOpen_pos_orthant : IsOpen {x : Fin K → ℝ | ∀ i, 0 < x i} := by
  have : {x : Fin K → ℝ | ∀ i, 0 < x i} = ⋂ i, {x : Fin K → ℝ | 0 < x i} := by
    ext x; simp
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)

/-- **Lemma 2.3 (4) as a `ConcaveOn` on the positive orthant.** -/
lemma eval_concaveOn : ConcaveOn ℝ {x : Fin K → ℝ | ∀ i, 0 < x i} d.eval := by
  refine ⟨convex_pos_orthant, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx0 : (0 : Fin K → ℝ) ≤ x := fun i => (hx i).le
  have hy0 : (0 : Fin K → ℝ) ≤ y := fun i => (hy i).le
  have hb' : b = 1 - a := by linarith
  subst hb'
  have := d.eval_concave hx0 hy0 ha (by linarith)
  simpa [smul_eq_mul] using this

/-- **Lemma 2.3 (3), genuine continuity).** The effective resistance `eval` is
continuous on the open positive orthant `(0,∞)^K`. -/
lemma eval_continuousOn_pos :
    ContinuousOn d.eval {x : Fin K → ℝ | ∀ i, 0 < x i} :=
  d.eval_concaveOn.continuousOn isOpen_pos_orthant

end ThomsonData

/-- The **resistance renormalisation map** `Ψ` of an EIGS with `K` colours, given
abstractly by Thomson data for each of its `K` coordinates (Definition 2.1 via
Thomson's principle). -/
structure RenormMap (K : ℕ) where
  /-- Thomson data for coordinate `i`. -/
  coord : Fin K → ThomsonData K

namespace RenormMap

variable {K : ℕ} (Ψ : RenormMap K)

/-- The map `Ψ : ℝ≥0^K → ℝ≥0^K`. -/
noncomputable def apply (x : Fin K → ℝ) : Fin K → ℝ := fun i => (Ψ.coord i).eval x

/-
`Ψ` maps the nonnegative orthant to itself.
-/
lemma apply_nonneg {x : Fin K → ℝ} (hx : 0 ≤ x) : 0 ≤ Ψ.apply x := by
  exact fun i => ThomsonData.eval_nonneg ( Ψ.coord i ) hx

/-
**Lemma 2.3 (1), Monotonicity of `Ψ`).**
-/
lemma apply_mono {x y : Fin K → ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Ψ.apply x ≤ Ψ.apply y := by
  exact fun i => Ψ.coord i |>.eval_mono hx hxy

/-
**Lemma 2.3 (2), Homogeneity of `Ψ`).**
-/
lemma apply_smul (x : Fin K → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Ψ.apply (t • x) = t • Ψ.apply x := by
  exact funext fun i => ( Ψ.coord i ).eval_smul x ht

/-
**Lemma 2.3 (4), Concavity of `Ψ`).**
-/
lemma apply_concave {x y : Fin K → ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    l • Ψ.apply x + (1 - l) • Ψ.apply y ≤ Ψ.apply (l • x + (1 - l) • y) := by
  intro i; exact (by
  simpa using ThomsonData.eval_concave ( Ψ.coord i ) hx hy hl0 hl1)

/-
**Lemma 2.3 (5), Superadditivity of `Ψ`).**
-/
lemma apply_superadditive {x y : Fin K → ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Ψ.apply x + Ψ.apply y ≤ Ψ.apply (x + y) := by
  intro i;
  convert Ψ.coord i |>.eval_superadditive hx hy using 1

/-
**Lemma 2.3 (3), extension of `Ψ`).**
For `x ≥ 0`, the right limit of `Ψ (x + ε • 1)` as `ε ↓ 0` exists (coordinatewise,
hence in the product topology), defining the extension of `Ψ` to `ℝ≥0^K`.
-/
lemma apply_extension_exists {x : Fin K → ℝ} (hx : 0 ≤ x) :
    ∃ L : Fin K → ℝ, Filter.Tendsto (fun ε : ℝ => Ψ.apply (x + ε • (fun _ => 1 : Fin K → ℝ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  -- For each coordinate i, by (Ψ.coord i).eval_extension_exists hx there is a limit Lᵢ of ε ↦ (Ψ.coord i).eval (x + ε•1) as ε↓0.
  have h_ext_i : ∀ i : Fin K, ∃ L_i : ℝ, Filter.Tendsto (fun ε : ℝ => (Ψ.coord i).eval (x + ε • (fun _ => 1 : Fin K → ℝ))) (nhdsWithin 0 (Set.Ioi 0)) (nhds L_i) := by
    exact fun i => by have := ( Ψ.coord i ).eval_extension_exists hx; tauto;
  exact ⟨ fun i => Classical.choose ( h_ext_i i ), tendsto_pi_nhds.mpr fun i => Classical.choose_spec ( h_ext_i i ) ⟩

/-
**Lemma 2.3 (3), genuine continuity of `Ψ`).**  The renormalisation map `Ψ` is
continuous on the open positive orthant `(0,∞)^K` (coordinatewise, from
`ThomsonData.eval_continuousOn_pos`, hence in the product topology).
-/
lemma apply_continuousOn_pos :
    ContinuousOn Ψ.apply {x : Fin K → ℝ | ∀ i, 0 < x i} :=
  continuousOn_pi.mpr fun i => (Ψ.coord i).eval_continuousOn_pos

/-!
### Corollary 2.7: two-sided growth of the iterates of `Ψ`

Given a positive Perron eigenpair `Ψ(v) = ρ • v` (whose *existence* is Lemma 2.6,
relying on Nussbaum–Perron–Frobenius theory and left to a future step), the
iterates `Ψ^[ℓ] 1` grow like `ρ^ℓ`, uniformly in the colour.  The proof uses only
monotonicity and homogeneity of `Ψ`. -/

/-
One step of the lower comparison: if `a • v ≤ x` then `(a·ρ) • v ≤ Ψ(x)`.
-/
lemma smul_eigen_le_apply {v : Fin K → ℝ} {ρ : ℝ} (hv : 0 ≤ v)
    (heig : Ψ.apply v = ρ • v) {a : ℝ} (ha : 0 ≤ a) {x : Fin K → ℝ}
    (hx : a • v ≤ x) : (a * ρ) • v ≤ Ψ.apply x := by
  -- From hx : a•v ≤ x and 0 ≤ a•v (smul_nonneg ha hv), by monotonicity we have Ψ.apply (a•v) ≤ Ψ.apply x.
  have h1 : Ψ.apply (a • v) ≤ Ψ.apply x := by
    exact Ψ.apply_mono ( by exact fun i => mul_nonneg ha ( hv i ) ) hx;
  convert h1 using 1 ; ext i ; have := Ψ.apply_smul v ha ; simp_all +decide [ mul_comm, mul_left_comm, Pi.smul_apply ]

/-
One step of the upper comparison: if `0 ≤ x ≤ b • v` then `Ψ(x) ≤ (b·ρ) • v`.
-/
lemma apply_le_smul_eigen {v : Fin K → ℝ} {ρ : ℝ}
    (heig : Ψ.apply v = ρ • v) {b : ℝ} (hb : 0 ≤ b) {x : Fin K → ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ b • v) : Ψ.apply x ≤ (b * ρ) • v := by
  convert Ψ.apply_mono hx0 hx using 1;
  rw [ Ψ.apply_smul _ hb, heig, smul_smul, mul_comm ]

/-
Lower bound for the iterates: if `a • v ≤ x` then `(a·ρ^ℓ) • v ≤ Ψ^[ℓ](x)`.
-/
lemma smul_eigen_le_iterate {v : Fin K → ℝ} {ρ : ℝ} (hv : 0 ≤ v) (hρ : 0 ≤ ρ)
    (heig : Ψ.apply v = ρ • v) {a : ℝ} (ha : 0 ≤ a) {x : Fin K → ℝ}
    (hx : a • v ≤ x) (ℓ : ℕ) : (a * ρ ^ ℓ) • v ≤ Ψ.apply^[ℓ] x := by
  induction' ℓ with ℓ ih;
  · simpa using hx;
  · convert smul_eigen_le_apply Ψ hv heig ( mul_nonneg ha ( pow_nonneg hρ ℓ ) ) ih using 1;
    · rw [ pow_succ, mul_assoc ];
    · rw [ Function.iterate_succ_apply' ]

/-
Upper bound for the iterates: if `0 ≤ x ≤ b • v` then `Ψ^[ℓ](x) ≤ (b·ρ^ℓ) • v`.
-/
lemma iterate_le_smul_eigen {v : Fin K → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (heig : Ψ.apply v = ρ • v) {b : ℝ} (hb : 0 ≤ b) {x : Fin K → ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ b • v) (ℓ : ℕ) : Ψ.apply^[ℓ] x ≤ (b * ρ ^ ℓ) • v := by
  induction' ℓ with ℓ ih;
  · simpa using hx;
  · convert apply_le_smul_eigen Ψ heig ( show 0 ≤ b * ρ ^ ℓ by positivity ) _ ih using 1;
    · rw [ Function.iterate_succ_apply' ];
    · module;
    · exact Nat.recOn ℓ hx0 fun n ihn => by rw [ Function.iterate_succ_apply' ] ; exact Ψ.apply_nonneg ihn;

/-
**Corollary 2.7.** With a positive eigenpair `Ψ(v) = ρ • v` (all entries of `v`
positive and `ρ > 0`), there are constants `c, C > 0` with
`c ρ^ℓ ≤ [Ψ^[ℓ](1)]_i ≤ C ρ^ℓ` for every `ℓ` and every colour `i`.
-/
theorem iterate_one_two_sided {v : Fin K → ℝ} {ρ : ℝ}
    (hvpos : ∀ i, 0 < v i) (hρpos : 0 < ρ) (heig : Ψ.apply v = ρ • v) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ℓ : ℕ) (i : Fin K),
      c * ρ ^ ℓ ≤ (Ψ.apply^[ℓ] (fun _ => 1)) i ∧
        (Ψ.apply^[ℓ] (fun _ => 1)) i ≤ C * ρ ^ ℓ := by
  -- Let `M := Finset.univ.sup' huniv v (max entry) > 0`, and `mn := Finset.univ.inf' huniv v (min entry) > 0`.
  by_cases hK : K = 0;
  · subst hK; use 1, 1; aesop;
  · -- Let `M := Finset.univ.sup' huniv v (max entry) > 0`, and `mn := Finset.univ.inf' huniv v (min entry) > 0`.
    obtain ⟨M, hM⟩ : ∃ M > 0, ∀ i, v i ≤ M := by
      exact ⟨ ∑ i, v i, Finset.sum_pos ( fun _ _ => hvpos _ ) ⟨ ⟨ 0, Nat.pos_of_ne_zero hK ⟩, Finset.mem_univ _ ⟩, fun i => Finset.single_le_sum ( fun a _ => le_of_lt ( hvpos a ) ) ( Finset.mem_univ i ) ⟩
    obtain ⟨mn, hmn⟩ : ∃ mn > 0, ∀ i, mn ≤ v i := by
      cases K <;> [ aesop; exact ⟨ Finset.min' ( Finset.univ.image v ) ⟨ _, Finset.mem_image_of_mem v ( Finset.mem_univ ⟨ 0, Nat.pos_of_ne_zero hK ⟩ ) ⟩, by have := Finset.min'_mem ( Finset.univ.image v ) ⟨ _, Finset.mem_image_of_mem v ( Finset.mem_univ ⟨ 0, Nat.pos_of_ne_zero hK ⟩ ) ⟩ ; aesop, fun i => Finset.min'_le _ _ <| Finset.mem_image_of_mem v <| Finset.mem_univ _ ⟩ ];
    -- Set `a := 1 / M` and `b := 1 / mn`.
    set a := 1 / M
    set b := 1 / mn;
    -- Then `a • v ≤ one ≤ b • v` pointwise.
    have h_bounds : a • v ≤ (fun _ => 1 : Fin K → ℝ) ∧ (fun _ => 1 : Fin K → ℝ) ≤ b • v := by
      constructor <;> intro i <;> norm_num <;> nlinarith [ hvpos i, hM.2 i, hmn.2 i, mul_div_cancel₀ 1 hM.1.ne', mul_div_cancel₀ 1 hmn.1.ne' ];
    -- Now define `c := a * mn > 0` and `C := b * M > 0`.
    use a * mn, b * M;
    refine' ⟨ mul_pos ( one_div_pos.mpr hM.1 ) hmn.1, mul_pos ( one_div_pos.mpr hmn.1 ) hM.1, fun ℓ i => ⟨ _, _ ⟩ ⟩;
    · have := Ψ.smul_eigen_le_iterate ( show 0 ≤ v from fun i => le_of_lt ( hvpos i ) ) ( show 0 ≤ ρ from le_of_lt hρpos ) heig ( show 0 ≤ a from one_div_nonneg.mpr hM.1.le ) h_bounds.1 ℓ;
      exact le_trans ( by simpa [ mul_assoc, mul_comm, mul_left_comm ] using mul_le_mul_of_nonneg_left ( hmn.2 i ) ( show 0 ≤ a * ρ ^ ℓ by exact mul_nonneg ( one_div_nonneg.mpr hM.1.le ) ( pow_nonneg hρpos.le _ ) ) ) ( this i );
    · have := Ψ.iterate_le_smul_eigen ( show 0 ≤ ρ from le_of_lt hρpos ) heig ( show 0 ≤ b from one_div_nonneg.mpr hmn.1.le ) ( show 0 ≤ ( fun _ => 1 : Fin K → ℝ ) from fun _ => zero_le_one ) h_bounds.2 ℓ;
      exact le_trans ( this i ) ( by simpa [ mul_assoc, mul_comm, mul_left_comm ] using mul_le_mul_of_nonneg_left ( hM.2 i ) ( show 0 ≤ b * ρ ^ ℓ by exact mul_nonneg ( one_div_nonneg.mpr hmn.1.le ) ( pow_nonneg hρpos.le _ ) ) )

/-!
### Uniqueness of the Perron eigenvalue (part of Lemma 2.6)

The paper's Lemma 2.6 asserts that the resistance renormalisation map `Ψ` has a
*unique* eigenvalue `ρ(Ψ) > 0` (and a unique positive eigenvector up to scalars),
appealing to Nussbaum–Perron–Frobenius theory.  The **uniqueness of the
eigenvalue** is in fact a soft consequence of monotonicity and homogeneity alone,
and we prove it here at the abstract level.  (Existence of the eigenpair, and
uniqueness of the eigenvector, genuinely need the deeper irreducibility input and
are left to a future step.) -/

/-
Iterating a positive eigenvector: `Ψ^[ℓ](v) = ρ^ℓ • v`.
-/
lemma iterate_eigen {v : Fin K → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (heig : Ψ.apply v = ρ • v) (ℓ : ℕ) : Ψ.apply^[ℓ] v = ρ ^ ℓ • v := by
  induction' ℓ with ℓ ih;
  · norm_num;
  · rw [ Function.iterate_succ_apply', ih, pow_succ', mul_smul, RenormMap.apply_smul, heig ];
    · rw [ SMulCommClass.smul_comm ];
    · positivity

/-
**Lemma 2.6 (eigenvalue uniqueness).**  Any two positive eigenpairs of `Ψ`
have the same eigenvalue.  Requires at least one colour (`0 < K`); for `K = 0` the
statement is vacuously false since every scalar is an eigenvalue of the empty map.
-/
theorem eigenvalue_unique (hK : 0 < K) {v v' : Fin K → ℝ} {ρ ρ' : ℝ}
    (hv : ∀ i, 0 < v i) (hv' : ∀ i, 0 < v' i) (hρ : 0 < ρ) (hρ' : 0 < ρ')
    (heig : Ψ.apply v = ρ • v) (heig' : Ψ.apply v' = ρ' • v') :
    ρ = ρ' := by
  by_contra h_neq
  obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a • v ≤ v' ∧ v' ≤ b • v := by
    obtain ⟨a, ha⟩ : ∃ a : ℝ, 0 < a ∧ ∀ i, a * v i ≤ v' i := by
      exact ⟨ Finset.min' ( Finset.univ.image fun i => v' i / v i ) ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ ⟨ 0, hK ⟩ ) ⟩, by have := Finset.min'_mem ( Finset.univ.image fun i => v' i / v i ) ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ ⟨ 0, hK ⟩ ) ⟩ ; aesop, fun i => by have := Finset.min'_le _ _ ( Finset.mem_image_of_mem ( fun i => v' i / v i ) ( Finset.mem_univ i ) ) ; rw [ le_div_iff₀ ( hv i ) ] at this; linarith ⟩
    obtain ⟨b, hb⟩ : ∃ b : ℝ, 0 < b ∧ ∀ i, v' i ≤ b * v i := by
      exact ⟨ ( ∑ i, v' i / v i ) + 1, add_pos_of_nonneg_of_pos ( Finset.sum_nonneg fun _ _ => div_nonneg ( le_of_lt ( hv' _ ) ) ( le_of_lt ( hv _ ) ) ) zero_lt_one, fun i => by nlinarith [ hv i, hv' i, div_mul_cancel₀ ( v' i ) ( ne_of_gt ( hv i ) ), Finset.single_le_sum ( fun i _ => div_nonneg ( le_of_lt ( hv' i ) ) ( le_of_lt ( hv i ) ) ) ( Finset.mem_univ i ) ] ⟩
    use a, b;
    exact ⟨ ha.1, hb.1, fun i => ha.2 i, fun i => hb.2 i ⟩;
  -- Applying the inequalities and taking the limit as ℓ approaches infinity, we get a contradiction unless ρ = ρ'.
  have h_contra : ∀ ℓ : ℕ, a * ρ^ℓ * v ⟨0, hK⟩ ≤ ρ'^ℓ * v' ⟨0, hK⟩ ∧ ρ'^ℓ * v' ⟨0, hK⟩ ≤ b * ρ^ℓ * v ⟨0, hK⟩ := by
    intros ℓ
    have h_lower : a * ρ^ℓ * v ⟨0, hK⟩ ≤ ρ'^ℓ * v' ⟨0, hK⟩ := by
      have h_lower : (a * ρ^ℓ) • v ≤ Ψ.apply^[ℓ] v' := by
        apply smul_eigen_le_iterate;
        · exact fun i => le_of_lt ( hv i );
        · positivity;
        · exact heig;
        · positivity;
        · exact hab.1
      generalize_proofs at *; (
      convert h_lower ⟨ 0, hK ⟩ using 1 ; ring!;
      rw [ show Ψ.apply^[ℓ] v' = ρ'^ℓ • v' from ?_ ] ; norm_num [ mul_comm ] ; ring;
      grind +suggestions)
    have h_upper : ρ'^ℓ * v' ⟨0, hK⟩ ≤ b * ρ^ℓ * v ⟨0, hK⟩ := by
      convert RenormMap.iterate_le_smul_eigen Ψ ( show 0 ≤ ρ by positivity ) heig ( show 0 ≤ b by positivity ) ( show 0 ≤ v' by exact fun i => le_of_lt ( hv' i ) ) hab.2 ℓ |> fun h => h ⟨ 0, hK ⟩ using 1 ; ring!;
      rw [ RenormMap.iterate_eigen Ψ ( show 0 ≤ ρ' by positivity ) heig' ] ; aesop
    exact ⟨h_lower, h_upper⟩;
  -- Dividing both sides of the inequalities by ρ^ℓ, we get a * v ⟨0, hK⟩ ≤ (ρ' / ρ)^ℓ * v' ⟨0, hK⟩ ≤ b * v ⟨0, hK⟩.
  have h_div : ∀ ℓ : ℕ, a * v ⟨0, hK⟩ ≤ (ρ' / ρ)^ℓ * v' ⟨0, hK⟩ ∧ (ρ' / ρ)^ℓ * v' ⟨0, hK⟩ ≤ b * v ⟨0, hK⟩ := by
    simp_all +decide [ mul_assoc, div_pow ];
    field_simp;
    exact fun ℓ => ⟨ by linarith [ h_contra ℓ ], by linarith [ h_contra ℓ ] ⟩;
  -- If ρ' / ρ > 1, then (ρ' / ρ)^ℓ grows without bound as ℓ increases, contradicting the upper bound.
  by_cases h_ratio : ρ' / ρ > 1;
  · have h_contra : Filter.Tendsto (fun ℓ : ℕ => (ρ' / ρ)^ℓ * v' ⟨0, hK⟩) Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.atTop_mul_const ( hv' _ ) ( tendsto_pow_atTop_atTop_of_one_lt h_ratio );
    exact absurd ( h_contra.eventually_gt_atTop ( b * v ⟨ 0, hK ⟩ ) ) fun h => by obtain ⟨ ℓ, hℓ ⟩ := h.exists; linarith [ h_div ℓ ] ;
  · -- If ρ' / ρ < 1, then (ρ' / ρ)^ℓ tends to 0 as ℓ increases, contradicting the lower bound.
    have h_lim_zero : Filter.Tendsto (fun ℓ : ℕ => (ρ' / ρ)^ℓ * v' ⟨0, hK⟩) Filter.atTop (nhds 0) := by
      simpa using Filter.Tendsto.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one ( by positivity ) ( lt_of_le_of_ne ( le_of_not_gt h_ratio ) ( by intro h; exact h_neq <| by rw [ div_eq_iff <| by positivity ] at h; linarith ) ) ) tendsto_const_nhds;
    exact absurd ( le_of_tendsto_of_tendsto' tendsto_const_nhds h_lim_zero fun ℓ => h_div ℓ |>.1 ) ( by nlinarith [ hv ⟨ 0, hK ⟩, hv' ⟨ 0, hK ⟩ ] )

end RenormMap

end EIGS
