import RequestProject.Section2
import RequestProject.Section2Network

/-!
# The resistance substitution recursion on genuine networks (Section 2.1, Lemma 2.4)

`Section21.lean` proves the *algebraic* iterate identity of Lemma 2.4 (a sequence
`yₙ` with `y₀ = x`, `yₙ₊₁ = Ψ(yₙ)` equals `Ψⁿ(x)`), but the *geometric* fact that the
edge substitution actually realises `Ψ` — i.e. that the effective resistance of the
substituted network equals `Ψ` applied to the effective resistance of the base
network — was left to the combinatorial framework.

This file proves that geometric substitution recursion **directly on genuine finite
electrical networks** (`Section2Network.Network`), via Thomson's principle.

## The construction

Given a base network `G` (a finite `K`-coloured directed multigraph) and a
*rule family* `F` assigning to each colour `i` a connected two-terminal rule network
`R_i` (terminals `β⁺_i ≠ β⁻_i`), the **substituted network** `G.subst F` replaces
each edge `e` of `G` (of colour `c = G.color e`) by a private copy of `R_c`, gluing
the terminals `β⁺_c, β⁻_c` of the copy to the endpoints `tail e, head e` of `e`.
Concretely:

* `V(G.subst F) = V(G) ⊕ (Σ e, interior vertices of R_{c(e)})`;
* `E(G.subst F) = Σ e, E(R_{c(e)})`.

This mirrors exactly the vertex-identification quotient `XiVtx 𝓘 (n+1)` of
`Section1Vertices.lean`.

## The main result

`Network.subst_effRes`:
`(G.subst F).effRes (inl a) (inl b) x = G.effRes a b (F.Psi x)`,
where `F.Psi x i = (R i).effRes β⁺_i β⁻_i x` is precisely the renormalisation map
`Ψ` of Definition 2.1.

The proof is Thomson's principle in both directions:

* (≥) any unit flow `θ'` on `G.subst F` projects to a unit flow `θ_G` on `G`
  (`substProj`), and its energy decomposes copy-by-copy; within each copy the energy
  of a `t`-flow is `≥ t²·R_eff(R_c)`, giving
  `ℰ(θ') ≥ ℰ_G(θ_G, Ψ x) ≥ R_eff(G, Ψ x)`;
* (≤) any unit flow `θ_G` on `G` lifts (`substLift`) by scaling near-optimal rule
  flows, with energy `≈ ℰ_G(θ_G, Ψ x)`.
-/

namespace EIGS

open scoped BigOperators
open Filter Topology

variable {K : ℕ}

/-- A `K`-colour **rule family**: for each colour `i` a connected two-terminal rule
network `R_i` with distinct planting vertices `β⁺_i ≠ β⁻_i`.  (This is the data of
`RuleSystem` together with the distinctness of the terminals, which the substitution
geometry needs.) -/
structure RuleFamily (K : ℕ) where
  /-- rule network for colour `i`. -/
  R : Fin K → Network K
  /-- positive terminal `β⁺_i`. -/
  βplus : ∀ i, (R i).V
  /-- negative terminal `β⁻_i`. -/
  βminus : ∀ i, (R i).V
  /-- the two terminals are distinct. -/
  plant_ne : ∀ i, βplus i ≠ βminus i
  /-- each rule is connected (so a unit flow exists). -/
  connected : ∀ i, Nonempty ((R i).Flow (βplus i) (βminus i))

namespace Network

variable (G : Network K) (F : RuleFamily K)

/-- The interior (non-planting) vertices of the rule copy attached to edge `e`. -/
def SubstInner (e : G.E) : Type :=
  {w : (F.R (G.color e)).V //
      w ≠ F.βplus (G.color e) ∧ w ≠ F.βminus (G.color e)}

instance (e : G.E) : Fintype (G.SubstInner F e) := by
  unfold Network.SubstInner; infer_instance

instance (e : G.E) : DecidableEq (G.SubstInner F e) := by
  unfold Network.SubstInner; infer_instance

/-- The vertex-identification embedding of a rule-copy vertex `w` (on edge `e`) into
`V(G.subst F)`: the planting vertices `β⁺, β⁻` are glued to `tail e, head e`; every
interior vertex becomes its own private vertex `(e, w)`. -/
def substEmbed (e : G.E) (w : (F.R (G.color e)).V) :
    G.V ⊕ (Σ e : G.E, G.SubstInner F e) :=
  if hp : w = F.βplus (G.color e) then Sum.inl (G.tail e)
  else if hm : w = F.βminus (G.color e) then Sum.inl (G.head e)
  else Sum.inr ⟨e, w, hp, hm⟩

/-- The **substituted network** `G.subst F`: each edge `e` of `G` is replaced by a
private copy of the rule network `R_{c(e)}`, terminals glued to the endpoints of `e`. -/
noncomputable def subst : Network K where
  V := G.V ⊕ (Σ e : G.E, G.SubstInner F e)
  E := Σ e : G.E, (F.R (G.color e)).E
  fintypeV := inferInstance
  decEqV := Classical.decEq _
  fintypeE := inferInstance
  tail := fun p => G.substEmbed F p.1 ((F.R (G.color p.1)).tail p.2)
  head := fun p => G.substEmbed F p.1 ((F.R (G.color p.1)).head p.2)
  color := fun p => (F.R (G.color p.1)).color p.2

/-- The renormalisation map `Ψ` of Definition 2.1, read off the rule family: the
`i`-th coordinate of `F.Psi x` is the effective resistance of rule `R_i`. -/
noncomputable def _root_.EIGS.RuleFamily.Psi (F : RuleFamily K) (x : Fin K → ℝ)
    (i : Fin K) : ℝ :=
  (F.R i).effRes (F.βplus i) (F.βminus i) (F.connected i) x

/-- Restriction of a current `θ'` on `G.subst F` to the copy on edge `e`. -/
def substRestrict (θ' : (G.subst F).E → ℝ) (e : G.E) :
    (F.R (G.color e)).E → ℝ := fun e' => θ' ⟨e, e'⟩

/-- The current that `θ'` induces on the base edge `e`: the throughput through the
copy on `e`, measured as the divergence of the restricted current at `β⁺`. -/
def substProj (θ' : (G.subst F).E → ℝ) (e : G.E) : ℝ :=
  (F.R (G.color e)).div (G.substRestrict F θ' e) (F.βplus (G.color e))

/-- Lift a base current `θ_G` on `G` together with rule currents `φ` to a current on
`G.subst F` by scaling the copy on `e` by `θ_G e`. -/
def substLift (θG : G.E → ℝ) (φ : ∀ i, (F.R i).E → ℝ) :
    (G.subst F).E → ℝ := fun p => θG p.1 * φ (G.color p.1) p.2

/-! ### General `Network` lemmas (Thomson lower bound) -/

/-
The total divergence of any current is zero.
-/
lemma div_sum_zero (N : Network K) (θ : N.E → ℝ) : ∑ u, N.div θ u = 0 := by
  unfold Network.div;
  simp +decide [ Finset.sum_ite ];
  rw [ sub_eq_zero, Finset.sum_fiberwise, Finset.sum_fiberwise ]

/-
Divergence is linear in scaling the current.
-/
lemma div_smul (N : Network K) (t : ℝ) (θ : N.E → ℝ) (u : N.V) :
    N.div (fun e => t * θ e) u = t * N.div θ u := by
  unfold Network.div; simp +decide [ mul_sub, Finset.mul_sum _ _ _ ] ;

/-
Energy scales quadratically.
-/
lemma energyNetwork_smul (N : Network K) (t : ℝ) (θ : N.E → ℝ) (x : Fin K → ℝ) :
    N.energyNetwork (fun e => t * θ e) x = t ^ 2 * N.energyNetwork θ x := by
  unfold Network.energyNetwork; simp +decide [ mul_pow, mul_assoc, mul_comm, Finset.mul_sum _ _ _ ] ;

/-
The flow energy is nonnegative for nonnegative resistances.
-/
lemma energyNetwork_nonneg (N : Network K) (θ : N.E → ℝ) {x : Fin K → ℝ}
    (hx : 0 ≤ x) : 0 ≤ N.energyNetwork θ x := by
  exact Finset.sum_nonneg fun _ _ => mul_nonneg ( hx _ ) ( sq_nonneg _ )

/-
The family of unit-flow energies is bounded below (by `0`) for `x ≥ 0`.
-/
lemma bddBelow_flow_energy (N : Network K) (a b : N.V) {x : Fin K → ℝ} (hx : 0 ≤ x) :
    BddBelow (Set.range (fun θ : N.Flow a b => N.energyNetwork θ.1 x)) := by
  exact ⟨ 0, Set.forall_mem_range.mpr fun θ => energyNetwork_nonneg N _ hx ⟩

/-
`effRes` is a lower bound for the energy of any unit flow (`x ≥ 0`).
-/
lemma effRes_le_energy (N : Network K) (a b : N.V) (hconn : Nonempty (N.Flow a b))
    {x : Fin K → ℝ} (hx : 0 ≤ x) (θ : N.Flow a b) :
    N.effRes a b hconn x ≤ N.energyNetwork θ.1 x := by
  rw [Network.effRes_eq_iInf];
  exact ciInf_le ( bddBelow_flow_energy N a b hx ) θ

/-
If every unit-flow energy is `≥ c`, then `effRes ≥ c`.
-/
lemma le_effRes (N : Network K) (a b : N.V) (hconn : Nonempty (N.Flow a b))
    {x : Fin K → ℝ} {c : ℝ} (h : ∀ θ : N.Flow a b, c ≤ N.energyNetwork θ.1 x) :
    c ≤ N.effRes a b hconn x := by
  rw [Network.effRes_eq_iInf];
  exact le_ciInf h

/-
**Thomson lower bound.**  Any current `θ` whose divergence is `t` at `p`, `-t`
at `q`, and `0` elsewhere (a "`t`-flow") has energy `≥ t² · R_eff(p,q)`.
-/
lemma energy_ge_sq_mul_effRes (N : Network K) (p q : N.V)
    (hconn : Nonempty (N.Flow p q)) {x : Fin K → ℝ} (hx : 0 ≤ x)
    {θ : N.E → ℝ} {t : ℝ}
    (hθ : ∀ u, N.div θ u = t * (if u = p then 1 else if u = q then -1 else 0)) :
    t ^ 2 * N.effRes p q hconn x ≤ N.energyNetwork θ x := by
  by_cases ht : t = 0;
  · simpa [ ht ] using energyNetwork_nonneg N θ hx;
  · -- Define φ : N.E → ℝ by φ = fun e => (1/t) * θ e.
    set φ : N.E → ℝ := fun e => (1 / t) * θ e;
    -- By effRes_le_energy N p q hconn hx Φ: N.effRes p q hconn x ≤ N.energyNetwork φ x.
    have h_effRes_le_energy : N.effRes p q hconn x ≤ N.energyNetwork φ x := by
      apply effRes_le_energy N p q hconn hx ⟨φ, by
        intro u; specialize hθ u; simp_all +decide ;
        rw [ show N.div φ u = ( 1 / t ) * N.div θ u by exact div_smul N _ _ _ ] ; aesop⟩;
    -- By energyNetwork_smul N (1/t) θ x: N.energyNetwork φ x = (1/t)^2 * N.energyNetwork θ x.
    have h_energyNetwork_smul : N.energyNetwork φ x = (1 / t) ^ 2 * N.energyNetwork θ x := by
      exact energyNetwork_smul N (1 / t) θ x;
    convert mul_le_mul_of_nonneg_left h_effRes_le_energy ( sq_nonneg t ) using 1 ; rw [ h_energyNetwork_smul ] ; ring_nf ; aesop

/-! ### Divergence bookkeeping for the substituted network -/

/-
Divergence of `θ'` at an interior vertex `(e, w)` equals the divergence of the
restricted current at `w`.
-/
lemma div_subst_inr (θ' : (G.subst F).E → ℝ) (e : G.E) (w : G.SubstInner F e) :
    (G.subst F).div θ' (Sum.inr ⟨e, w⟩) =
      (F.R (G.color e)).div (G.substRestrict F θ' e) w.1 := by
  unfold Network.div;
  congr! 1;
  · erw [ Finset.sum_sigma ];
    rw [ Finset.sum_eq_single e ];
    · congr! 1;
      split_ifs <;> simp_all +decide [ Network.subst, Network.substEmbed ];
      · rfl;
      · grind;
      · grind;
    · unfold Network.subst; simp +decide [ Network.substEmbed ] ;
      intro b hb; rw [ Finset.sum_eq_zero ] ; intros ; aesop;
    · aesop;
  · erw [ Finset.sum_sigma ];
    rw [ Finset.sum_eq_single e ];
    · convert rfl;
      constructor <;> intro h <;> simp_all +decide [ Network.subst, Network.substEmbed ];
      · grind +locals;
      · grind;
    · intro b _ hb; rw [ Finset.sum_eq_zero ] ; intros ; simp_all +decide [ Network.subst ] ;
      unfold Network.substEmbed; aesop;
    · aesop

/-
Divergence of `θ'` at an old (skeleton) vertex `inl v`, expressed through the
divergences of the restricted currents at the planting vertices.
-/
lemma div_subst_inl (θ' : (G.subst F).E → ℝ) (v : G.V) :
    (G.subst F).div θ' (Sum.inl v) =
      (∑ e, if G.tail e = v then
          (F.R (G.color e)).div (G.substRestrict F θ' e) (F.βplus (G.color e)) else 0)
      + (∑ e, if G.head e = v then
          (F.R (G.color e)).div (G.substRestrict F θ' e) (F.βminus (G.color e)) else 0) := by
  have h_sum : ∑ p : (G.subst F).E, (if (G.subst F).tail p = Sum.inl v then θ' p else 0) =
    ∑ e : G.E, (if G.tail e = v then (∑ e' : (F.R (G.color e)).E, if (F.R (G.color e)).tail e' = F.βplus (G.color e) then θ' ⟨e, e'⟩ else 0) else 0) +
    ∑ e : G.E, (if G.head e = v then (∑ e' : (F.R (G.color e)).E, if (F.R (G.color e)).tail e' = F.βminus (G.color e) then θ' ⟨e, e'⟩ else 0) else 0) := by
      have h_sum : ∀ e : G.E, ∀ u : (F.R (G.color e)).V, (G.substEmbed F e u = Sum.inl v) ↔ (u = F.βplus (G.color e) ∧ G.tail e = v) ∨ (u = F.βminus (G.color e) ∧ G.head e = v) := by
        intro e u; unfold Network.substEmbed; split_ifs <;> simp_all +decide [ Sum.inl.injEq ] ;
        exact fun h => False.elim <| F.plant_ne _ h;
      have h_split : ∀ e : G.E, (∑ p : (F.R (G.color e)).E, if (G.subst F).tail ⟨e, p⟩ = Sum.inl v then θ' ⟨e, p⟩ else 0) =
        (∑ p : (F.R (G.color e)).E, if (F.R (G.color e)).tail p = F.βplus (G.color e) then (if G.tail e = v then θ' ⟨e, p⟩ else 0) else 0) +
        (∑ p : (F.R (G.color e)).E, if (F.R (G.color e)).tail p = F.βminus (G.color e) then (if G.head e = v then θ' ⟨e, p⟩ else 0) else 0) := by
          intro e; rw [ ← Finset.sum_add_distrib ] ; congr; ext p; specialize h_sum e ( ( F.R ( G.color e ) ).tail p ) ; simp_all +decide [ Network.subst, Network.substEmbed ] ;
          grind +suggestions;
      convert Finset.sum_congr rfl fun e _ => h_split e using 1;
      any_goals exact Finset.univ;
      · erw [ Finset.sum_sigma' ];
        refine' Finset.sum_bij ( fun x _ => ⟨ x.1, x.2 ⟩ ) _ _ _ _ <;> aesop;
      · rw [ ← Finset.sum_add_distrib ] ; congr ; ext ; split_ifs <;> simp +decide [ * ] ;
  have h_sum_head : ∑ p : (G.subst F).E, (if (G.subst F).head p = Sum.inl v then θ' p else 0) =
    ∑ e : G.E, (if G.tail e = v then (∑ e' : (F.R (G.color e)).E, if (F.R (G.color e)).head e' = F.βplus (G.color e) then θ' ⟨e, e'⟩ else 0) else 0) +
    ∑ e : G.E, (if G.head e = v then (∑ e' : (F.R (G.color e)).E, if (F.R (G.color e)).head e' = F.βminus (G.color e) then θ' ⟨e, e'⟩ else 0) else 0) := by
      have h_sum_head : ∀ e : G.E, ∀ e' : (F.R (G.color e)).E, (G.subst F).head ⟨e, e'⟩ = Sum.inl v ↔
        ((F.R (G.color e)).head e' = F.βplus (G.color e) ∧ G.tail e = v) ∨
        ((F.R (G.color e)).head e' = F.βminus (G.color e) ∧ G.head e = v) := by
          intros e e'
          simp [Network.subst, Network.substEmbed];
          grind +suggestions;
      erw [ Finset.sum_sigma ] ; simp +decide [ h_sum_head ] ; ring;
      rw [ ← Finset.sum_add_distrib ] ; congr ; ext e ; by_cases he : G.tail e = v <;> by_cases he' : G.head e = v <;> simp +decide [ he, he' ] ;
      rw [ ← Finset.sum_add_distrib ] ; congr ; ext x ; by_cases hx : ( F.R ( G.color e ) ).head x = F.βplus ( G.color e ) <;> by_cases hx' : ( F.R ( G.color e ) ).head x = F.βminus ( G.color e ) <;> simp +decide [ hx, hx' ] ;
      · exact fun h => False.elim <| F.plant_ne ( G.color e ) h;
      · grind +qlia;
      · exact fun h => False.elim <| F.plant_ne ( G.color e ) <| h.symm;
  unfold Network.div; simp +decide [ *, Network.substRestrict ] ; ring;
  simp +decide [ Finset.sum_ite ] ; ring

/-
For a unit flow on `G.subst F`, the restricted current on each copy `e` is a
`(substProj e)`-flow: its divergence is `substProj e` at `β⁺`, `-substProj e` at
`β⁻`, and `0` at every interior vertex.
-/
lemma substRestrict_tflow (a b : G.V) (θ' : (G.subst F).E → ℝ)
    (hθ' : (G.subst F).IsUnitFlow (Sum.inl a) (Sum.inl b) θ') (e : G.E) (u : (F.R (G.color e)).V) :
    (F.R (G.color e)).div (G.substRestrict F θ' e) u =
      (G.substProj F θ' e) *
        (if u = F.βplus (G.color e) then 1
         else if u = F.βminus (G.color e) then -1 else 0) := by
  by_cases hu : u = F.βplus ( G.color e ) <;> by_cases hu' : u = F.βminus ( G.color e ) <;> simp +decide [ hu, hu', Network.substProj ];
  · have h_sum_zero : ∑ u : (F.R (G.color e)).V, (F.R (G.color e)).div (G.substRestrict F θ' e) u = 0 := by
      exact div_sum_zero (F.R (G.color e)) (G.substRestrict F θ' e);
    have h_sum_zero : ∑ u ∈ Finset.univ \ {F.βplus (G.color e), F.βminus (G.color e)}, (F.R (G.color e)).div (G.substRestrict F θ' e) u = 0 := by
      refine' Finset.sum_eq_zero fun u hu => _;
      have := hθ' ( Sum.inr ⟨ e, ⟨ u, by aesop ⟩ ⟩ ) ; simp_all +decide [ Network.div_subst_inr ] ;
    simp_all +decide [ F.plant_ne ];
    linarith;
  · convert hθ' ( Sum.inr ⟨ e, ⟨ u, hu, hu' ⟩ ⟩ ) using 1 ; simp +decide [ Network.subst, Network.substEmbed ];
    · convert div_subst_inr G F θ' e ⟨ u, hu, hu' ⟩ |> Eq.symm using 1;
    · grind

/-
The projected current `substProj θ'` is a unit flow on `G` from `a` to `b`.
-/
lemma substProj_isUnitFlow (a b : G.V) (θ' : (G.subst F).E → ℝ)
    (hθ' : (G.subst F).IsUnitFlow (Sum.inl a) (Sum.inl b) θ') :
    G.IsUnitFlow a b (G.substProj F θ') := by
  intro v;
  have h_div_subst : (G.subst F).div θ' (Sum.inl v) = G.div (G.substProj F θ') v := by
    rw [Network.div_subst_inl];
    rw [Network.div];
    rw [ sub_eq_add_neg, ← Finset.sum_neg_distrib ] ; congr ; ext e ; simp +decide [ Network.substProj ] ; ring;
    have := F.plant_ne ( G.color e ) ; have := F.connected ( G.color e ) ; have := substRestrict_tflow G F a b θ' hθ' e; aesop;
  convert hθ' ( Sum.inl v ) using 1 ; aesop;
  grind

/-
Energy of `θ'` decomposes as a sum over copies.
-/
lemma energyNetwork_subst (θ' : (G.subst F).E → ℝ) (x : Fin K → ℝ) :
    (G.subst F).energyNetwork θ' x =
      ∑ e, (F.R (G.color e)).energyNetwork (G.substRestrict F θ' e) x := by
  erw [ Finset.sum_sigma' ];
  refine' Finset.sum_bij ( fun e _ => ⟨ e.1, e.2 ⟩ ) _ _ _ _ <;> aesop

/-! ### The lift (for the `≤` direction) -/

/-
The lifted current is a unit flow on `G.subst F` provided `θG` is a unit flow on
`G` and each `φ i` is a unit flow on `R_i`.
-/
lemma substLift_isUnitFlow (a b : G.V) (θG : G.E → ℝ)
    (hθG : G.IsUnitFlow a b θG) (φ : ∀ i, (F.R i).E → ℝ)
    (hφ : ∀ i, (F.R i).IsUnitFlow (F.βplus i) (F.βminus i) (φ i)) :
    (G.subst F).IsUnitFlow (Sum.inl a) (Sum.inl b) (G.substLift F θG φ) := by
  intro u;
  rcases u with ( u | ⟨ e, u ⟩ ) <;> simp_all +decide [ Network.div_subst_inl, Network.div_subst_inr ];
  · rw [ ← Finset.sum_add_distrib ];
    rw [ Finset.sum_congr rfl fun e _ => ?_ ];
    convert hθG u using 1;
    rw [ Network.div ];
    rw [ ← Finset.sum_sub_distrib ];
    · grind;
    · have h_div_subst : (F.R (G.color e)).div (G.substRestrict F (G.substLift F θG φ) e) (F.βplus (G.color e)) = θG e ∧ (F.R (G.color e)).div (G.substRestrict F (G.substLift F θG φ) e) (F.βminus (G.color e)) = -θG e := by
        have h_div_subst : (F.R (G.color e)).div (G.substRestrict F (G.substLift F θG φ) e) = fun u => θG e * (F.R (G.color e)).div (φ (G.color e)) u := by
          ext u; simp +decide [ Network.div, Network.substRestrict, Network.substLift ] ; ring;
          simp +decide only [Finset.mul_sum _ _ _, mul_ite, mul_zero];
        simp_all +decide [ Network.IsUnitFlow ];
        exact fun h => False.elim <| F.plant_ne ( G.color e ) h.symm;
      split_ifs <;> linarith;
  · convert div_smul ( F.R ( G.color e ) ) ( θG e ) ( φ ( G.color e ) ) u.1 using 1;
    rw [ hφ _ _ ];
    grind +suggestions

/-
Energy of the lifted current.
-/
lemma energyNetwork_substLift (θG : G.E → ℝ) (φ : ∀ i, (F.R i).E → ℝ)
    (x : Fin K → ℝ) :
    (G.subst F).energyNetwork (G.substLift F θG φ) x =
      ∑ e, (θG e) ^ 2 * (F.R (G.color e)).energyNetwork (φ (G.color e)) x := by
  convert energyNetwork_subst ( G := G ) ( F := F ) ( G.substLift F θG φ ) x using 2 ; ring!;
  unfold Network.energyNetwork; simp +decide [ mul_comm, Finset.mul_sum _ _ _ ] ;
  unfold Network.substRestrict Network.substLift; simp +decide [ mul_pow, mul_assoc ] ;

/-! ### Connectivity of the substituted network -/

/-
If `G` is connected between `a, b` and every rule is connected, then `G.subst F`
is connected between `inl a` and `inl b`.
-/
lemma subst_connected (a b : G.V) (hGconn : Nonempty (G.Flow a b)) :
    Nonempty ((G.subst F).Flow (Sum.inl a) (Sum.inl b)) := by
  -- By the connectedness of the individual rules and the base graph, their substitution is connected.
  obtain ⟨θG, hθG⟩ := hGconn;
  obtain ⟨φ, hφ⟩ : ∃ φ : ∀ i, (F.R i).E → ℝ, ∀ i, (F.R i).IsUnitFlow (F.βplus i) (F.βminus i) (φ i) := by
    exact ⟨ fun i => Classical.choice ( F.connected i ) |> Subtype.val, fun i => Classical.choice ( F.connected i ) |> Subtype.property ⟩;
  exact ⟨ ⟨ G.substLift F θG φ, substLift_isUnitFlow G F a b θG hθG φ hφ ⟩ ⟩

/-
`Ψ x` is nonnegative for nonnegative resistances.
-/
lemma Psi_nonneg {x : Fin K → ℝ} (hx : 0 ≤ x) : 0 ≤ F.Psi x := by
  intro i;
  convert EIGS.Network.effRes_nonneg ( F.R i ) ( F.βplus i ) ( F.βminus i ) ( F.connected i ) hx using 1

/-! ### The two directions of the substitution recursion -/

/-
(≥) The base resistance at `Ψ x` lower-bounds the substituted resistance.  Every
unit flow on `G.subst F` projects to a unit flow on `G`, and its energy decomposes
copy-by-copy with each copy contributing at least `substProj(e)² · R_eff(R_{c e})`.
-/
lemma subst_effRes_ge (a b : G.V) (hGconn : Nonempty (G.Flow a b))
    {x : Fin K → ℝ} (hx : 0 ≤ x) :
    G.effRes a b hGconn (F.Psi x)
      ≤ (G.subst F).effRes (Sum.inl a) (Sum.inl b) (G.subst_connected F a b hGconn) x := by
  rw [ Network.effRes_eq_iInf, Network.effRes_eq_iInf ];
  refine' le_csInf _ _;
  · exact ⟨ _, ⟨ Classical.choice ( subst_connected G F a b hGconn ), rfl ⟩ ⟩;
  · rintro _ ⟨ θ', rfl ⟩;
    refine' le_trans _ ( show ( G.subst F ).energyNetwork θ'.1 x ≥ ∑ e, ( G.substProj F θ'.1 e ) ^ 2 * F.Psi x ( G.color e ) from _ );
    · refine' le_trans ( ciInf_le _ ⟨ G.substProj F θ'.1, substProj_isUnitFlow G F a b θ'.1 θ'.2 ⟩ ) _;
      · exact ⟨ 0, Set.forall_mem_range.mpr fun θ => energyNetwork_nonneg _ _ <| Psi_nonneg F hx ⟩;
      · unfold Network.energyNetwork; simp +decide [ mul_comm ] ;
    · rw [ Network.energyNetwork_subst ];
      refine' Finset.sum_le_sum fun e _ => _;
      convert EIGS.Network.energy_ge_sq_mul_effRes ( F.R ( G.color e ) ) ( F.βplus ( G.color e ) ) ( F.βminus ( G.color e ) ) ( F.connected ( G.color e ) ) hx _ using 1;
      exact fun u => EIGS.Network.substRestrict_tflow G F a b θ'.1 θ'.2 e u

/-
(≤) The substituted resistance is at most the base resistance at `Ψ x`.  Any unit
flow on `G` lifts, by scaling near-optimal rule flows, to a unit flow on `G.subst F`
with energy approaching `ℰ_G(θ_G, Ψ x)`.
-/
lemma subst_effRes_le (a b : G.V) (hGconn : Nonempty (G.Flow a b))
    {x : Fin K → ℝ} (hx : 0 ≤ x) :
    (G.subst F).effRes (Sum.inl a) (Sum.inl b) (G.subst_connected F a b hGconn) x
      ≤ G.effRes a b hGconn (F.Psi x) := by
  rw [Network.effRes_eq_iInf, Network.effRes_eq_iInf];
  refine' le_ciInf fun θG => _;
  -- Fix $\delta > 0$. Set $\epsilon := \delta / (S + 1) > 0$.
  have h_eps : ∀ δ > 0, ∃ ε > 0, ε * (∑ e : G.E, (θG.val e)^2) ≤ δ ∧ ∀ i, ∃ ψ : (F.R i).Flow (F.βplus i) (F.βminus i), (F.R i).energyNetwork ψ.val x < F.Psi x i + ε := by
    intro δ hδ_pos
    set S := ∑ e : G.E, (θG.val e)^2
    set ε := min (δ / (S + 1)) 1
    have hε_pos : 0 < ε := by
      exact lt_min ( div_pos hδ_pos ( add_pos_of_nonneg_of_pos ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) zero_lt_one ) ) zero_lt_one
    have hε_bound : ε * S ≤ δ := by
      nlinarith [ min_le_left ( δ / ( S + 1 ) ) 1, min_le_right ( δ / ( S + 1 ) ) 1, mul_div_cancel₀ δ ( show ( S + 1 ) ≠ 0 by exact ne_of_gt ( add_pos_of_nonneg_of_pos ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) zero_lt_one ) ), show 0 ≤ S by exact Finset.sum_nonneg fun _ _ => sq_nonneg _ ]
    have hε_optimal : ∀ i, ∃ ψ : (F.R i).Flow (F.βplus i) (F.βminus i), (F.R i).energyNetwork ψ.val x < F.Psi x i + ε := by
      intro i
      have h_inf : F.Psi x i = ⨅ ψ : (F.R i).Flow (F.βplus i) (F.βminus i), (F.R i).energyNetwork ψ.val x := by
        convert Network.effRes_eq_iInf ( F.R i ) ( F.βplus i ) ( F.βminus i ) ( F.connected i ) x using 1;
      exact by rcases exists_lt_of_csInf_lt ( show Set.Nonempty ( Set.range fun ψ : ( F.R i ).Flow ( F.βplus i ) ( F.βminus i ) => ( F.R i ).energyNetwork ( ψ.val ) x ) from ⟨ _, ⟨ Classical.choice ( F.connected i ), rfl ⟩ ⟩ ) ( show ⨅ ψ : ( F.R i ).Flow ( F.βplus i ) ( F.βminus i ), ( F.R i ).energyNetwork ( ψ.val ) x < F.Psi x i + ε from by linarith ) with ⟨ ψ, ⟨ ψ', rfl ⟩, hψ ⟩ ; exact ⟨ ψ', hψ ⟩ ;
    use ε, hε_pos, hε_bound, hε_optimal;
  refine' le_of_forall_pos_le_add fun δ δpos => _;
  obtain ⟨ ε, εpos, hε₁, hε₂ ⟩ := h_eps δ δpos;
  choose ψ hψ using hε₂;
  refine' le_trans ( ciInf_le _ ⟨ G.substLift F θG.val ( fun i => ( ψ i ).val ), substLift_isUnitFlow G F a b θG.val θG.property ( fun i => ( ψ i ).val ) ( fun i => ( ψ i ).property ) ⟩ ) _;
  · exact ⟨ 0, Set.forall_mem_range.mpr fun θ => energyNetwork_nonneg _ _ hx ⟩;
  · rw [ Network.energyNetwork_substLift ];
    refine' le_trans ( Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left ( le_of_lt ( hψ _ ) ) ( sq_nonneg _ ) ) _;
    simp +decide [ mul_add, Finset.sum_add_distrib, mul_comm, Network.energyNetwork ];
    rwa [ ← Finset.mul_sum _ _ _ ]

/-! ### The substitution recursion -/

/-- **Resistance substitution recursion (Lemma 2.4, geometric part).**  The
effective resistance of the substituted network equals `Ψ` applied to the effective
resistance of the base network. -/
theorem subst_effRes (a b : G.V) (hGconn : Nonempty (G.Flow a b))
    {x : Fin K → ℝ} (hx : 0 ≤ x) :
    (G.subst F).effRes (Sum.inl a) (Sum.inl b) (G.subst_connected F a b hGconn) x
      = G.effRes a b hGconn (F.Psi x) :=
  le_antisymm (G.subst_effRes_le F a b hGconn hx) (G.subst_effRes_ge F a b hGconn hx)

/-! ### Iterating the substitution: `ℛ(Ξⁿ) = Ψⁿ`

Iterating the substitution `n` times realises `Ψⁿ` as the effective resistance of a
genuine network.  For the single-edge base network of colour `ι` (the EIGS initial
graph `Ξ⁰`), the effective resistance of the `n`-fold substituted network at
resistance vector `x` is exactly `(Ψⁿ x)_ι`. -/

/-- The `n`-fold substitution of a base network by the rule family `F`. -/
noncomputable def substIter : ℕ → Network K :=
  fun n => Nat.rec G (fun _ H => H.subst F) n

@[simp] lemma substIter_zero : G.substIter F 0 = G := rfl

@[simp] lemma substIter_succ (n : ℕ) :
    G.substIter F (n + 1) = (G.substIter F n).subst F := rfl

/-- The image of a base terminal in the `n`-fold substituted network (`n`-fold
`Sum.inl`). -/
def inlIter (a : G.V) : (n : ℕ) → (G.substIter F n).V :=
  fun n => Nat.rec (motive := fun n => (G.substIter F n).V) a (fun _ ih => Sum.inl ih) n

@[simp] lemma inlIter_zero (a : G.V) : G.inlIter F a 0 = a := rfl

@[simp] lemma inlIter_succ (a : G.V) (n : ℕ) :
    G.inlIter F a (n + 1) = Sum.inl (G.inlIter F a n) := rfl

/-- Connectivity of the iterated substituted network between the iterated terminals. -/
lemma substIter_connected (a b : G.V) (hGconn : Nonempty (G.Flow a b)) (n : ℕ) :
    Nonempty ((G.substIter F n).Flow (G.inlIter F a n) (G.inlIter F b n)) := by
  induction n with
  | zero => exact hGconn
  | succ n ih =>
      exact (G.substIter F n).subst_connected F (G.inlIter F a n) (G.inlIter F b n) ih

/-
**Iterated resistance substitution recursion.**  The effective resistance of the
`n`-fold substituted network equals `Ψⁿ` applied to the effective resistance of the
base network.
-/
theorem substIter_effRes (F : RuleFamily K) (a b : G.V) (hGconn : Nonempty (G.Flow a b))
    {x : Fin K → ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (G.substIter F n).effRes (G.inlIter F a n) (G.inlIter F b n)
        (G.substIter_connected F a b hGconn n) x
      = G.effRes a b hGconn (F.Psi^[n] x) := by
  induction' n with n ih generalizing x;
  · convert rfl;
  · convert ih ( Psi_nonneg F hx ) using 1;
    convert Network.subst_effRes ( G.substIter F n ) F ( G.inlIter F a n ) ( G.inlIter F b n ) ( G.substIter_connected F a b hGconn n ) hx using 1

/-- The single directed edge of colour `ι` (the EIGS initial graph `Ξ⁰`): two
vertices `false` (tail) and `true` (head), one edge. -/
def singleEdge (ι : Fin K) : Network K where
  V := Bool
  E := Unit
  fintypeV := inferInstance
  decEqV := inferInstance
  fintypeE := inferInstance
  tail := fun _ => false
  head := fun _ => true
  color := fun _ => ι

/-
The single-edge network is connected between its two terminals.
-/
lemma singleEdge_connected (ι : Fin K) :
    Nonempty ((singleEdge ι).Flow false true) := by
  refine' ⟨ fun _ => 1, _ ⟩ ; simp +decide [ Network.IsUnitFlow ];
  unfold Network.div; aesop;

/-
The effective resistance of the single edge of colour `ι` is just the
resistance `x ι` of that colour.
-/
lemma singleEdge_effRes (ι : Fin K) (x : Fin K → ℝ) :
    (singleEdge ι).effRes false true (singleEdge_connected ι) x = x ι := by
  convert Network.effRes_eq_iInf ( singleEdge ι ) false true ( singleEdge_connected ι ) x using 1;
  convert ( ciInf_const ).symm using 2;
  · ext ⟨ θ, hθ ⟩ ; simp +decide [ Network.energyNetwork, singleEdge ] ;
    have := hθ false; ( have := hθ true; ( unfold singleEdge at *; simp_all +decide [ Network.div ] ; ) );
  · exact singleEdge_connected ι

/-- **`ℛ(Ξⁿ) = Ψⁿ` on a genuine network.**  The effective resistance of the `n`-fold
substitution of the single edge of colour `ι`, evaluated at resistance vector `x`,
equals `(Ψⁿ x)_ι` — Lemma 2.4 realised on an explicit electrical network. -/
theorem singleEdge_substIter_effRes (ι : Fin K) (F : RuleFamily K)
    {x : Fin K → ℝ} (hx : 0 ≤ x) (n : ℕ) :
    ((singleEdge ι).substIter F n).effRes
        ((singleEdge ι).inlIter F false n) ((singleEdge ι).inlIter F true n)
        ((singleEdge ι).substIter_connected F false true (singleEdge_connected ι) n) x
      = (F.Psi^[n] x) ι := by
  rw [(singleEdge ι).substIter_effRes F false true (singleEdge_connected ι) hx n,
    singleEdge_effRes]

end Network

end EIGS
