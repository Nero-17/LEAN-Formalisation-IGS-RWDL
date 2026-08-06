import Mathlib
import RequestProject.Section1

/-!
# The vertex-identification quotient of an EIGS (Section 1)

`Section1.lean` constructs the substitution networks `Ξⁿ` only at the level of
*edges and colours* (`XiEdge`, `XiCol`), and therefore had to take the
vertex-level data — the **vertex-identification quotient**, the resulting
**degree recursion**, and the graph metric — as cited hypotheses (`[36]`).

This file builds the vertex-identification quotient **concretely**.  The key
observation is that the quotient that glues each rule copy `R_{𝒞(e)}` to the
skeleton edge `e` (identifying the planting vertices `β⁺, β⁻` of the copy with the
tail/head of `e`) has an explicit *normal form*: every vertex of `Ξⁿ⁺¹` is either

* an old (skeleton) vertex of `Ξⁿ`, or
* a *private interior* vertex `(e, w)` of a unique rule copy, i.e. a non-planting
  vertex `w ∈ V(R_{𝒞(e)}) ∖ {β⁺, β⁻}`.

Realising the quotient by this normal form makes the vertex type a concrete
`Fintype` with `DecidableEq`, and turns the gluing relation into the explicit
`embedRuleVtx` map.  This is the gate that unlocks the metric and the degree
recursion.

## What is built and proved here

* `XiVtx 𝓘 n` — the vertex type of `Ξⁿ`, with `Fintype`/`DecidableEq` instances.
* `XiTail`, `XiHead` — the endpoint maps, defined through `embedRuleVtx`
  (the identification of planting vertices with skeleton endpoints).
* `XiGraph 𝓘 n` — the full edge-coloured directed multigraph `Ξⁿ`.
* Gating lemmas: old vertices embed injectively (`xiOld_injective`); the planting
  vertices of a copy are exactly the skeleton endpoints
  (`embedRuleVtx_plantPlus`, `embedRuleVtx_plantMinus`).
-/

namespace EIGS

open scoped BigOperators

variable {K : ℕ}

/-- The vertex type of `Ξⁿ`.  `Ξ⁰` is a single directed edge with two endpoints
(`false` = tail, `true` = head).  A vertex of `Ξⁿ⁺¹` is, in normal form, either an
old skeleton vertex of `Ξⁿ` (`Sum.inl`) or a *private interior* vertex of a rule
copy: a pair `(e, w)` with `e ∈ E(Ξⁿ)` and `w` a non-planting vertex of
`R_{𝒞(e)}` (`Sum.inr`). -/
def XiVtx (𝓘 : EIGSData K) : ℕ → Type
  | 0 => Bool
  | (n+1) => XiVtx 𝓘 n ⊕
      (Σ e : XiEdge 𝓘.toRuleData n,
        {w : (𝓘.rule (XiCol 𝓘.toRuleData n e)).V //
            w ≠ 𝓘.plantPlus (XiCol 𝓘.toRuleData n e) ∧
            w ≠ 𝓘.plantMinus (XiCol 𝓘.toRuleData n e)})

instance XiVtxFintype (𝓘 : EIGSData K) : (n : ℕ) → Fintype (XiVtx 𝓘 n)
  | 0 => inferInstanceAs (Fintype Bool)
  | (n+1) => by
      letI := XiVtxFintype 𝓘 n
      exact inferInstanceAs (Fintype (XiVtx 𝓘 n ⊕ _))

instance XiVtxDecEq (𝓘 : EIGSData K) : (n : ℕ) → DecidableEq (XiVtx 𝓘 n)
  | 0 => inferInstanceAs (DecidableEq Bool)
  | (n+1) => by
      letI := XiVtxDecEq 𝓘 n
      exact inferInstanceAs (DecidableEq (XiVtx 𝓘 n ⊕ _))

/-- Embed a vertex `w` of the rule copy attached to skeleton edge `e` into
`V(Ξⁿ⁺¹)`, given the skeleton endpoints `te = tail(e)` and `he = head(e)`.  The
planting vertices `β⁺, β⁻` are identified with `te, he` respectively; every other
vertex is its own private interior vertex `(e, w)`.  This is the
vertex-identification quotient. -/
def embedRuleVtx (𝓘 : EIGSData K) (n : ℕ) (e : XiEdge 𝓘.toRuleData n)
    (te he : XiVtx 𝓘 n) (w : (𝓘.rule (XiCol 𝓘.toRuleData n e)).V) :
    XiVtx 𝓘 (n+1) :=
  if hp : w = 𝓘.plantPlus (XiCol 𝓘.toRuleData n e) then Sum.inl te
  else if hm : w = 𝓘.plantMinus (XiCol 𝓘.toRuleData n e) then Sum.inl he
  else Sum.inr ⟨e, ⟨w, hp, hm⟩⟩

/-- The endpoint maps `(tail, head)` of `Ξⁿ`, defined together by recursion: at
level `n+1` an edge `p = ⟨e, e'⟩` has endpoints obtained by embedding the rule
endpoints of `e'` via `embedRuleVtx`, using the already-computed skeleton endpoints
of `e`. -/
def XiEnds (𝓘 : EIGSData K) :
    (n : ℕ) → XiEdge 𝓘.toRuleData n → XiVtx 𝓘 n × XiVtx 𝓘 n
  | 0 => fun _ => (false, true)
  | (n+1) => fun p =>
      let ends := XiEnds 𝓘 n p.1
      (embedRuleVtx 𝓘 n p.1 ends.1 ends.2 ((𝓘.rule _).tail p.2),
       embedRuleVtx 𝓘 n p.1 ends.1 ends.2 ((𝓘.rule _).head p.2))

/-- Tail (source) map of `Ξⁿ`. -/
def XiTail (𝓘 : EIGSData K) (n : ℕ) (e : XiEdge 𝓘.toRuleData n) : XiVtx 𝓘 n :=
  (XiEnds 𝓘 n e).1

/-- Head (target) map of `Ξⁿ`. -/
def XiHead (𝓘 : EIGSData K) (n : ℕ) (e : XiEdge 𝓘.toRuleData n) : XiVtx 𝓘 n :=
  (XiEnds 𝓘 n e).2

/-- The full edge-coloured directed multigraph `Ξⁿ` (Definition 1.1). -/
def XiGraph (𝓘 : EIGSData K) (n : ℕ) : ColGraph K where
  V := XiVtx 𝓘 n
  E := XiEdge 𝓘.toRuleData n
  tail := XiTail 𝓘 n
  head := XiHead 𝓘 n
  col := XiCol 𝓘.toRuleData n

/-! ### Gating lemmas for the vertex-identification quotient -/

/-- The old (skeleton) vertices of `Ξⁿ` embed injectively into `Ξⁿ⁺¹`: this is the
statement that the identification quotient does not collapse distinct old vertices. -/
lemma xiOld_injective (𝓘 : EIGSData K) (n : ℕ) :
    Function.Injective (Sum.inl : XiVtx 𝓘 n → XiVtx 𝓘 (n+1)) :=
  Sum.inl_injective

/-- The positive planting vertex `β⁺` of the rule copy on edge `e` is identified
with the tail-endpoint `te` of `e` (the vertex-identification quotient). -/
@[simp] lemma embedRuleVtx_plantPlus (𝓘 : EIGSData K) (n : ℕ)
    (e : XiEdge 𝓘.toRuleData n) (te he : XiVtx 𝓘 n) :
    embedRuleVtx 𝓘 n e te he (𝓘.plantPlus (XiCol 𝓘.toRuleData n e)) = Sum.inl te := by
  simp [embedRuleVtx]

/-- The negative planting vertex `β⁻` of the rule copy on edge `e` is identified
with the head-endpoint `he` of `e`. -/
@[simp] lemma embedRuleVtx_plantMinus (𝓘 : EIGSData K) (n : ℕ)
    (e : XiEdge 𝓘.toRuleData n) (te he : XiVtx 𝓘 n) :
    embedRuleVtx 𝓘 n e te he (𝓘.plantMinus (XiCol 𝓘.toRuleData n e)) = Sum.inl he := by
  have hne := (𝓘.plant_ne (XiCol 𝓘.toRuleData n e)).symm
  simp [embedRuleVtx, hne]

/-- An interior (non-planting) rule vertex `w` becomes its own private vertex
`(e, w)` of `Ξⁿ⁺¹`. -/
lemma embedRuleVtx_interior (𝓘 : EIGSData K) (n : ℕ)
    (e : XiEdge 𝓘.toRuleData n) (te he : XiVtx 𝓘 n)
    {w : (𝓘.rule (XiCol 𝓘.toRuleData n e)).V}
    (hp : w ≠ 𝓘.plantPlus (XiCol 𝓘.toRuleData n e))
    (hm : w ≠ 𝓘.plantMinus (XiCol 𝓘.toRuleData n e)) :
    embedRuleVtx 𝓘 n e te he w = Sum.inr ⟨e, ⟨w, hp, hm⟩⟩ := by
  simp [embedRuleVtx, hp, hm]

/-- Unfolding of the tail endpoint at a successor level. -/
lemma XiTail_succ (𝓘 : EIGSData K) (n : ℕ) (p : XiEdge 𝓘.toRuleData (n+1)) :
    XiTail 𝓘 (n+1) p =
      embedRuleVtx 𝓘 n p.1 (XiTail 𝓘 n p.1) (XiHead 𝓘 n p.1)
        ((𝓘.rule _).tail p.2) := rfl

/-- Unfolding of the head endpoint at a successor level. -/
lemma XiHead_succ (𝓘 : EIGSData K) (n : ℕ) (p : XiEdge 𝓘.toRuleData (n+1)) :
    XiHead 𝓘 (n+1) p =
      embedRuleVtx 𝓘 n p.1 (XiTail 𝓘 n p.1) (XiHead 𝓘 n p.1)
        ((𝓘.rule _).head p.2) := rfl

/-! ### The graph metric on `Ξⁿ` (unlocked by the vertex quotient)

With vertices in hand, the substitution network carries its graph metric.  We take
the underlying simple graph (symmetrising the directed edge relation and dropping
loops) and its combinatorial distance; this is the metric whose diameter growth is
the cited `[38]` input. -/

/-- The underlying simple graph of `Ξⁿ`: two distinct vertices are adjacent iff some
edge joins them (in either orientation). -/
def XiSimpleGraph (𝓘 : EIGSData K) (n : ℕ) : SimpleGraph (XiVtx 𝓘 n) :=
  SimpleGraph.fromRel (fun u v =>
    ∃ e : XiEdge 𝓘.toRuleData n,
      (XiTail 𝓘 n e = u ∧ XiHead 𝓘 n e = v))

/-- The graph distance on `Ξⁿ` (the combinatorial metric). -/
noncomputable def XiDist (𝓘 : EIGSData K) (n : ℕ) (u v : XiVtx 𝓘 n) : ℕ :=
  (XiSimpleGraph 𝓘 n).dist u v

/-! ### Bridge to the electrical-network / random-walk layer

The vertex quotient turns `Ξⁿ` into a genuine finite `K`-coloured network
(`Section2Network.Network`), so the unit-flow / effective-resistance / random-walk
machinery applies to it directly. -/

/-- `Ξⁿ` as a finite `K`-coloured electrical network. -/
def XiNetwork (𝓘 : EIGSData K) (n : ℕ) : Network K where
  V := XiVtx 𝓘 n
  E := XiEdge 𝓘.toRuleData n
  fintypeV := inferInstance
  decEqV := inferInstance
  fintypeE := inferInstance
  tail := XiTail 𝓘 n
  head := XiHead 𝓘 n
  color := XiCol 𝓘.toRuleData n

/-! ### The degree recursion (the degree matrix `N`)

The vertex quotient lets us prove the **degree substitution recursion** that
`Section1.degree_geometric_growth` previously took as the cited `[36]` hypothesis.
For a *fixed* vertex tracked forward by the embedding `Sum.inl`, the oriented
coloured degrees `(outDeg, inDeg)` transform by a constant `2K × 2K` matrix `N`.

The key combinatorial fact: an edge `(e, e')` of `Ξⁿ⁺¹` has tail `Sum.inl v'`
precisely when the rule edge `e'` has its tail at a planting vertex of `R_{𝒯(e)}`
that the quotient glues to `v'`, i.e. either `tail(e') = β⁺` and `tailₙ(e) = v'`,
or `tail(e') = β⁻` and `headₙ(e) = v'`. -/

/-- Number of colour-`i` edges of `Ξⁿ` whose **tail** is the vertex `v`
(the colour-`i` out-degree of `v`). -/
def outDeg (𝓘 : EIGSData K) (n : ℕ) (v : XiVtx 𝓘 n) (i : Fin K) : ℕ :=
  (Finset.univ.filter (fun e : XiEdge 𝓘.toRuleData n =>
    XiTail 𝓘 n e = v ∧ XiCol 𝓘.toRuleData n e = i)).card

/-- Number of colour-`i` edges of `Ξⁿ` whose **head** is the vertex `v`
(the colour-`i` in-degree of `v`). -/
def inDeg (𝓘 : EIGSData K) (n : ℕ) (v : XiVtx 𝓘 n) (i : Fin K) : ℕ :=
  (Finset.univ.filter (fun e : XiEdge 𝓘.toRuleData n =>
    XiHead 𝓘 n e = v ∧ XiCol 𝓘.toRuleData n e = i)).card

/-- Number of colour-`j` edges of the rule graph `R_i` whose **tail** is the
vertex `s` (used with `s = β⁺, β⁻`). -/
def ruleTailDeg (𝓘 : EIGSData K) (i : Fin K) (s : (𝓘.rule i).V) (j : Fin K) : ℕ :=
  (Finset.univ.filter (fun e' : (𝓘.rule i).E =>
    (𝓘.rule i).tail e' = s ∧ (𝓘.rule i).col e' = j)).card

/-- Number of colour-`j` edges of the rule graph `R_i` whose **head** is the
vertex `s` (used with `s = β⁺, β⁻`). -/
def ruleHeadDeg (𝓘 : EIGSData K) (i : Fin K) (s : (𝓘.rule i).V) (j : Fin K) : ℕ :=
  (Finset.univ.filter (fun e' : (𝓘.rule i).E =>
    (𝓘.rule i).head e' = s ∧ (𝓘.rule i).col e' = j)).card

/-
**Degree recursion, out-degrees.**  The colour-`j` out-degree of an old vertex
`Sum.inl v'` in `Ξⁿ⁺¹` is governed by the level-`n` oriented degrees of `v'` and
the rule out-degrees at the planting vertices.
-/
theorem outDeg_inl (𝓘 : EIGSData K) (n : ℕ) (v' : XiVtx 𝓘 n) (j : Fin K) :
    outDeg 𝓘 (n+1) (Sum.inl v') j =
      (∑ i, outDeg 𝓘 n v' i * ruleTailDeg 𝓘 i (𝓘.plantPlus i) j)
        + (∑ i, inDeg 𝓘 n v' i * ruleTailDeg 𝓘 i (𝓘.plantMinus i) j) := by
  have h_sum : Finset.card (Finset.filter (fun e : XiEdge 𝓘.toRuleData (n + 1) => XiTail 𝓘 (n + 1) e = Sum.inl v' ∧ XiCol 𝓘.toRuleData (n + 1) e = j) Finset.univ) = ∑ e : XiEdge 𝓘.toRuleData n, Finset.card (Finset.filter (fun e' : (𝓘.rule (XiCol 𝓘.toRuleData n e)).E => embedRuleVtx 𝓘 n e (XiTail 𝓘 n e) (XiHead 𝓘 n e) ((𝓘.rule (XiCol 𝓘.toRuleData n e)).tail e') = Sum.inl v' ∧ (𝓘.rule (XiCol 𝓘.toRuleData n e)).col e' = j) Finset.univ) := by
    simp +decide only [Finset.card_filter];
    rw [ Finset.sum_sigma' ];
    congr! 2;
  -- Split the sum into two parts: one for edges where the tail is v' and one for edges where the head is v'.
  have h_split : ∑ e : XiEdge 𝓘.toRuleData n, Finset.card (Finset.filter (fun e' : (𝓘.rule (XiCol 𝓘.toRuleData n e)).E => embedRuleVtx 𝓘 n e (XiTail 𝓘 n e) (XiHead 𝓘 n e) ((𝓘.rule (XiCol 𝓘.toRuleData n e)).tail e') = Sum.inl v' ∧ (𝓘.rule (XiCol 𝓘.toRuleData n e)).col e' = j) Finset.univ) = ∑ e : XiEdge 𝓘.toRuleData n, (if XiTail 𝓘 n e = v' then ruleTailDeg 𝓘 (XiCol 𝓘.toRuleData n e) (𝓘.plantPlus (XiCol 𝓘.toRuleData n e)) j else 0) + ∑ e : XiEdge 𝓘.toRuleData n, (if XiHead 𝓘 n e = v' then ruleTailDeg 𝓘 (XiCol 𝓘.toRuleData n e) (𝓘.plantMinus (XiCol 𝓘.toRuleData n e)) j else 0) := by
    rw [ ← Finset.sum_add_distrib ] ; refine' Finset.sum_congr rfl fun e _ => _ ; split_ifs <;> simp_all +decide [ ruleTailDeg ] ;
    · rw [ ← Finset.card_union_of_disjoint ];
      · congr with e' ; simp +decide [ embedRuleVtx ];
        grind +extAll;
      · simp +contextual [ Finset.disjoint_left, EIGSData.plant_ne ];
    · congr with e' ; simp +decide [ *, embedRuleVtx ];
      grind;
    · congr with e' ; simp +decide [ embedRuleVtx ];
      grind +suggestions;
    · intro x hx; contrapose! hx; simp_all +decide [ embedRuleVtx ] ;
      grind;
  convert h_sum.trans h_split using 2;
  · unfold outDeg; simp +decide [ Finset.sum_ite ] ;
    simp +decide only [Finset.card_filter, Finset.sum_mul];
    rw [ Finset.sum_comm ];
    rw [ Finset.sum_filter ] ; congr ; ext ; aesop;
  · unfold inDeg;
    simp +decide only [Finset.card_filter, Finset.sum_mul _ _ _];
    rw [ Finset.sum_comm ];
    exact Finset.sum_congr rfl fun x hx => by rw [ Finset.sum_eq_single ( XiCol 𝓘.toRuleData n x ) ] <;> aesop;

/-
**Degree recursion, in-degrees.**  The colour-`j` in-degree of an old vertex
`Sum.inl v'` in `Ξⁿ⁺¹` is governed by the level-`n` oriented degrees of `v'` and
the rule in-degrees at the planting vertices.
-/
theorem inDeg_inl (𝓘 : EIGSData K) (n : ℕ) (v' : XiVtx 𝓘 n) (j : Fin K) :
    inDeg 𝓘 (n+1) (Sum.inl v') j =
      (∑ i, outDeg 𝓘 n v' i * ruleHeadDeg 𝓘 i (𝓘.plantPlus i) j)
        + (∑ i, inDeg 𝓘 n v' i * ruleHeadDeg 𝓘 i (𝓘.plantMinus i) j) := by
  unfold inDeg; simp +decide [ Finset.sum_ite ] ;
  have h_sum : Finset.card (Finset.filter (fun e : XiEdge 𝓘.toRuleData (n + 1) => XiHead 𝓘 (n + 1) e = Sum.inl v' ∧ XiCol 𝓘.toRuleData (n + 1) e = j) Finset.univ) = ∑ e : XiEdge 𝓘.toRuleData n, Finset.card (Finset.filter (fun e' : (𝓘.rule (XiCol 𝓘.toRuleData n e)).E => embedRuleVtx 𝓘 n e (XiTail 𝓘 n e) (XiHead 𝓘 n e) ((𝓘.rule (XiCol 𝓘.toRuleData n e)).head e') = Sum.inl v' ∧ (𝓘.rule (XiCol 𝓘.toRuleData n e)).col e' = j) Finset.univ) := by
    simp +decide only [Finset.card_filter];
    rw [ Finset.sum_sigma' ] ; aesop;
  convert h_sum using 1;
  have h_split : ∀ e : XiEdge 𝓘.toRuleData n, Finset.card (Finset.filter (fun e' : (𝓘.rule (XiCol 𝓘.toRuleData n e)).E => embedRuleVtx 𝓘 n e (XiTail 𝓘 n e) (XiHead 𝓘 n e) ((𝓘.rule (XiCol 𝓘.toRuleData n e)).head e') = Sum.inl v' ∧ (𝓘.rule (XiCol 𝓘.toRuleData n e)).col e' = j) Finset.univ) = (if XiTail 𝓘 n e = v' then ruleHeadDeg 𝓘 (XiCol 𝓘.toRuleData n e) (𝓘.plantPlus (XiCol 𝓘.toRuleData n e)) j else 0) + (if XiHead 𝓘 n e = v' then ruleHeadDeg 𝓘 (XiCol 𝓘.toRuleData n e) (𝓘.plantMinus (XiCol 𝓘.toRuleData n e)) j else 0) := by
    intro e; split_ifs <;> simp_all +decide [ ruleHeadDeg ] ;
    · rw [ ← Finset.card_union_of_disjoint ];
      · congr with e' ; simp +decide [ embedRuleVtx ];
        grind;
      · simp +contextual [ Finset.disjoint_left, EIGSData.plant_ne ];
    · congr with e' ; simp +decide [ *, embedRuleVtx ];
      grind;
    · congr with e' ; simp +decide [ *, embedRuleVtx ];
      grind +suggestions;
    · intro x hx; contrapose! hx; simp_all +decide [ embedRuleVtx ] ;
      grind +splitIndPred;
  simp +decide only [h_split, Finset.sum_add_distrib];
  congr! 1;
  · unfold outDeg; simp +decide [ Finset.sum_ite ] ;
    simp +decide only [Finset.card_filter, Finset.sum_mul];
    rw [ Finset.sum_comm ];
    rw [ Finset.sum_filter ] ; congr ; ext ; aesop;
  · simp +decide only [Finset.card_filter, Finset.sum_mul];
    rw [ Finset.sum_comm ] ; congr ; ext ; aesop;

/-! ### The combined degree matrix `N` and geometric degree growth

The two recursions above assemble into a single linear recursion on the oriented
degree state `(outDeg, inDeg) : Fin K ⊕ Fin K → ℝ`, governed by the constant
`2K × 2K` **degree matrix** `N`.  Tracking a *fixed* vertex forward by the
embedding `Sum.inl` then yields the geometric degree growth
`κ_{Ξⁿ}(v) ≈ ρ(N)ⁿ`, exactly the statement `Section1.degree_geometric_growth` had
to assume — here it is reduced to the Perron–Frobenius eigenpair of `N`. -/

/-- The oriented degree state of a vertex `v` of `Ξⁿ`, indexed by `Fin K ⊕ Fin K`
(`inl i` = colour-`i` out-degree, `inr i` = colour-`i` in-degree). -/
def degVec (𝓘 : EIGSData K) (n : ℕ) (v : XiVtx 𝓘 n) : Fin K ⊕ Fin K → ℝ :=
  fun s => Sum.elim (fun i => (outDeg 𝓘 n v i : ℝ)) (fun i => (inDeg 𝓘 n v i : ℝ)) s

/-- The **degree matrix** `N` of the EIGS, of size `2K × 2K` (Definition 1.1).  The
block structure records how out/in degrees at the planting vertices of each rule
produce out/in degrees one level up. -/
def degreeMatrix (𝓘 : EIGSData K) : Matrix (Fin K ⊕ Fin K) (Fin K ⊕ Fin K) ℝ :=
  fun s t => Sum.elim
    (fun i => Sum.elim
      (fun j => (ruleTailDeg 𝓘 i (𝓘.plantPlus i) j : ℝ))
      (fun j => (ruleHeadDeg 𝓘 i (𝓘.plantPlus i) j : ℝ)) t)
    (fun i => Sum.elim
      (fun j => (ruleTailDeg 𝓘 i (𝓘.plantMinus i) j : ℝ))
      (fun j => (ruleHeadDeg 𝓘 i (𝓘.plantMinus i) j : ℝ)) t) s

lemma degreeMatrix_nonneg (𝓘 : EIGSData K) (s t : Fin K ⊕ Fin K) :
    0 ≤ degreeMatrix 𝓘 s t := by
  cases s <;> cases t <;> exact Nat.cast_nonneg _

/-
**The degree recursion in matrix form.**  For an old vertex `Sum.inl v'`, the
oriented degree state one level up is `degVec(v') ·ᵥ N`.
-/
theorem degVec_inl (𝓘 : EIGSData K) (n : ℕ) (v' : XiVtx 𝓘 n) :
    degVec 𝓘 (n+1) (Sum.inl v') = Matrix.vecMul (degVec 𝓘 n v') (degreeMatrix 𝓘) := by
  ext t;
  cases t <;> simp +decide [ degVec, Matrix.vecMul, dotProduct ];
  · rw [ outDeg_inl ] ; aesop;
  · convert congr_arg ( ( ↑ ) : ℕ → ℝ ) ( inDeg_inl 𝓘 n v' ‹_› ) using 1;
    simp +decide [ degreeMatrix ]

/-
**Geometric-growth engine over an arbitrary finite index** (generalising
`Section1.vecMul_recursion_geometric` from `Fin K` to any nonempty finite index,
as needed for the `2K`-dimensional degree state).  If a nonnegative row-vector
sequence obeys `seq (n+1) = seq n ·ᵥ A` with `A ≥ 0` having a positive right
eigenvector `u` (eigenvalue `ρ > 0`) and `∑ (seq 0) u > 0`, then the entry sum of
`seq n` grows like `ρⁿ`.
-/
theorem vecMul_recursion_geometric_general {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {A : Matrix ι ι ℝ} {seq : ℕ → ι → ℝ} {u : ι → ℝ} {ρ : ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hu : ∀ i, 0 < u i)
    (hseq0 : ∀ i, 0 ≤ seq 0 i) (hwu : 0 < ∑ i, seq 0 i * u i)
    (hrec : ∀ n, seq (n+1) = Matrix.vecMul (seq n) A)
    (heig : A.mulVec u = ρ • u) (hρ : 0 < ρ) :
    ∃ c C, 0 < c ∧ 0 < C ∧ ∀ n,
      c * ρ ^ n ≤ ∑ j, seq n j ∧ ∑ j, seq n j ≤ C * ρ ^ n := by
  obtain ⟨c, C, hc, hC⟩ : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n, c * ρ ^ n ≤ ∑ j, (Matrix.vecMul (seq 0) (A ^ n)) j ∧ ∑ j, (Matrix.vecMul (seq 0) (A ^ n)) j ≤ C * ρ ^ n := by
    -- By the properties of the geometric series and the positivity of the sums, we can find such constants $c$ and $C$.
    obtain ⟨umin, humin⟩ : ∃ umin : ℝ, 0 < umin ∧ ∀ i, umin ≤ u i := by
      exact ⟨ Finset.min' ( Finset.univ.image u ) ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ ( Classical.arbitrary ι ) ) ⟩, by have := Finset.min'_mem ( Finset.univ.image u ) ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ ( Classical.arbitrary ι ) ) ⟩ ; aesop, fun i => Finset.min'_le _ _ ( Finset.mem_image_of_mem _ ( Finset.mem_univ i ) ) ⟩;
    obtain ⟨umax, humax⟩ : ∃ umax : ℝ, 0 < umax ∧ ∀ i, u i ≤ umax := by
      exact ⟨ ∑ i, u i, Finset.sum_pos ( fun _ _ => hu _ ) Finset.univ_nonempty, fun i => Finset.single_le_sum ( fun i _ => le_of_lt ( hu i ) ) ( Finset.mem_univ i ) ⟩;
    -- By the properties of the geometric series and the positivity of the sums, we can find such constants $c$ and $C$ using the bounds on $u$.
    have h_bounds : ∀ n, ∑ j, (Matrix.vecMul (seq 0) (A ^ n)) j * u j = (∑ i, seq 0 i * u i) * ρ ^ n := by
      intro n
      have h_eigen : (A ^ n).mulVec u = ρ ^ n • u := by
        induction' n with n ih;
        · simp +decide [ Matrix.one_mulVec ];
        · simp +decide [ pow_succ', ← Matrix.mulVec_mulVec, ih, heig, smul_smul ];
          rw [ Matrix.mulVec_smul, heig, smul_smul, mul_comm ];
      convert congr_arg ( fun x => ∑ i, seq 0 i * x i ) h_eigen using 1 <;> simp +decide [ Matrix.mulVec, dotProduct, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
      rw [ Finset.sum_comm ] ; simp +decide [ Matrix.vecMul, dotProduct, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
    have h_bounds : ∀ n, ∑ j, (Matrix.vecMul (seq 0) (A ^ n)) j * u j ≤ umax * ∑ j, (Matrix.vecMul (seq 0) (A ^ n)) j ∧ umin * ∑ j, (Matrix.vecMul (seq 0) (A ^ n)) j ≤ ∑ j, (Matrix.vecMul (seq 0) (A ^ n)) j * u j := by
      intro n
      have h_nonneg : ∀ j, 0 ≤ (Matrix.vecMul (seq 0) (A ^ n)) j := by
        intro j
        have h_nonneg : ∀ i, 0 ≤ (A ^ n) i j := by
          induction' n with n ih generalizing j <;> simp_all +decide [ pow_succ, Matrix.mul_apply ];
          · exact fun i => by rw [ Matrix.one_apply ] ; split_ifs <;> norm_num;
          · exact fun i => Finset.sum_nonneg fun _ _ => mul_nonneg ( ih _ _ ) ( hA _ _ )
        generalize_proofs at *;
        exact Finset.sum_nonneg fun i _ => mul_nonneg ( hseq0 i ) ( h_nonneg i );
      exact ⟨ by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i _ => by nlinarith [ h_nonneg i, humax.2 i ], by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i _ => by nlinarith [ h_nonneg i, humin.2 i ] ⟩;
    use (∑ i, seq 0 i * u i) / umax, (∑ i, seq 0 i * u i) / umin;
    simp_all +decide [ div_mul_eq_mul_div, div_le_iff₀, le_div_iff₀ ];
    exact fun n => ⟨ by linarith [ h_bounds n ], by linarith [ h_bounds n ] ⟩;
  use c, C, hc, hC.1; intro n; convert hC.2 n using 4 ;
  · refine' Nat.recOn n _ _ <;> simp_all +decide [ pow_succ ];
  · refine' Nat.recOn n _ _ <;> simp_all +decide [ pow_succ ]

/-- The forward image of a vertex of `Ξⁿ⁰` at level `n₀+m`, obtained by `m`-fold
application of the skeleton embedding `Sum.inl`. -/
def xiForward (𝓘 : EIGSData K) (n₀ : ℕ) : (m : ℕ) → XiVtx 𝓘 n₀ → XiVtx 𝓘 (n₀+m)
  | 0 => id
  | (m+1) => fun v => Sum.inl (xiForward 𝓘 n₀ m v)

lemma degVec_xiForward_succ (𝓘 : EIGSData K) (n₀ m : ℕ) (v₀ : XiVtx 𝓘 n₀) :
    degVec 𝓘 (n₀+(m+1)) (xiForward 𝓘 n₀ (m+1) v₀)
      = Matrix.vecMul (degVec 𝓘 (n₀+m) (xiForward 𝓘 n₀ m v₀)) (degreeMatrix 𝓘) := by
  exact degVec_inl 𝓘 (n₀+m) (xiForward 𝓘 n₀ m v₀)

/-- **Geometric degree growth (Section 1, now proved).**  Tracking a fixed vertex
`v₀` of `Ξⁿ⁰` forward, its total (out + in) coloured degree grows geometrically
like `ρ(N)ᵐ`, where `ρ(N)` is the Perron eigenvalue of the degree matrix `N`.  The
only input is the Perron–Frobenius positive eigenpair of `N` (cited), supplied as a
hypothesis exactly as in the rest of the project; the two-sided bound is proved. -/
theorem degree_geometric_growth_proved (𝓘 : EIGSData K) [Nonempty (Fin K)]
    (n₀ : ℕ) (v₀ : XiVtx 𝓘 n₀)
    {u : Fin K ⊕ Fin K → ℝ} {ρN : ℝ} (hu : ∀ s, 0 < u s)
    (heig : (degreeMatrix 𝓘).mulVec u = ρN • u) (hρN : 0 < ρN)
    (hpos : 0 < ∑ s, degVec 𝓘 n₀ v₀ s * u s) :
    ∃ c C, 0 < c ∧ 0 < C ∧ ∀ m,
      c * ρN ^ m ≤ ∑ s, degVec 𝓘 (n₀+m) (xiForward 𝓘 n₀ m v₀) s
        ∧ ∑ s, degVec 𝓘 (n₀+m) (xiForward 𝓘 n₀ m v₀) s ≤ C * ρN ^ m := by
  have hne : Nonempty (Fin K ⊕ Fin K) := ⟨Sum.inl (Classical.arbitrary _)⟩
  refine vecMul_recursion_geometric_general (ι := Fin K ⊕ Fin K)
    (A := degreeMatrix 𝓘) (seq := fun m => degVec 𝓘 (n₀+m) (xiForward 𝓘 n₀ m v₀))
    (u := u) (ρ := ρN) (degreeMatrix_nonneg 𝓘) hu ?_ ?_ ?_ heig hρN
  · intro s; cases s <;> exact Nat.cast_nonneg _
  · simpa using hpos
  · intro m; exact degVec_xiForward_succ 𝓘 n₀ m v₀

end EIGS