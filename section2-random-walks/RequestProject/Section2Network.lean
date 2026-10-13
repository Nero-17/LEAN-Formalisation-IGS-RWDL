import RequestProject.Section2

/-!
# Grounding the abstract Thomson framework in finite electrical networks

This file connects the abstract `EIGS.ThomsonData` / `EIGS.RenormMap` framework of
`Section2.lean` to *genuine* finite electrical networks and unit flows, following
Definition 2.1 of arXiv:2603.13798.

For a finite directed multigraph with `K`-coloured edges and two terminals `a, b`,
Thomson's principle expresses the effective resistance at the resistance vector `x`
as the infimum, over all **unit flows** `θ` from `a` to `b`, of the energy

  `ℰ(θ) = ∑_{e} x_{𝒞(e)} · θ(e)²`.

Grouping the edges by colour, `ℰ(θ) = ∑_{j} (∑_{e : 𝒞(e)=j} θ(e)²) · x_j`, which is
exactly a linear functional of `x` with nonnegative coefficients
`w θ j = ∑_{e : 𝒞(e)=j} θ(e)²`.  This realises the abstract `ThomsonData`, so the
structural properties of Lemma 2.3 proved abstractly in `Section2.lean` apply
verbatim to the genuine effective resistance defined here.
-/

namespace EIGS

open scoped BigOperators

/-- A finite `K`-coloured directed (multi)graph: an electrical network.  Each edge
`e` has a tail, a head, and a colour `𝒞(e) ∈ Fin K`; assigning resistance `x j` to
every `j`-coloured edge turns it into an electrical network. -/
structure Network (K : ℕ) where
  /-- vertices -/
  V : Type
  /-- (oriented) edges -/
  E : Type
  /-- finitely many vertices -/
  fintypeV : Fintype V
  /-- decidable equality of vertices (for divergence indicator) -/
  decEqV : DecidableEq V
  /-- finitely many edges -/
  fintypeE : Fintype E
  /-- tail (source) of an edge -/
  tail : E → V
  /-- head (target) of an edge -/
  head : E → V
  /-- colour of an edge -/
  color : E → Fin K

attribute [instance] Network.fintypeV Network.decEqV Network.fintypeE

namespace Network

variable {K : ℕ} (N : Network K)

/-- Net flow out of vertex `u` under the (real) edge-current `θ`: outgoing minus
incoming. -/
def div (θ : N.E → ℝ) (u : N.V) : ℝ :=
  (∑ e, if N.tail e = u then θ e else 0) - (∑ e, if N.head e = u then θ e else 0)

/-- `θ` is a **unit flow** from `a` to `b`: it has divergence `+1` at the source
`a`, `-1` at the sink `b`, and `0` elsewhere (Kirchhoff's node law with a unit of
current injected at `a` and extracted at `b`). -/
def IsUnitFlow (a b : N.V) (θ : N.E → ℝ) : Prop :=
  ∀ u, N.div θ u = (if u = a then 1 else if u = b then -1 else 0)

/-- The type of unit flows from `a` to `b`. -/
def Flow (a b : N.V) : Type := {θ : N.E → ℝ // N.IsUnitFlow a b θ}

/-- Coefficient of colour `j` in the flow energy: the sum of squared currents over
the `j`-coloured edges. -/
def colorWeight (a b : N.V) (θ : N.Flow a b) (j : Fin K) : ℝ :=
  ∑ e, if N.color e = j then (θ.1 e) ^ 2 else 0

lemma colorWeight_nonneg (a b : N.V) (θ : N.Flow a b) (j : Fin K) :
    0 ≤ N.colorWeight a b θ j := by
  refine Finset.sum_nonneg ?_
  intro e _
  by_cases h : N.color e = j <;> simp [h, sq_nonneg]

/-- The abstract Thomson data attached to a connected two-terminal network: the
unit flows index a family of linear energy functionals with nonnegative
coefficients. -/
noncomputable def toThomsonData (a b : N.V) (hconn : Nonempty (N.Flow a b)) :
    ThomsonData K where
  F := N.Flow a b
  nonempty := hconn
  w := N.colorWeight a b
  w_nonneg := fun θ j => N.colorWeight_nonneg a b θ j

/-- The Dirichlet/flow energy of a current `θ` at resistance vector `x`:
`∑_e x_{𝒞(e)} θ(e)²`. -/
def energyNetwork (θ : N.E → ℝ) (x : Fin K → ℝ) : ℝ :=
  ∑ e, x (N.color e) * (θ e) ^ 2

/-
**Thomson's principle (representation).** The flow energy equals the abstract
linear functional `∑_j w_j x_j` obtained by grouping edges by colour.
-/
lemma energyNetwork_eq_energy (a b : N.V) (hconn : Nonempty (N.Flow a b))
    (θ : N.Flow a b) (x : Fin K → ℝ) :
    N.energyNetwork θ.1 x = (N.toThomsonData a b hconn).energy θ x := by
  unfold EIGS.Network.energyNetwork EIGS.ThomsonData.energy;
  unfold EIGS.Network.toThomsonData;
  simp +decide only [mul_comm, colorWeight, Finset.mul_sum _ _ _];
  rw [ Finset.sum_comm ] ; simp +decide [ mul_comm ]

/-- The **effective resistance** of the two-terminal network `(a, b)` at resistance
vector `x`, defined via Thomson's principle as the abstract Thomson functional. -/
noncomputable def effRes (a b : N.V) (hconn : Nonempty (N.Flow a b))
    (x : Fin K → ℝ) : ℝ :=
  (N.toThomsonData a b hconn).eval x

/-
`effRes` is the infimum of the genuine flow energies over all unit flows —
Thomson's principle in its usual form.
-/
lemma effRes_eq_iInf (a b : N.V) (hconn : Nonempty (N.Flow a b)) (x : Fin K → ℝ) :
    N.effRes a b hconn x = ⨅ θ : N.Flow a b, N.energyNetwork θ.1 x := by
  convert iInf_congr _;
  exact fun θ => Eq.symm ( N.energyNetwork_eq_energy a b hconn θ x )

/-! ### Lemma 2.3 for the genuine effective resistance

All structural properties follow from the abstract development in `Section2.lean`
because `effRes` is by definition the abstract Thomson functional. -/

lemma effRes_nonneg (a b : N.V) (hconn : Nonempty (N.Flow a b))
    {x : Fin K → ℝ} (hx : 0 ≤ x) : 0 ≤ N.effRes a b hconn x :=
  ThomsonData.eval_nonneg _ hx

/-- Monotonicity (Lemma 2.3 (1)). -/
lemma effRes_mono (a b : N.V) (hconn : Nonempty (N.Flow a b))
    {x y : Fin K → ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    N.effRes a b hconn x ≤ N.effRes a b hconn y :=
  ThomsonData.eval_mono _ hx hxy

/-- Homogeneity (Lemma 2.3 (2)). -/
lemma effRes_smul (a b : N.V) (hconn : Nonempty (N.Flow a b))
    (x : Fin K → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    N.effRes a b hconn (t • x) = t * N.effRes a b hconn x :=
  ThomsonData.eval_smul _ x ht

/-- Concavity (Lemma 2.3 (4)). -/
lemma effRes_concave (a b : N.V) (hconn : Nonempty (N.Flow a b))
    {x y : Fin K → ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    l * N.effRes a b hconn x + (1 - l) * N.effRes a b hconn y
      ≤ N.effRes a b hconn (l • x + (1 - l) • y) :=
  ThomsonData.eval_concave _ hx hy hl0 hl1

/-- Superadditivity (Lemma 2.3 (5)). -/
lemma effRes_superadditive (a b : N.V) (hconn : Nonempty (N.Flow a b))
    {x y : Fin K → ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    N.effRes a b hconn x + N.effRes a b hconn y ≤ N.effRes a b hconn (x + y) :=
  ThomsonData.eval_superadditive _ hx hy

end Network

/-- A `K`-colour EIGS rule system, abstractly: for each colour `i` a rule network
`R i` with two terminals `β⁺ i, β⁻ i`, connected (so a unit flow exists).  This
assembles the resistance renormalisation map `Ψ` of Definition 2.1 from genuine
networks. -/
structure RuleSystem (K : ℕ) where
  /-- rule network for colour `i` -/
  R : Fin K → Network K
  /-- positive terminal of rule `i` -/
  βplus : ∀ i, (R i).V
  /-- negative terminal of rule `i` -/
  βminus : ∀ i, (R i).V
  /-- each rule is connected between its terminals -/
  connected : ∀ i, Nonempty ((R i).Flow (βplus i) (βminus i))

namespace RuleSystem

variable {K : ℕ} (S : RuleSystem K)

/-- The resistance renormalisation map `Ψ` (Definition 2.1) assembled from the
genuine rule networks via Thomson's principle. -/
noncomputable def toRenormMap : RenormMap K where
  coord := fun i => (S.R i).toThomsonData (S.βplus i) (S.βminus i) (S.connected i)

/-- Coordinate `i` of `Ψ(x)` is the effective resistance of rule `i`. -/
lemma toRenormMap_apply (x : Fin K → ℝ) (i : Fin K) :
    S.toRenormMap.apply x i =
      (S.R i).effRes (S.βplus i) (S.βminus i) (S.connected i) x := rfl

end RuleSystem

end EIGS
