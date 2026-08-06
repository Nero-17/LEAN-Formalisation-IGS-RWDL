import Mathlib
import RequestProject.Section1Vertices

/-!
# Connectivity of the substitution networks `Ξⁿ` (Section 1)

`Section1Vertices.lean` builds the vertex-identification quotient of an EIGS and the
underlying simple graph `XiSimpleGraph 𝓘 n` of `Ξⁿ`, but everywhere downstream the
**connectivity** `(XiSimpleGraph 𝓘 n).Connected` was taken as a hypothesis.  Since
the construction of `Ξⁿ` is explicit, connectivity is a self-contained combinatorial
fact, proved here by induction on the substitution level `n`.

The only genuine input is that each **rule graph** is connected (this is the
standing EIGS assumption that every rule connects its planting vertices through its
interior).  We phrase it as `(ruleSG 𝓘 i).Connected`, where `ruleSG 𝓘 i` is the
underlying simple graph of the rule `R_i`.

## Proof outline

* `ruleSG` — the underlying simple graph of a rule `R_i`.
* `cmap` — the map embedding a rule vertex `w` (on skeleton edge `e`) into
  `V(Ξⁿ⁺¹)` via the vertex-identification quotient `embedRuleVtx`.
* `reachable_map` — reachability transports along a map that sends adjacency to
  reachability.
* `cmap_adj_reachable` / `cmap_reachable` — a rule copy is connected inside `Ξⁿ⁺¹`
  (so all its embedded vertices are reachable from each other).
* `inl_reachable` — old (skeleton) vertices keep their reachability one level up
  (two skeleton endpoints of an edge are joined through the rule copy attached to
  that edge).
* `xiSimpleGraph_connected` — the main theorem: `Ξⁿ` is connected for every `n`.
-/

namespace EIGS

open scoped BigOperators
open SimpleGraph

variable {K : ℕ}

/-- The underlying simple graph of a rule graph `R_i`: two distinct vertices are
adjacent iff some rule edge joins them (in either orientation). -/
def ruleSG (𝓘 : EIGSData K) (i : Fin K) : SimpleGraph ((𝓘.rule i).V) :=
  SimpleGraph.fromRel (fun u v =>
    ∃ e' : (𝓘.rule i).E, (𝓘.rule i).tail e' = u ∧ (𝓘.rule i).head e' = v)

/-- The embedding of a rule vertex `w` on the skeleton edge `e` into `V(Ξⁿ⁺¹)`, via
the vertex-identification quotient. -/
def cmap (𝓘 : EIGSData K) (n : ℕ) (e : XiEdge 𝓘.toRuleData n)
    (w : (𝓘.rule (XiCol 𝓘.toRuleData n e)).V) : XiVtx 𝓘 (n+1) :=
  embedRuleVtx 𝓘 n e (XiTail 𝓘 n e) (XiHead 𝓘 n e) w

/-- Reachability transports along a map that sends adjacency to reachability. -/
lemma reachable_map {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W)
    (hf : ∀ a b, G.Adj a b → H.Reachable (f a) (f b)) {u v : V}
    (h : G.Reachable u v) : H.Reachable (f u) (f v) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact Reachable.refl _
  | cons hadj p ih => exact (hf _ _ hadj).trans ih

/-- `cmap e (β⁺)` is the skeleton tail `Sum.inl (XiTail n e)`. -/
@[simp] lemma cmap_plantPlus (𝓘 : EIGSData K) (n : ℕ) (e : XiEdge 𝓘.toRuleData n) :
    cmap 𝓘 n e (𝓘.plantPlus (XiCol 𝓘.toRuleData n e)) = Sum.inl (XiTail 𝓘 n e) := by
  simp [cmap]

/-- `cmap e (β⁻)` is the skeleton head `Sum.inl (XiHead n e)`. -/
@[simp] lemma cmap_plantMinus (𝓘 : EIGSData K) (n : ℕ) (e : XiEdge 𝓘.toRuleData n) :
    cmap 𝓘 n e (𝓘.plantMinus (XiCol 𝓘.toRuleData n e)) = Sum.inl (XiHead 𝓘 n e) := by
  simp [cmap]

/-
Adjacent rule vertices become reachable inside `Ξⁿ⁺¹` after embedding via `cmap`
(each rule edge `e'` gives a genuine edge `(e, e')` of `Ξⁿ⁺¹`).
-/
lemma cmap_adj_reachable (𝓘 : EIGSData K) (n : ℕ) (e : XiEdge 𝓘.toRuleData n)
    {w w' : (𝓘.rule (XiCol 𝓘.toRuleData n e)).V}
    (h : (ruleSG 𝓘 (XiCol 𝓘.toRuleData n e)).Adj w w') :
    (XiSimpleGraph 𝓘 (n+1)).Reachable (cmap 𝓘 n e w) (cmap 𝓘 n e w') := by
  cases h.2;
  · obtain ⟨ e', he', he'' ⟩ := ‹_›;
    by_cases heq : cmap 𝓘 n e w = cmap 𝓘 n e w';
    · exact heq.symm ▸ SimpleGraph.Reachable.refl _;
    · refine' SimpleGraph.Adj.reachable _;
      exact ⟨ heq, Or.inl ⟨ ⟨ e, e' ⟩, by aesop ⟩ ⟩;
  · obtain ⟨ e', he' ⟩ := ‹∃ e', _›;
    -- Consider the level-`n+1` edge `p := (⟨e, e'⟩ : XiEdge 𝓘.toRuleData (n+1))`.
    set p : XiEdge 𝓘.toRuleData (n + 1) := ⟨e, e'⟩;
    -- By definition of `cmap`, we have `XiTail 𝓘 (n+1) p = cmap 𝓘 n e w'` and `XiHead 𝓘 (n+1) p = cmap 𝓘 n e w`.
    have h_tail : XiTail 𝓘 (n + 1) p = cmap 𝓘 n e w' := by
      exact he'.1 ▸ rfl
    have h_head : XiHead 𝓘 (n + 1) p = cmap 𝓘 n e w := by
      unfold XiHead; aesop;
    by_cases heq : cmap 𝓘 n e w = cmap 𝓘 n e w';
    · exact heq.symm ▸ SimpleGraph.Reachable.refl _;
    · exact SimpleGraph.Adj.reachable ( by unfold XiSimpleGraph; aesop )

/-
A whole rule copy is connected inside `Ξⁿ⁺¹`: any two embedded vertices of the
copy on `e` are reachable from each other.
-/
lemma cmap_reachable (𝓘 : EIGSData K) (hrule : ∀ i, (ruleSG 𝓘 i).Connected)
    (n : ℕ) (e : XiEdge 𝓘.toRuleData n)
    (w w' : (𝓘.rule (XiCol 𝓘.toRuleData n e)).V) :
    (XiSimpleGraph 𝓘 (n+1)).Reachable (cmap 𝓘 n e w) (cmap 𝓘 n e w') := by
  exact reachable_map (ruleSG 𝓘 (XiCol 𝓘.toRuleData n e)) (XiSimpleGraph 𝓘 (n + 1))
    (cmap 𝓘 n e) (fun _ _ => cmap_adj_reachable 𝓘 n e)
    ((hrule (XiCol 𝓘.toRuleData n e)).preconnected w w')

/-- The two skeleton endpoints of a level-`n` edge `e` are reachable in `Ξⁿ⁺¹`,
through the rule copy attached to `e`. -/
lemma inl_ends_reachable (𝓘 : EIGSData K) (hrule : ∀ i, (ruleSG 𝓘 i).Connected)
    (n : ℕ) (e : XiEdge 𝓘.toRuleData n) :
    (XiSimpleGraph 𝓘 (n+1)).Reachable (Sum.inl (XiTail 𝓘 n e)) (Sum.inl (XiHead 𝓘 n e)) := by
  have := cmap_reachable 𝓘 hrule n e
    (𝓘.plantPlus (XiCol 𝓘.toRuleData n e)) (𝓘.plantMinus (XiCol 𝓘.toRuleData n e))
  simpa using this

/-
Old (skeleton) vertices keep their reachability one level up.
-/
lemma inl_reachable (𝓘 : EIGSData K) (hrule : ∀ i, (ruleSG 𝓘 i).Connected)
    (n : ℕ) {u v : XiVtx 𝓘 n} (h : (XiSimpleGraph 𝓘 n).Reachable u v) :
    (XiSimpleGraph 𝓘 (n+1)).Reachable (Sum.inl u) (Sum.inl v) := by
  refine' reachable_map _ _ _ _ h;
  simp [XiSimpleGraph];
  rintro a b hab ( ⟨ e, rfl, rfl ⟩ | ⟨ e, rfl, rfl ⟩ );
  · convert inl_ends_reachable 𝓘 hrule n e using 1;
  · exact inl_ends_reachable 𝓘 hrule n e |> fun h => h.symm

/-
Every vertex of `Ξⁿ⁺¹` is reachable from a skeleton (old) vertex.
-/
lemma reachable_some_inl (𝓘 : EIGSData K) (hrule : ∀ i, (ruleSG 𝓘 i).Connected)
    (n : ℕ) (x : XiVtx 𝓘 (n+1)) :
    ∃ u : XiVtx 𝓘 n, (XiSimpleGraph 𝓘 (n+1)).Reachable x (Sum.inl u) := by
  cases' x with x x;
  · exact ⟨ x, SimpleGraph.Reachable.refl _ ⟩;
  · use XiTail 𝓘 n x.1;
    convert cmap_reachable 𝓘 hrule n x.1 x.2.1 ( 𝓘.plantPlus ( XiCol 𝓘.toRuleData n x.1 ) ) using 1;
    · exact Eq.symm ( embedRuleVtx_interior _ _ _ _ _ x.2.2.1 x.2.2.2 );
    · grind +suggestions

/-
**Connectivity of `Ξⁿ` (Section 1).**  If every rule graph is connected, then the
substitution network `Ξⁿ` is connected for every level `n`.
-/
theorem xiSimpleGraph_connected (𝓘 : EIGSData K)
    (hrule : ∀ i, (ruleSG 𝓘 i).Connected) :
    ∀ n, (XiSimpleGraph 𝓘 n).Connected := by
  intro n; induction' n with n ih; exact (by
  unfold XiSimpleGraph; simp +decide [ SimpleGraph.connected_iff_exists_forall_reachable ] ;
  use Bool.true; intro w; rcases w with ( _ | _ ) <;> simp +decide [ SimpleGraph.Reachable ] ;
  · refine' ⟨ SimpleGraph.Walk.cons _ _ ⟩;
    exact Bool.false;
    · simp +decide [ XiTail, XiHead, XiEnds ];
      exact ⟨ ⟨ ⟩ ⟩;
    · exact SimpleGraph.Walk.nil;
  · exact ⟨ SimpleGraph.Walk.nil ⟩); exact (by
  have h_connected : ∀ x y : XiVtx 𝓘 (n + 1), (XiSimpleGraph 𝓘 (n + 1)).Reachable x y := by
    intros x y; obtain ⟨ ux, hx ⟩ := reachable_some_inl 𝓘 hrule n x; obtain ⟨ uy, hy ⟩ := reachable_some_inl 𝓘 hrule n y; exact hx.trans ( ( inl_reachable 𝓘 hrule n ( ih.preconnected ux uy ) ) |> fun h => h.trans hy.symm ) ;
  convert h_connected using 1;
  constructor <;> intro h <;> simp_all +decide [ SimpleGraph.connected_iff_exists_forall_reachable ];
  exact ⟨ Sum.inl ( ih.choose ) ⟩);

end EIGS