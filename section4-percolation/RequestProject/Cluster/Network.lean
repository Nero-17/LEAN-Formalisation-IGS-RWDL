import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic

/-!
# Finite two-terminal unit-resistance networks

This file develops, from scratch, the small amount of electrical-network theory needed for
Proposition 4.2 of *Iterated Graph Systems (I): random walks and diffusion limits*
(arXiv:2603.13798): finite two-terminal networks in which every edge has resistance `1`, their
**effective resistance** defined by Thomson's principle (an infimum of the flow energy over unit
flows), and the **series** and **parallel** composition laws.

The effective resistance takes values in `ℝ≥0∞`; the value `⊤` occurs exactly when the two
terminals are not joined by any unit flow, i.e. when they lie in different components.  With this
convention the parallel law

  `effRes (par N M)⁻¹ = (effRes N)⁻¹ + (effRes M)⁻¹`

also encodes the *deletion of dangling pieces*: if `M` is disconnected (`effRes M = ⊤`), then
`effRes (par N M) = effRes N`.
-/

namespace Cluster

open scoped BigOperators ENNReal
open Finset

/-- A finite two-terminal electrical network, all of whose edges have unit resistance:
a finite (multi)graph with an oriented edge set and two distinct marked terminals `a ≠ b`. -/
structure TTN where
  /-- vertices -/
  V : Type
  /-- oriented edges -/
  E : Type
  /-- finitely many vertices -/
  fintypeV : Fintype V
  /-- decidable equality of vertices -/
  decEqV : DecidableEq V
  /-- finitely many edges -/
  fintypeE : Fintype E
  /-- tail of an edge -/
  tail : E → V
  /-- head of an edge -/
  head : E → V
  /-- first terminal -/
  a : V
  /-- second terminal -/
  b : V
  /-- the terminals are distinct -/
  hab : a ≠ b

attribute [instance] TTN.fintypeV TTN.decEqV TTN.fintypeE

namespace TTN

variable (N : TTN)

/-- Net flow out of the vertex `u` under the edge current `θ`. -/
def div (θ : N.E → ℝ) (u : N.V) : ℝ :=
  (∑ e, if N.tail e = u then θ e else 0) - (∑ e, if N.head e = u then θ e else 0)

/-- `θ` is a flow of strength `t` from `a` to `b`. -/
def IsFlow (t : ℝ) (θ : N.E → ℝ) : Prop :=
  ∀ u, N.div θ u = (if u = N.a then t else if u = N.b then -t else 0)

/-- The type of flows of strength `t` from `a` to `b`. -/
def Flow (t : ℝ) : Type := {θ : N.E → ℝ // N.IsFlow t θ}

/-- The energy `∑_e θ(e)²` of a current (all edges have unit resistance). -/
def energy (θ : N.E → ℝ) : ℝ := ∑ e, (θ e) ^ 2

/-- The infimum of the energy over flows of strength `t`; `⊤` if there is no such flow. -/
noncomputable def flowRes (t : ℝ) : ℝ≥0∞ := ⨅ θ : N.Flow t, ENNReal.ofReal (N.energy θ.1)

/-- The **effective resistance** between the two terminals (Thomson's principle). -/
noncomputable def effRes : ℝ≥0∞ := N.flowRes 1

lemma energy_nonneg (θ : N.E → ℝ) : 0 ≤ N.energy θ := by
  unfold energy; positivity

/-! ### Basic identities -/

/-- The total divergence of any current vanishes. -/
lemma sum_div (θ : N.E → ℝ) : ∑ u, N.div θ u = 0 := by
  classical
  unfold div
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ u, ∑ e, (if N.tail e = u then θ e else 0) = ∑ e, θ e := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun e _ => by simp)
  have h2 : ∑ u, ∑ e, (if N.head e = u then θ e else 0) = ∑ e, θ e := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun e _ => by simp)
  rw [h1, h2, sub_self]

/-- Scaling a current scales the divergence. -/
lemma div_smul (θ : N.E → ℝ) (c : ℝ) (u : N.V) :
    N.div (fun e => c * θ e) u = c * N.div θ u := by
  unfold div
  rw [mul_sub]
  congr 1 <;> rw [Finset.mul_sum] <;> exact Finset.sum_congr rfl (by intro e _; split <;> simp)

lemma energy_smul (θ : N.E → ℝ) (c : ℝ) :
    N.energy (fun e => c * θ e) = c ^ 2 * N.energy θ := by
  unfold energy
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (by intro e _; ring)

/-- Rescaling turns a flow of strength `1` into a flow of strength `t`. -/
noncomputable def flowScale {t : ℝ} (ht : t ≠ 0) : N.Flow 1 ≃ N.Flow t where
  toFun φ := ⟨fun e => t * φ.1 e, by
    intro u
    rw [N.div_smul, φ.2 u]
    split_ifs <;> ring⟩
  invFun θ := ⟨fun e => t⁻¹ * θ.1 e, by
    intro u
    rw [N.div_smul, θ.2 u]
    split_ifs <;> simp [inv_mul_cancel₀ ht]⟩
  left_inv φ := by
    refine Subtype.ext (funext fun e => ?_)
    field_simp
  right_inv θ := by
    refine Subtype.ext (funext fun e => ?_)
    field_simp

/-- The infimum over flows of strength `t` is `t²` times the effective resistance. -/
theorem flowRes_eq (t : ℝ) : N.flowRes t = ENNReal.ofReal (t ^ 2) * N.effRes := by
  rcases eq_or_ne t 0 with rfl | ht
  · have h0 : N.IsFlow 0 (fun _ => 0) := by
      intro u
      simp [div]
    have : N.flowRes 0 = 0 := by
      refine le_antisymm ?_ (zero_le _)
      refine le_of_le_of_eq (iInf_le _ (⟨fun _ => 0, h0⟩ : N.Flow 0)) ?_
      simp [energy]
    simp [this]
  · have hne : ENNReal.ofReal (t ^ 2) ≠ 0 := by
      simp [ENNReal.ofReal_eq_zero]
      positivity
    have hne' : ENNReal.ofReal (t ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [flowRes, ← (N.flowScale ht).iInf_comp, effRes, flowRes,
      ENNReal.mul_iInf_of_ne hne hne']
    refine iInf_congr (fun φ => ?_)
    have : N.energy ((N.flowScale ht) φ).1 = t ^ 2 * N.energy φ.1 := N.energy_smul _ _
    rw [this, ENNReal.ofReal_mul (by positivity)]

/-- If the divergence vanishes off the terminals and equals `t` at `a`, it equals `-t` at `b`. -/
lemma div_at_b (X : TTN) (θ : X.E → ℝ) (t : ℝ)
    (h : ∀ u, u ≠ X.a → u ≠ X.b → X.div θ u = 0) (ha : X.div θ X.a = t) :
    X.div θ X.b = -t := by
  classical
  have hsum : ∑ u, X.div θ u = 0 := X.sum_div θ
  have h2 : ∑ u ∈ ({X.a, X.b} : Finset X.V), X.div θ u = ∑ u, X.div θ u := by
    refine Finset.sum_subset (f := X.div θ) (Finset.subset_univ _) ?_
    intro u _ hu
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu
    exact h u hu.1 hu.2
  rw [Finset.sum_pair X.hab, hsum, ha] at h2
  linarith

/-- A convenient characterisation of flows: it suffices to know the divergence at `a` and that it
vanishes away from the terminals. -/
lemma isFlow_iff (X : TTN) (θ : X.E → ℝ) (t : ℝ) :
    X.IsFlow t θ ↔ (X.div θ X.a = t ∧ ∀ u, u ≠ X.a → u ≠ X.b → X.div θ u = 0) := by
  constructor
  · intro h
    exact ⟨by simpa using h X.a, fun u hu hu' => by simpa [hu, hu'] using h u⟩
  · rintro ⟨ha, h0⟩ u
    by_cases hu : u = X.a
    · subst hu; simpa using ha
    · by_cases hu' : u = X.b
      · subst hu'
        simp only [if_neg hu]
        exact div_at_b X θ t h0 ha
      · simp only [if_neg hu, if_neg hu']
        exact h0 u hu hu'

/-- Infimum of a sum of two independent quantities over a product. -/
lemma iInf_add_iInf_prod {ι κ : Type*} (f : ι → ℝ≥0∞) (g : κ → ℝ≥0∞) :
    ⨅ p : ι × κ, (f p.1 + g p.2) = (⨅ i, f i) + (⨅ j, g j) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [iInf_of_isEmpty]
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simp [iInf_of_isEmpty]
  · have h1 : (⨅ p : ι × κ, f p.1) = ⨅ i, f i := by
      rw [iInf_prod]; simp
    have h2 : (⨅ p : ι × κ, g p.2) = ⨅ j, g j := by
      rw [iInf_prod]; simp
    rw [← h1, ← h2]
    exact (ENNReal.iInf_add_iInf (fun i j => ⟨(i.1, j.2), le_of_eq (by simp)⟩)).symm

/-! ### The elementary networks -/

/-- A single unit edge between the two terminals. -/
def edgeTTN : TTN where
  V := Bool
  E := Unit
  fintypeV := inferInstance
  decEqV := inferInstance
  fintypeE := inferInstance
  tail := fun _ => false
  head := fun _ => true
  a := false
  b := true
  hab := by decide

/-- Two isolated terminals: the network obtained from a closed (absent) edge. -/
def gapTTN : TTN where
  V := Bool
  E := Empty
  fintypeV := inferInstance
  decEqV := inferInstance
  fintypeE := inferInstance
  tail := fun e => e.elim
  head := fun e => e.elim
  a := false
  b := true
  hab := by decide

theorem effRes_edge : edgeTTN.effRes = 1 := by
  have hflow : edgeTTN.IsFlow 1 (fun _ => 1) := by
    intro u
    cases u <;> simp [div, edgeTTN]
  refine le_antisymm ?_ ?_
  · refine le_of_le_of_eq (iInf_le _ (⟨fun _ => 1, hflow⟩ : edgeTTN.Flow 1)) ?_
    simp [energy, edgeTTN]
  · refine le_iInf (fun θ => ?_)
    have h := θ.2 false
    simp [div, edgeTTN] at h
    have : edgeTTN.energy θ.1 = 1 := by
      simp [energy, edgeTTN, h]
    rw [this]
    simp

theorem effRes_gap : gapTTN.effRes = ⊤ := by
  have : IsEmpty (gapTTN.Flow 1) := by
    constructor
    rintro ⟨θ, hθ⟩
    have h := hθ false
    simp [div, gapTTN] at h
  simp [effRes, flowRes, iInf_of_isEmpty]

/-! ### Series composition -/

/-- Vertices of the series composition: the terminal `a` of `M` is glued to the terminal `b`
of `N`. -/
abbrev seriesV (N M : TTN) : Type := N.V ⊕ {v : M.V // v ≠ M.a}

instance (N M : TTN) : Fintype (seriesV N M) := by unfold seriesV; infer_instance
instance (N M : TTN) : DecidableEq (seriesV N M) := by unfold seriesV; infer_instance

/-- The embedding of the vertices of `M` into the series composition. -/
def seriesEmb (N M : TTN) (v : M.V) : seriesV N M :=
  if h : v = M.a then Sum.inl N.b else Sum.inr ⟨v, h⟩

/-- The **series composition** of `N` and `M`: the terminal `b` of `N` is identified with the
terminal `a` of `M`. -/
def seriesTTN (N M : TTN) : TTN where
  V := seriesV N M
  E := N.E ⊕ M.E
  fintypeV := inferInstance
  decEqV := inferInstance
  fintypeE := inferInstance
  tail := Sum.elim (fun e => Sum.inl (N.tail e)) (fun e => seriesEmb N M (M.tail e))
  head := Sum.elim (fun e => Sum.inl (N.head e)) (fun e => seriesEmb N M (M.head e))
  a := Sum.inl N.a
  b := seriesEmb N M M.b
  hab := by
    simp only [seriesEmb, dif_neg (Ne.symm M.hab)]
    exact fun h => by cases h

@[simp] lemma seriesEmb_eq_inl (N M : TTN) (v : M.V) (u : N.V) :
    seriesEmb N M v = Sum.inl u ↔ (v = M.a ∧ N.b = u) := by
  unfold seriesEmb
  split <;> simp_all

@[simp] lemma seriesEmb_eq_inr (N M : TTN) (v : M.V) (w : {x : M.V // x ≠ M.a}) :
    seriesEmb N M v = Sum.inr w ↔ v = w.1 := by
  unfold seriesEmb
  split
  · next h => simp [h, Ne.symm w.2]
  · next h => simp [Subtype.ext_iff]

lemma seriesTTN_b (N M : TTN) :
    (seriesTTN N M).b = Sum.inr ⟨M.b, Ne.symm M.hab⟩ := by
  show seriesEmb N M M.b = _
  simp [seriesEmb, Ne.symm M.hab]

lemma series_div_inl (N M : TTN) (θ : (seriesTTN N M).E → ℝ) (u : N.V) :
    (seriesTTN N M).div θ (Sum.inl u)
      = N.div (fun e => θ (Sum.inl e)) u
        + (if u = N.b then M.div (fun e => θ (Sum.inr e)) M.a else 0) := by
  classical
  simp only [TTN.div, seriesTTN, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Sum.inl.injEq, seriesEmb_eq_inl]
  by_cases hu : u = N.b
  · subst hu
    simp only [and_true]
    split_ifs <;> ring
  · simp only [if_neg hu]
    simp only [Ne.symm hu, and_false, if_false, Finset.sum_const_zero]
    ring

lemma series_div_inr (N M : TTN) (θ : (seriesTTN N M).E → ℝ) (w : {x : M.V // x ≠ M.a}) :
    (seriesTTN N M).div θ (Sum.inr w) = M.div (fun e => θ (Sum.inr e)) w.1 := by
  classical
  simp only [TTN.div, seriesTTN, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    seriesEmb_eq_inr, reduceCtorEq, if_false, Finset.sum_const_zero, zero_add]

lemma series_energy (N M : TTN) (θ : (seriesTTN N M).E → ℝ) :
    (seriesTTN N M).energy θ
      = N.energy (fun e => θ (Sum.inl e)) + M.energy (fun e => θ (Sum.inr e)) := by
  simp only [TTN.energy, seriesTTN, Fintype.sum_sum_type]

lemma series_isFlow_iff (N M : TTN) (t : ℝ) (θ : (seriesTTN N M).E → ℝ) :
    (seriesTTN N M).IsFlow t θ ↔
      (N.IsFlow t (fun e => θ (Sum.inl e)) ∧ M.IsFlow t (fun e => θ (Sum.inr e))) := by
  classical
  have hSa : (seriesTTN N M).a = (Sum.inl N.a : seriesV N M) := rfl
  have hSb := seriesTTN_b N M
  constructor
  · intro h
    have hN : N.IsFlow t (fun e => θ (Sum.inl e)) := by
      rw [isFlow_iff]
      constructor
      · have h1 := h (Sum.inl N.a)
        rw [series_div_inl, if_neg N.hab, add_zero] at h1
        rw [h1, ← hSa]
        simp
      · intro u hu hu'
        have h1 := h (Sum.inl u)
        rw [series_div_inl, if_neg hu', add_zero] at h1
        have hne : (Sum.inl u : seriesV N M) ≠ (seriesTTN N M).a := by
          rw [hSa]; exact fun hc => hu (Sum.inl.inj hc)
        have hne2 : (Sum.inl u : seriesV N M) ≠ (seriesTTN N M).b := by
          rw [hSb]; exact fun hc => by cases hc
        rw [h1, if_neg hne, if_neg hne2]
    refine ⟨hN, ?_⟩
    have hNb : N.div (fun e => θ (Sum.inl e)) N.b = -t := by
      have h2 := (isFlow_iff N (fun e => θ (Sum.inl e)) t).1 hN
      exact div_at_b N _ t h2.2 h2.1
    rw [isFlow_iff]
    constructor
    · have h1 := h (Sum.inl N.b)
      rw [series_div_inl, if_pos rfl, hNb] at h1
      have hne : (Sum.inl N.b : seriesV N M) ≠ (seriesTTN N M).a := by
        rw [hSa]; exact fun hc => N.hab (Sum.inl.inj hc).symm
      have hne2 : (Sum.inl N.b : seriesV N M) ≠ (seriesTTN N M).b := by
        rw [hSb]; exact fun hc => by cases hc
      rw [if_neg hne, if_neg hne2] at h1
      linarith
    · intro w hw hw'
      have h1 := h (Sum.inr ⟨w, hw⟩)
      rw [series_div_inr] at h1
      have hne : (Sum.inr ⟨w, hw⟩ : seriesV N M) ≠ (seriesTTN N M).a := by
        rw [hSa]; exact fun hc => by cases hc
      have hne2 : (Sum.inr ⟨w, hw⟩ : seriesV N M) ≠ (seriesTTN N M).b := by
        rw [hSb]
        simp only [ne_eq, Sum.inr.injEq, Subtype.mk.injEq]
        exact hw'
      rw [h1, if_neg hne, if_neg hne2]
  · rintro ⟨hN, hM⟩
    have hNa := ((isFlow_iff N (fun e => θ (Sum.inl e)) t).1 hN).1
    have hN0 := ((isFlow_iff N (fun e => θ (Sum.inl e)) t).1 hN).2
    have hMa := ((isFlow_iff M (fun e => θ (Sum.inr e)) t).1 hM).1
    have hM0 := ((isFlow_iff M (fun e => θ (Sum.inr e)) t).1 hM).2
    have hNb : N.div (fun e => θ (Sum.inl e)) N.b = -t := div_at_b N _ t hN0 hNa
    rw [isFlow_iff]
    constructor
    · rw [hSa, series_div_inl, if_neg N.hab, hNa, add_zero]
    · rintro (u | w) hu hu'
      · rw [series_div_inl]
        by_cases huc : u = N.b
        · subst huc
          rw [if_pos rfl, hNb, hMa]
          ring
        · rw [if_neg huc, add_zero]
          refine hN0 u ?_ huc
          intro hc
          exact hu (by rw [hSa, hc])
      · rw [series_div_inr]
        refine hM0 w.1 w.2 ?_
        intro hc
        exact hu' (by rw [hSb]; exact congrArg Sum.inr (Subtype.ext hc))

/-- The flows on a series composition are exactly the pairs of flows of the same strength. -/
def seriesFlowEquiv (N M : TTN) (t : ℝ) : (seriesTTN N M).Flow t ≃ N.Flow t × M.Flow t where
  toFun θ := (⟨fun e => θ.1 (Sum.inl e), ((series_isFlow_iff N M t θ.1).1 θ.2).1⟩,
              ⟨fun e => θ.1 (Sum.inr e), ((series_isFlow_iff N M t θ.1).1 θ.2).2⟩)
  invFun p := ⟨Sum.elim p.1.1 p.2.1, (series_isFlow_iff N M t _).2 ⟨p.1.2, p.2.2⟩⟩
  left_inv θ := Subtype.ext (funext (by rintro (e | e) <;> rfl))
  right_inv p := by
    refine Prod.ext (Subtype.ext (funext fun e => rfl)) (Subtype.ext (funext fun e => rfl))

/-- **Series law** for the effective resistance. -/
theorem effRes_series (N M : TTN) :
    (seriesTTN N M).effRes = N.effRes + M.effRes := by
  rw [effRes, flowRes, ← (seriesFlowEquiv N M 1).symm.iInf_comp]
  have : ∀ p : N.Flow 1 × M.Flow 1,
      ENNReal.ofReal ((seriesTTN N M).energy ((seriesFlowEquiv N M 1).symm p).1)
        = ENNReal.ofReal (N.energy p.1.1) + ENNReal.ofReal (M.energy p.2.1) := by
    intro p
    rw [show ((seriesFlowEquiv N M 1).symm p).1 = Sum.elim p.1.1 p.2.1 from rfl,
      series_energy]
    exact ENNReal.ofReal_add (N.energy_nonneg _) (M.energy_nonneg _)
  simp only [this]
  rw [iInf_add_iInf_prod (fun i : N.Flow 1 => ENNReal.ofReal (N.energy i.1))
    (fun j : M.Flow 1 => ENNReal.ofReal (M.energy j.1))]
  rfl

/-! ### Parallel composition -/

/-- Vertices of the parallel composition: both terminals of `M` are glued to those of `N`. -/
abbrev parV (N M : TTN) : Type := N.V ⊕ {v : M.V // v ≠ M.a ∧ v ≠ M.b}

instance (N M : TTN) : Fintype (parV N M) := by unfold parV; infer_instance
instance (N M : TTN) : DecidableEq (parV N M) := by unfold parV; infer_instance

/-- The embedding of the vertices of `M` into the parallel composition. -/
def parEmb (N M : TTN) (v : M.V) : parV N M :=
  if h : v = M.a then Sum.inl N.a else if h' : v = M.b then Sum.inl N.b else Sum.inr ⟨v, h, h'⟩

/-- The **parallel composition** of `N` and `M`: the two terminals are identified pairwise. -/
def parTTN (N M : TTN) : TTN where
  V := parV N M
  E := N.E ⊕ M.E
  fintypeV := inferInstance
  decEqV := inferInstance
  fintypeE := inferInstance
  tail := Sum.elim (fun e => Sum.inl (N.tail e)) (fun e => parEmb N M (M.tail e))
  head := Sum.elim (fun e => Sum.inl (N.head e)) (fun e => parEmb N M (M.head e))
  a := Sum.inl N.a
  b := Sum.inl N.b
  hab := fun h => N.hab (Sum.inl.inj h)

@[simp] lemma parEmb_eq_inl (N M : TTN) (v : M.V) (u : N.V) :
    parEmb N M v = Sum.inl u ↔ ((v = M.a ∧ N.a = u) ∨ (v = M.b ∧ N.b = u)) := by
  unfold parEmb
  by_cases h : v = M.a
  · simp [h, M.hab]
  · by_cases h' : v = M.b
    · simp [h', Ne.symm M.hab]
    · simp [h, h']

@[simp] lemma parEmb_eq_inr (N M : TTN) (v : M.V) (w : {x : M.V // x ≠ M.a ∧ x ≠ M.b}) :
    parEmb N M v = Sum.inr w ↔ v = w.1 := by
  unfold parEmb
  by_cases h : v = M.a
  · simp [h, Ne.symm w.2.1]
  · by_cases h' : v = M.b
    · simp [h', Ne.symm M.hab, Ne.symm w.2.2]
    · simp [h, h', Subtype.ext_iff]

lemma par_div_a (N M : TTN) (θ : (parTTN N M).E → ℝ) :
    (parTTN N M).div θ (Sum.inl N.a)
      = N.div (fun e => θ (Sum.inl e)) N.a + M.div (fun e => θ (Sum.inr e)) M.a := by
  classical
  simp only [TTN.div, parTTN, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Sum.inl.injEq, parEmb_eq_inl, and_true, Ne.symm N.hab, and_false, or_false]
  ring

lemma par_div_b (N M : TTN) (θ : (parTTN N M).E → ℝ) :
    (parTTN N M).div θ (Sum.inl N.b)
      = N.div (fun e => θ (Sum.inl e)) N.b + M.div (fun e => θ (Sum.inr e)) M.b := by
  classical
  simp only [TTN.div, parTTN, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Sum.inl.injEq, parEmb_eq_inl, and_true, N.hab, and_false, false_or]
  ring

lemma par_div_other (N M : TTN) (θ : (parTTN N M).E → ℝ) (u : N.V)
    (hu : u ≠ N.a) (hu' : u ≠ N.b) :
    (parTTN N M).div θ (Sum.inl u) = N.div (fun e => θ (Sum.inl e)) u := by
  classical
  simp only [TTN.div, parTTN, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Sum.inl.injEq, parEmb_eq_inl, Ne.symm hu, Ne.symm hu', and_false, or_self,
    if_false, Finset.sum_const_zero, add_zero]

lemma par_div_inr (N M : TTN) (θ : (parTTN N M).E → ℝ)
    (w : {x : M.V // x ≠ M.a ∧ x ≠ M.b}) :
    (parTTN N M).div θ (Sum.inr w) = M.div (fun e => θ (Sum.inr e)) w.1 := by
  classical
  simp only [TTN.div, parTTN, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    parEmb_eq_inr, reduceCtorEq, if_false, Finset.sum_const_zero, zero_add]

lemma par_energy (N M : TTN) (θ : (parTTN N M).E → ℝ) :
    (parTTN N M).energy θ
      = N.energy (fun e => θ (Sum.inl e)) + M.energy (fun e => θ (Sum.inr e)) := by
  simp only [TTN.energy, parTTN, Fintype.sum_sum_type]

lemma par_isFlow_of (N M : TTN) (t s : ℝ) (φ : N.E → ℝ) (ψ : M.E → ℝ)
    (hφ : N.IsFlow s φ) (hψ : M.IsFlow (t - s) ψ) :
    (parTTN N M).IsFlow t (Sum.elim φ ψ) := by
  classical
  have hPa : (parTTN N M).a = (Sum.inl N.a : parV N M) := rfl
  have hPb : (parTTN N M).b = (Sum.inl N.b : parV N M) := rfl
  have hNa := ((isFlow_iff N φ s).1 hφ).1
  have hN0 := ((isFlow_iff N φ s).1 hφ).2
  have hMa := ((isFlow_iff M ψ (t - s)).1 hψ).1
  have hM0 := ((isFlow_iff M ψ (t - s)).1 hψ).2
  rw [isFlow_iff]
  refine ⟨?_, ?_⟩
  · rw [hPa, par_div_a]
    show N.div φ N.a + M.div ψ M.a = t
    rw [hNa, hMa]
    ring
  · rintro (u | w) hu hu'
    · have hua : u ≠ N.a := fun hc => hu (by rw [hPa, hc])
      have hub : u ≠ N.b := fun hc => hu' (by rw [hPb, hc])
      rw [par_div_other N M _ u hua hub]
      exact hN0 u hua hub
    · rw [par_div_inr]
      exact hM0 w.1 w.2.1 w.2.2

lemma par_isFlow_iff (N M : TTN) (t : ℝ) (θ : (parTTN N M).E → ℝ) :
    (parTTN N M).IsFlow t θ ↔
      ∃ s : ℝ, N.IsFlow s (fun e => θ (Sum.inl e))
        ∧ M.IsFlow (t - s) (fun e => θ (Sum.inr e)) := by
  classical
  have hPa : (parTTN N M).a = (Sum.inl N.a : parV N M) := rfl
  have hPb : (parTTN N M).b = (Sum.inl N.b : parV N M) := rfl
  constructor
  · intro h
    refine ⟨N.div (fun e => θ (Sum.inl e)) N.a, ?_, ?_⟩
    · rw [isFlow_iff]
      refine ⟨rfl, ?_⟩
      intro u hu hu'
      have h1 := h (Sum.inl u)
      rw [par_div_other N M θ u hu hu'] at h1
      have hne : (Sum.inl u : parV N M) ≠ (parTTN N M).a := by
        rw [hPa]; exact fun hc => hu (Sum.inl.inj hc)
      have hne2 : (Sum.inl u : parV N M) ≠ (parTTN N M).b := by
        rw [hPb]; exact fun hc => hu' (Sum.inl.inj hc)
      rw [if_neg hne, if_neg hne2] at h1
      exact h1
    · rw [isFlow_iff]
      constructor
      · have h1 := h (Sum.inl N.a)
        rw [par_div_a, ← hPa, if_pos rfl] at h1
        linarith [h1]
      · intro w hw hw'
        have h1 := h (Sum.inr ⟨w, hw, hw'⟩)
        rw [par_div_inr] at h1
        have hne : (Sum.inr ⟨w, hw, hw'⟩ : parV N M) ≠ (parTTN N M).a := by
          rw [hPa]; exact fun hc => by cases hc
        have hne2 : (Sum.inr ⟨w, hw, hw'⟩ : parV N M) ≠ (parTTN N M).b := by
          rw [hPb]; exact fun hc => by cases hc
        rw [if_neg hne, if_neg hne2] at h1
        exact h1
  · rintro ⟨s, hN, hM⟩
    have hmain := par_isFlow_of N M t s _ _ hN hM
    have hθ : Sum.elim (fun e => θ (Sum.inl e)) (fun e => θ (Sum.inr e)) = θ := by
      funext x
      cases x <;> rfl
    rwa [hθ] at hmain

/-- The parallel effective resistance as an infimum over the splitting of the current. -/
lemma effRes_par_iInf (N M : TTN) :
    (parTTN N M).effRes = ⨅ s : ℝ, (N.flowRes s + M.flowRes (1 - s)) := by
  classical
  refine le_antisymm ?_ ?_
  · refine le_iInf fun s => ?_
    rw [flowRes, flowRes, ← iInf_add_iInf_prod (fun φ : N.Flow s => ENNReal.ofReal (N.energy φ.1))
      (fun ψ : M.Flow (1 - s) => ENNReal.ofReal (M.energy ψ.1))]
    refine le_iInf fun p => ?_
    have hflow : (parTTN N M).IsFlow 1 (Sum.elim p.1.1 p.2.1) :=
      par_isFlow_of N M 1 s _ _ p.1.2 p.2.2
    refine le_of_le_of_eq (iInf_le _ (⟨Sum.elim p.1.1 p.2.1, hflow⟩ : (parTTN N M).Flow 1)) ?_
    rw [show ((⟨Sum.elim p.1.1 p.2.1, hflow⟩ : (parTTN N M).Flow 1) : (parTTN N M).E → ℝ)
        = Sum.elim p.1.1 p.2.1 from rfl, par_energy]
    exact ENNReal.ofReal_add (N.energy_nonneg _) (M.energy_nonneg _)
  · refine le_iInf fun θ => ?_
    obtain ⟨s, hN, hM⟩ := (par_isFlow_iff N M 1 θ.1).1 θ.2
    refine le_trans (iInf_le _ s) ?_
    have h1 : N.flowRes s ≤ ENNReal.ofReal (N.energy (fun e => θ.1 (Sum.inl e))) :=
      iInf_le _ (⟨_, hN⟩ : N.Flow s)
    have h2 : M.flowRes (1 - s) ≤ ENNReal.ofReal (M.energy (fun e => θ.1 (Sum.inr e))) :=
      iInf_le _ (⟨_, hM⟩ : M.Flow (1 - s))
    calc N.flowRes s + M.flowRes (1 - s)
        ≤ ENNReal.ofReal (N.energy (fun e => θ.1 (Sum.inl e)))
          + ENNReal.ofReal (M.energy (fun e => θ.1 (Sum.inr e))) := add_le_add h1 h2
      _ = ENNReal.ofReal ((parTTN N M).energy θ.1) := by
          rw [par_energy]
          exact (ENNReal.ofReal_add (N.energy_nonneg _) (M.energy_nonneg _)).symm

/-- The elementary optimisation behind the parallel law. -/
lemma iInf_quad (A B : ℝ≥0∞) :
    (⨅ s : ℝ, (ENNReal.ofReal (s ^ 2) * A + ENNReal.ofReal ((1 - s) ^ 2) * B))
      = (A⁻¹ + B⁻¹)⁻¹ := by
  rcases eq_or_ne A 0 with rfl | hA0
  · refine le_antisymm ?_ (by simp)
    refine le_of_le_of_eq (iInf_le _ (1 : ℝ)) ?_
    simp
  rcases eq_or_ne B 0 with rfl | hB0
  · refine le_antisymm ?_ (by simp)
    refine le_of_le_of_eq (iInf_le _ (0 : ℝ)) ?_
    simp
  rcases eq_or_ne A ⊤ with rfl | hAtop
  · rcases eq_or_ne B ⊤ with rfl | hBtop
    · rw [show ((⊤ : ℝ≥0∞)⁻¹ + (⊤ : ℝ≥0∞)⁻¹)⁻¹ = ⊤ by simp]
      refine le_antisymm le_top ?_
      simp only [le_iInf_iff]
      intro s
      rcases eq_or_ne s 0 with rfl | hs
      · simp
      · have : ENNReal.ofReal (s ^ 2) ≠ 0 := by
          simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
          positivity
        simp [ENNReal.mul_top this]
    · have hBB : ((⊤ : ℝ≥0∞)⁻¹ + B⁻¹)⁻¹ = B := by simp
      rw [hBB]
      refine le_antisymm ?_ ?_
      · refine le_of_le_of_eq (iInf_le _ (0 : ℝ)) ?_
        simp
      · refine le_iInf fun s => ?_
        rcases eq_or_ne s 0 with rfl | hs
        · simp
        · have h : ENNReal.ofReal (s ^ 2) ≠ 0 := by
            simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
            positivity
          simp [ENNReal.mul_top h]
  rcases eq_or_ne B ⊤ with rfl | hBtop
  · have hAA : (A⁻¹ + (⊤ : ℝ≥0∞)⁻¹)⁻¹ = A := by simp
    rw [hAA]
    refine le_antisymm ?_ ?_
    · refine le_of_le_of_eq (iInf_le _ (1 : ℝ)) ?_
      simp
    · refine le_iInf fun s => ?_
      rcases eq_or_ne (1 - s) 0 with h1 | hs
      · have : s = 1 := by linarith [sub_eq_zero.mp h1]
        subst this
        simp
      · have h : ENNReal.ofReal ((1 - s) ^ 2) ≠ 0 := by
          simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
          positivity
        simp [ENNReal.mul_top h]
  · obtain ⟨a, ha0, rfl⟩ : ∃ a : ℝ, 0 < a ∧ A = ENNReal.ofReal a :=
      ⟨A.toReal, ENNReal.toReal_pos hA0 hAtop, (ENNReal.ofReal_toReal hAtop).symm⟩
    obtain ⟨b, hb0, rfl⟩ : ∃ b : ℝ, 0 < b ∧ B = ENNReal.ofReal b :=
      ⟨B.toReal, ENNReal.toReal_pos hB0 hBtop, (ENNReal.ofReal_toReal hBtop).symm⟩
    have hab : 0 < a + b := by linarith
    have key : ∀ s : ℝ, ENNReal.ofReal (s ^ 2) * ENNReal.ofReal a
        + ENNReal.ofReal ((1 - s) ^ 2) * ENNReal.ofReal b
        = ENNReal.ofReal (s ^ 2 * a + (1 - s) ^ 2 * b) := by
      intro s
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    have hRHS : ((ENNReal.ofReal a)⁻¹ + (ENNReal.ofReal b)⁻¹)⁻¹
        = ENNReal.ofReal (a * b / (a + b)) := by
      rw [← ENNReal.ofReal_inv_of_pos ha0, ← ENNReal.ofReal_inv_of_pos hb0,
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_inv_of_pos (by positivity)]
      congr 1
      field_simp
      ring
    simp only [key, hRHS]
    refine le_antisymm ?_ ?_
    · refine le_of_le_of_eq (iInf_le _ (b / (a + b))) ?_
      congr 1
      field_simp
      ring
    · refine le_iInf fun s => ?_
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_iff₀ hab]
      nlinarith [sq_nonneg ((a + b) * s - b)]

/-- **Parallel law** for the effective resistance.  This also covers the deletion of a
disconnected ("dangling") branch: if `M.effRes = ⊤` then the right-hand side is `N.effRes`. -/
theorem effRes_par (N M : TTN) :
    (parTTN N M).effRes = (N.effRes⁻¹ + M.effRes⁻¹)⁻¹ := by
  rw [effRes_par_iInf]
  simp only [flowRes_eq]
  exact iInf_quad N.effRes M.effRes

end TTN

end Cluster
