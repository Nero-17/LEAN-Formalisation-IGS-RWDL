import Mathlib

/-!
# Oscillation of a function on a finite set, and oscillation contraction

This file provides the **oscillation contraction machinery** that the new proof of
Lemma 2.22 of the paper uses in order to *prove* (rather than assume) the
near-diagonal Green comparison.

The mathematical content is elementary but is exactly what the analytic argument
needs:

* `oscOn f A` : the oscillation `sup_A f - inf_A f` of `f` over a finite set `A`;
* `oscOn_le_of_pairwise`, `oscOn_mono`, `oscOn_le_sub` : the basic calculus of
  oscillations;
* `oscOn_meanValue_contraction` : the **one-step contraction**.  If every point
  of the child set `A`, with the possible exception of one distinguished
  boundary point `p ∈ B`, realises `f` as an average of the boundary values
  `f|_B` with all weights at least `ε`, then
  `oscOn f A ≤ (1 - ε) · oscOn f B`;
* `oscOn_chain_pow` : iterating a contraction along a chain of nested cells,
  `oscOn f (C j) ≤ θ ^ j · oscOn f (C 0)`;
* `sub_oscOn_le` / `half_le_of_oscOn_le_half` : the conclusion drawn from a small
  oscillation, namely that a function equal to its maximal value `1` at a point
  of the cell stays `≥ 1/2` on the whole cell.
-/

namespace EIGS

open Finset

variable {V : Type*}

/-- The **oscillation** of `f` over the finite set `A`: `sup_A f - inf_A f`
(and `0` on the empty set). -/
noncomputable def oscOn (f : V → ℝ) (A : Finset V) : ℝ :=
  if h : A.Nonempty then A.sup' h f - A.inf' h f else 0

lemma oscOn_eq {f : V → ℝ} {A : Finset V} (h : A.Nonempty) :
    oscOn f A = A.sup' h f - A.inf' h f := by
  simp [oscOn, h]

lemma oscOn_empty (f : V → ℝ) : oscOn f (∅ : Finset V) = 0 := by
  simp [oscOn]

/-- The infimum over a nonempty finite set is at most the supremum. -/
lemma inf'_le_sup' {f : V → ℝ} {A : Finset V} (h : A.Nonempty) :
    A.inf' h f ≤ A.sup' h f := by
  obtain ⟨x, hx⟩ := h
  exact le_trans (Finset.inf'_le f hx) (Finset.le_sup' f hx)

/-- Oscillations are nonnegative. -/
lemma oscOn_nonneg (f : V → ℝ) (A : Finset V) : 0 ≤ oscOn f A := by
  by_cases h : A.Nonempty
  · rw [oscOn_eq h]
    have := inf'_le_sup' (f := f) h
    linarith
  · simp [oscOn, h]

/-- Any difference of values is bounded by the oscillation. -/
lemma sub_le_oscOn {f : V → ℝ} {A : Finset V} {x y : V} (hx : x ∈ A) (hy : y ∈ A) :
    f x - f y ≤ oscOn f A := by
  have h : A.Nonempty := ⟨x, hx⟩
  rw [oscOn_eq h]
  have h1 : f x ≤ A.sup' h f := Finset.le_sup' f hx
  have h2 : A.inf' h f ≤ f y := Finset.inf'_le f hy
  linarith

/-- A value minus the oscillation bounds every other value from below. -/
lemma sub_oscOn_le {f : V → ℝ} {A : Finset V} {x y : V} (hx : x ∈ A) (hy : y ∈ A) :
    f x - oscOn f A ≤ f y := by
  have := sub_le_oscOn (f := f) hx hy
  linarith

/-- A pairwise bound on differences bounds the oscillation. -/
lemma oscOn_le_of_pairwise {f : V → ℝ} {A : Finset V} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x ∈ A, ∀ y ∈ A, f x - f y ≤ c) : oscOn f A ≤ c := by
  by_cases hA : A.Nonempty
  · rw [oscOn_eq hA]
    obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup' hA f
    obtain ⟨y, hy, hye⟩ := Finset.exists_mem_eq_inf' hA f
    rw [hxe, hye]
    exact h x hx y hy
  · simpa [oscOn, hA] using hc

/-- Monotonicity of the oscillation in the set. -/
lemma oscOn_mono {f : V → ℝ} {A B : Finset V} (hAB : A ⊆ B) :
    oscOn f A ≤ oscOn f B := by
  refine oscOn_le_of_pairwise (oscOn_nonneg f B) ?_
  intro x hx y hy
  exact sub_le_oscOn (hAB hx) (hAB hy)

/-- Two-sided pointwise bounds bound the oscillation. -/
lemma oscOn_le_sub {f : V → ℝ} {A : Finset V} {a b : ℝ} (hab : a ≤ b)
    (hlo : ∀ x ∈ A, a ≤ f x) (hhi : ∀ x ∈ A, f x ≤ b) :
    oscOn f A ≤ b - a := by
  refine oscOn_le_of_pairwise (by linarith) ?_
  intro x hx y hy
  have := hhi x hx
  have := hlo y hy
  linarith

/-- **Iterated contraction.**  If the oscillation contracts by the factor `θ`
at each step of a chain of sets, then it contracts by `θ ^ j` after `j` steps. -/
lemma oscOn_chain_pow {f : V → ℝ} {C : ℕ → Finset V} {θ : ℝ} (hθ : 0 ≤ θ) (j : ℕ)
    (hstep : ∀ i, i < j → oscOn f (C (i + 1)) ≤ θ * oscOn f (C i)) :
    oscOn f (C j) ≤ θ ^ j * oscOn f (C 0) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have h1 : oscOn f (C (j + 1)) ≤ θ * oscOn f (C j) :=
        hstep j (Nat.lt_succ_self j)
      have h2 : oscOn f (C j) ≤ θ ^ j * oscOn f (C 0) :=
        ih fun i hi => hstep i (by omega)
      calc oscOn f (C (j + 1)) ≤ θ * oscOn f (C j) := h1
        _ ≤ θ * (θ ^ j * oscOn f (C 0)) := by
            exact mul_le_mul_of_nonneg_left h2 hθ
        _ = θ ^ (j + 1) * oscOn f (C 0) := by ring

/-- If `f` attains the value `1` at a point of `A` and its oscillation over `A`
is at most `1/2`, then `f ≥ 1/2` on `A`. -/
lemma half_le_of_oscOn_le_half {f : V → ℝ} {A : Finset V} {v : V} (hv : v ∈ A)
    (hfv : f v = 1) (hosc : oscOn f A ≤ 1 / 2) :
    ∀ y ∈ A, 1 / 2 ≤ f y := by
  intro y hy
  have := sub_le_oscOn (f := f) hv hy
  rw [hfv] at this
  linarith

/-! ### The one-step mean-value contraction -/

/-- **Mean-value oscillation contraction.**

Suppose every point `y` of the child set `A` other than one distinguished
boundary point `p ∈ B` writes `f y` as a weighted average of the values of `f`
on the (nonempty) boundary set `B`, with all weights at least `ε ∈ (0, 1]`.
Then the oscillation of `f` over `A` contracts:
`oscOn f A ≤ (1 - ε) * oscOn f B`.

This is the abstract form of the statement "a function harmonic in the interior
of a cell has oscillation over a child cell at most `θ` times its oscillation
over the cell", with `θ = 1 - ε`; the exceptional point `p` is the planting
vertex shared by the child cell and the boundary of the parent cell. -/
lemma oscOn_meanValue_contraction {f : V → ℝ} {A B : Finset V} {p : V}
    {w : V → V → ℝ} {ε : ℝ} (hB : B.Nonempty) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hpB : p ∈ B)
    (hw_lb : ∀ y ∈ A, y ≠ p → ∀ z ∈ B, ε ≤ w y z)
    (hw_sum : ∀ y ∈ A, y ≠ p → ∑ z ∈ B, w y z = 1)
    (hw_rep : ∀ y ∈ A, y ≠ p → f y = ∑ z ∈ B, w y z * f z) :
    oscOn f A ≤ (1 - ε) * oscOn f B := by
  set M := B.sup' hB f with hM
  set m := B.inf' hB f with hm
  have hmM : m ≤ M := inf'_le_sup' hB
  have hoscB : oscOn f B = M - m := oscOn_eq hB
  -- key: values at non-exceptional points are squeezed
  have key : ∀ y ∈ A, y ≠ p → m + ε * (M - m) ≤ f y ∧ f y ≤ M - ε * (M - m) := by
    intro y hy hyp
    have hlb := hw_lb y hy hyp
    have hsum := hw_sum y hy hyp
    have hrep := hw_rep y hy hyp
    have hnn : ∀ z ∈ B, 0 ≤ w y z := fun z hz => le_trans hε0 (hlb z hz)
    -- pick the point where f attains its minimum / maximum on B
    obtain ⟨z₀, hz₀, hz₀e⟩ := Finset.exists_mem_eq_inf' hB f
    obtain ⟨z₁, hz₁, hz₁e⟩ := Finset.exists_mem_eq_sup' hB f
    have hfz₀ : f z₀ = m := hz₀e.symm
    have hfz₁ : f z₁ = M := hz₁e.symm
    have hw0 : ε ≤ w y z₀ := hlb z₀ hz₀
    have hw1 : ε ≤ w y z₁ := hlb z₁ hz₁
    constructor
    · -- lower bound: `f y = m + ∑ w (f - m) ≥ m + w(z₁)(M - m) ≥ m + ε (M - m)`
      have hsplit : f y = m + ∑ z ∈ B, w y z * (f z - m) := by
        rw [hrep]
        have : ∑ z ∈ B, w y z * (f z - m) = ∑ z ∈ B, w y z * f z - m := by
          simp only [mul_sub]
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
        rw [this]; ring
      have hterm : w y z₁ * (f z₁ - m) ≤ ∑ z ∈ B, w y z * (f z - m) := by
        refine Finset.single_le_sum (f := fun z => w y z * (f z - m)) ?_ hz₁
        intro z hz
        have hzm : m ≤ f z := Finset.inf'_le f hz
        have := hnn z hz
        nlinarith
      rw [hsplit, hfz₁] at *
      nlinarith
    · -- upper bound, symmetric
      have hsplit : f y = M - ∑ z ∈ B, w y z * (M - f z) := by
        rw [hrep]
        have : ∑ z ∈ B, w y z * (M - f z) = M - ∑ z ∈ B, w y z * f z := by
          simp only [mul_sub]
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
        rw [this]; ring
      have hterm : w y z₀ * (M - f z₀) ≤ ∑ z ∈ B, w y z * (M - f z) := by
        refine Finset.single_le_sum (f := fun z => w y z * (M - f z)) ?_ hz₀
        intro z hz
        have hzM : f z ≤ M := Finset.le_sup' f hz
        have := hnn z hz
        nlinarith
      rw [hsplit, hfz₀] at *
      nlinarith
  -- the exceptional point is a boundary point, so its value lies in `[m, M]`
  have hp_lo : m ≤ f p := Finset.inf'_le f hpB
  have hp_hi : f p ≤ M := Finset.le_sup' f hpB
  rw [hoscB]
  refine oscOn_le_of_pairwise (by nlinarith) ?_
  intro x hx y hy
  by_cases hxp : x = p <;> by_cases hyp : y = p
  · subst hxp; simp [hyp]; nlinarith
  · subst hxp
    have := (key y hy hyp).1
    nlinarith
  · have := (key x hx hxp).2
    subst hyp
    nlinarith
  · have h1 := (key x hx hxp).2
    have h2 := (key y hy hyp).1
    nlinarith

end EIGS
