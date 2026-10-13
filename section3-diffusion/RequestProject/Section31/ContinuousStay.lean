import Mathlib

/-!
# §3.1, step 7: passing the stay estimate to the limit
(Corollary `sec31_continuous_stay`)

Reference: arXiv:2603.13798, §3.1, Corollary `sec31_continuous_stay`.

Granting Theorem `sec31_ghps` (convergence in distribution of the rescaled walks
to the diffusion `W`) and the Skorokhod representation theorem — both cited by
the paper, and both hypotheses here — the corollary follows from two elementary
steps, and both are proved in this file.

1. **A triangle inequality.**  On the Skorokhod coupling, if the starting points
   are `r/4`-close, the paths are uniformly `r/4`-close, and the discrete path
   stays within `δ ≤ r/2` of its starting point, then the limit path stays
   within `r` of `x`.  This is `dist_lt_of_skorokhod_coupling`.

2. **A probability limit.**  If `P(E_n) ≥ p` for all `n`, if `E_n ∩ G_n ⊆ E`
   where `G_n` is the coupling event of step 1, and if `P(G_n) → 1` (which is
   what almost sure convergence in path space gives), then `P(E) ≥ p`.  This is
   `le_measure_of_eventual_inclusion`.

Together: `P_x(τ_{B(x,r)} > t_r) ≥ p_stay` with
`t_r = c_stay 4^{-d_w} r^{d_w}`, which is the corollary.
-/

namespace IGS.Sec31

open MeasureTheory Filter Topology

/--
**Step 1 of Corollary `sec31_continuous_stay`.**
If `d(x_n, x) < r/4`, the coupled paths satisfy `d(Y_s, W_s) < r/4`, and
`d(Y_s, x_n) ≤ δ ≤ r/2`, then `d(W_s, x) < r`.
-/
theorem dist_lt_of_skorokhod_coupling {X : Type*} [MetricSpace X]
    (x xn ys ws : X) (r delta : ℝ)
    (h1 : dist xn x < r / 4) (h2 : dist ys ws < r / 4)
    (h3 : dist ys xn ≤ delta) (h4 : delta ≤ r / 2) :
    dist ws x < r := by
  have := dist_triangle4 ws ys xn x
  rw [dist_comm ws ys] at this
  linarith

/--
**Step 2 of Corollary `sec31_continuous_stay`.**
`P(E) ≥ p` if `P(E_n) ≥ p` for every `n`, `E_n ∩ G_n ⊆ E`, and `P(G_n) → 1`.
-/
theorem le_measure_of_eventual_inclusion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p : ℝ) (E : Set Ω) (En Gn : ℕ → Set Ω)
    (hGmeas : ∀ n, MeasurableSet (Gn n))
    (hp : ∀ n, p ≤ (P (En n)).toReal) (hsub : ∀ n, En n ∩ Gn n ⊆ E)
    (hG : Tendsto (fun n => (P (Gn n)).toReal) atTop (𝓝 1)) :
    p ≤ (P E).toReal := by
  have key : ∀ n, p ≤ (P E).toReal + 1 - (P (Gn n)).toReal := by
    intro n
    have hsplit : En n ⊆ (En n ∩ Gn n) ∪ (Gn n)ᶜ := by
      intro ω hω
      by_cases h : ω ∈ Gn n
      · exact Or.inl ⟨hω, h⟩
      · exact Or.inr h
    have h1 : P (En n) ≤ P (En n ∩ Gn n) + P (Gn n)ᶜ :=
      le_trans (measure_mono hsplit) (measure_union_le _ _)
    have h2 : (P (En n)).toReal ≤ (P (En n ∩ Gn n)).toReal + (P (Gn n)ᶜ).toReal := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      exact ENNReal.toReal_mono (by finiteness) h1
    have h3 : (P (En n ∩ Gn n)).toReal ≤ (P E).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (hsub n))
    have h4 : (P (Gn n)ᶜ).toReal = 1 - (P (Gn n)).toReal := by
      rw [prob_compl_eq_one_sub (hGmeas n)]
      simp [ENNReal.toReal_sub_of_le prob_le_one (by finiteness)]
    linarith [hp n]
  have hlim : Tendsto (fun n => (P E).toReal + 1 - (P (Gn n)).toReal) atTop
      (𝓝 ((P E).toReal)) := by
    have h := (tendsto_const_nhds (x := (P E).toReal + 1) (f := atTop (α := ℕ))).sub hG
    simpa using h
  exact ge_of_tendsto hlim (Eventually.of_forall key)

end IGS.Sec31
