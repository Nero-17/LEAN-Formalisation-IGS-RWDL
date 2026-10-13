import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Parameters of the reduced two-terminal resistance process

This file formalises the parameters appearing in Subsection 4.1 ("Solution to the open problem
in [hambly2010diffusion]") of *Iterated Graph Systems (I): random walks and diffusion limits*.

For `p ∈ (0,1)`, given a red parent cell, the two conditional probabilities that *both* branches
survive (`diamond`) or *exactly one* branch survives (`series`) are
```
p_diamond = p^4 / (2 p^2 - p^4) = p^2 / (2 - p^2),
p_series  = (2 p^2 - 2 p^4) / (2 p^2 - p^4) = (2 - 2 p^2) / (2 - p^2).
```
The critical DHL parameter is `p_c = (√5 - 1)/2`, characterised by `1 - p_c = p_c^2`.
-/

namespace Reduced

open Real

/-- Conditional probability that both branches survive (diamond case). -/
noncomputable def pdiamond (p : ℝ) : ℝ := p ^ 2 / (2 - p ^ 2)

/-- Conditional probability that exactly one branch survives (series case). -/
noncomputable def pseries (p : ℝ) : ℝ := (2 - 2 * p ^ 2) / (2 - p ^ 2)

/-- The critical DHL bond-percolation parameter. -/
noncomputable def pc : ℝ := (Real.sqrt 5 - 1) / 2

lemma two_sub_sq_pos {p : ℝ} (hp1 : p < 1) (hp0 : 0 < p) : 0 < 2 - p ^ 2 := by
  nlinarith [sq_nonneg p, hp1, hp0]

/-- The two conditional probabilities sum to `1`. -/
lemma pseries_add_pdiamond {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    pseries p + pdiamond p = 1 := by
  have h : (2 - p ^ 2) ≠ 0 := ne_of_gt (two_sub_sq_pos hp1 hp0)
  unfold pseries pdiamond
  field_simp
  ring

lemma pdiamond_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < pdiamond p := by
  unfold pdiamond
  apply div_pos
  · positivity
  · exact two_sub_sq_pos hp1 hp0

lemma pdiamond_lt_one {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : pdiamond p < 1 := by
  unfold pdiamond
  rw [div_lt_one (two_sub_sq_pos hp1 hp0)]
  nlinarith [sq_nonneg p, hp1, hp0]

lemma pseries_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < pseries p := by
  have := pdiamond_lt_one hp0 hp1
  have := pseries_add_pdiamond hp0 hp1
  linarith

lemma pseries_nonneg {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 ≤ pseries p :=
  (pseries_pos hp0 hp1).le

lemma pdiamond_nonneg {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 ≤ pdiamond p :=
  (pdiamond_pos hp0 hp1).le

/-- The critical parameter is positive. -/
lemma pc_pos : 0 < pc := by
  unfold pc
  have : (2 : ℝ) < Real.sqrt 5 := by
    have h4 : (2 : ℝ) = Real.sqrt 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h4]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

lemma pc_lt_one : pc < 1 := by
  unfold pc
  have : Real.sqrt 5 < 3 := by
    have h9 : (3 : ℝ) = Real.sqrt 9 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h9]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- Defining identity of the critical parameter: `1 - p_c = p_c ^ 2`. -/
lemma pc_sq : pc ^ 2 = 1 - pc := by
  unfold pc
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-- At the critical parameter, `p_diamond = √5 - 2`. -/
lemma pdiamond_pc : pdiamond pc = Real.sqrt 5 - 2 := by
  have hden : (2 - pc ^ 2) ≠ 0 := ne_of_gt (two_sub_sq_pos pc_lt_one pc_pos)
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold pdiamond
  rw [div_eq_iff hden, pc_sq]
  unfold pc
  nlinarith [h5]

/-- At the critical parameter, `p_diamond < 1/2`. -/
lemma pdiamond_pc_lt_half : pdiamond pc < 1 / 2 := by
  rw [pdiamond_pc]
  have : Real.sqrt 5 < 2.5 := by
    have h625 : (2.5 : ℝ) = Real.sqrt 6.25 := by
      rw [show (6.25 : ℝ) = 2.5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h625]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

end Reduced
