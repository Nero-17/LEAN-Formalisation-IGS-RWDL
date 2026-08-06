import Mathlib

/-!
# Elementary real identities and inequalities

Pointwise real-analysis facts used in Subsection 4.1.  These are the algebraic identities and
inequalities underlying the one-step moment computations for the reduced resistance process.

The parallel (diamond) combination of two positive resistances `a, b` is `a*b/(a+b)`.
-/

namespace Reduced

open Real

/-- Parallel (diamond) combination of two positive resistances. -/
noncomputable def par (a b : ℝ) : ℝ := a * b / (a + b)

/-- Diamond value from four positive resistances: parallel of two series pairs. -/
noncomputable def diamondVal (x1 x2 x3 x4 : ℝ) : ℝ := par (x1 + x2) (x3 + x4)

/-- Key identity: `a*b/(a+b) = (a+b)/4 - (a-b)^2/(4(a+b))`. -/
lemma par_eq (a b : ℝ) (h : 0 < a + b) :
    par a b = (a + b) / 4 - (a - b) ^ 2 / (4 * (a + b)) := by
  unfold par
  field_simp
  ring

/-- Reciprocal identity: `1/(x+y) = (1/4)(1/x + 1/y) - (1/4)·(x-y)^2/(xy(x+y))`. -/
lemma inv_add_eq (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (x + y)⁻¹ = (1 / 4) * (x⁻¹ + y⁻¹) - (1 / 4) * ((x - y) ^ 2 / (x * y * (x + y))) := by
  have hxy : 0 < x + y := by linarith
  field_simp
  ring

/-- Reciprocal of the parallel combination is the sum of reciprocals. -/
lemma inv_par (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (par a b)⁻¹ = a⁻¹ + b⁻¹ := by
  have hab : 0 < a + b := by linarith
  unfold par
  field_simp
  ring

/-- `a*b/(a+b) ≤ (a+b)/4` for positive `a, b` (AM–GM type bound). -/
lemma par_le_quarter (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    par a b ≤ (a + b) / 4 := by
  have hab : 0 < a + b := by linarith
  rw [par, div_le_iff₀ hab]
  nlinarith [sq_nonneg (a - b)]

/-- `a*b/(a+b) ≤ √(a*b)/2` for positive `a, b` (AM–GM type bound). -/
lemma par_le_sqrt (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    par a b ≤ Real.sqrt (a * b) / 2 := by
  have hab : 0 < a + b := by linarith
  have hs : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt (by positivity)
  -- a + b ≥ 2√(ab)
  have hamgm : 2 * Real.sqrt (a * b) ≤ a + b := by
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha.le,
      Real.sq_sqrt hb.le, Real.sqrt_mul_self ha.le,
      Real.sqrt_mul ha.le b, Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  rw [par, div_le_iff₀ hab]
  nlinarith [hsq, hs, hamgm, mul_pos ha hb]

/-- The map `x ↦ x - (x-1)^2/(2x-1)` is monotone on `[1, ∞)`. -/
lemma logistic2_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    x - (x - 1) ^ 2 / (2 * x - 1) ≤ y - (y - 1) ^ 2 / (2 * y - 1) := by
  have hx0 : 0 < 2 * x - 1 := by linarith
  have hy0 : 0 < 2 * y - 1 := by linarith
  have key : (y - 1) ^ 2 / (2 * y - 1) - (x - 1) ^ 2 / (2 * x - 1) ≤ y - x := by
    rw [div_sub_div _ _ (ne_of_gt hy0) (ne_of_gt hx0), div_le_iff₀ (mul_pos hy0 hx0)]
    nlinarith [hx, hxy, hx0, hy0, sq_nonneg (x - y), mul_pos hx0 hy0]
  linarith [key]

/-- The map `x ↦ x - (x-1)^2/(3x-1)` is monotone on `[1, ∞)`. -/
lemma logistic3_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    x - (x - 1) ^ 2 / (3 * x - 1) ≤ y - (y - 1) ^ 2 / (3 * y - 1) := by
  have hx0 : 0 < 3 * x - 1 := by linarith
  have hy0 : 0 < 3 * y - 1 := by linarith
  have key : (y - 1) ^ 2 / (3 * y - 1) - (x - 1) ^ 2 / (3 * x - 1) ≤ y - x := by
    rw [div_sub_div _ _ (ne_of_gt hy0) (ne_of_gt hx0), div_le_iff₀ (mul_pos hy0 hx0)]
    nlinarith [hx, hxy, hx0, hy0, sq_nonneg (x - y), mul_pos hx0 hy0]
  linarith [key]

/-- Deterministic series bound: if `1 ≤ x, y ≤ B` then `1 ≤ x + y ≤ 2B` (for `1 ≤ B`). -/
lemma series_bounds {x y B : ℝ} (hx1 : 1 ≤ x) (hxB : x ≤ B) (hy1 : 1 ≤ y) (hyB : y ≤ B) :
    1 ≤ x + y ∧ x + y ≤ 2 * B := by
  constructor <;> linarith

/-- Deterministic diamond bound: if each `xᵢ ∈ [1, B]` with `1 ≤ B`, then the diamond value
lies in `[1, B]`. -/
lemma diamond_bounds {x1 x2 x3 x4 B : ℝ}
    (h11 : 1 ≤ x1) (h1B : x1 ≤ B) (h21 : 1 ≤ x2) (h2B : x2 ≤ B)
    (h31 : 1 ≤ x3) (h3B : x3 ≤ B) (h41 : 1 ≤ x4) (h4B : x4 ≤ B) :
    1 ≤ diamondVal x1 x2 x3 x4 ∧ diamondVal x1 x2 x3 x4 ≤ B := by
  unfold diamondVal par
  set a := x1 + x2 with ha
  set b := x3 + x4 with hb
  have ha2 : 2 ≤ a := by simp only [ha]; linarith
  have hb2 : 2 ≤ b := by simp only [hb]; linarith
  have haB : a ≤ 2 * B := by simp only [ha]; linarith
  have hbB : b ≤ 2 * B := by simp only [hb]; linarith
  have hab : 0 < a + b := by linarith
  constructor
  · rw [le_div_iff₀ hab]; nlinarith [ha2, hb2]
  · rw [div_le_iff₀ hab]; nlinarith [ha2, hb2, haB, hbB]

end Reduced
