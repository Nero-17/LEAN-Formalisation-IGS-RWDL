import Mathlib

/-!
# Section 3, step 3: the on-diagonal lower bound

This file formalises Theorem "general-lower" of *Iterated Graph Systems (I)*
(arXiv:2603.13798): a uniform lower bound on the probability that the diffusion
`W` has not left the ball `B(x,r)` by time `t` forces the on-diagonal heat kernel
to be at least the reciprocal of the volume of that ball.

Everything about the construction of the diffusion is treated as a black box.
Concretely, the diffusion enters only through:

* `hstay`  : `P_x(W_t ∈ B(x,r)) = ∫_{B(x,r)} p_t(x,y) dμ(y) ≥ pstay`
             (the survival estimate, Corollary "sec31_continuous_stay"),
* `hCK`    : `∫ (p_t(x,y))² dμ(y) = p_{2t}(x,x)`
             (Chapman--Kolmogorov together with symmetry of the kernel),
* `hmem`   : `p_t(x,·) ∈ L²(μ)`,

and the argument itself — Cauchy--Schwarz on the ball — is proved here in full.
-/

namespace IGS

open MeasureTheory

variable {X : Type*} [MeasurableSpace X]

/--
**Cauchy--Schwarz on a set of finite measure.**
If `0 ≤ q ≤ ∫_B f dμ` with `f ≥ 0` in `L²(μ)` and `μ B < ∞`, then
`q² ≤ μ(B) * ∫ f² dμ`.
-/
theorem sq_le_measure_mul_integral_sq (mu : Measure X) (B : Set X) (f : X → ℝ) (q : ℝ)
    (hq0 : 0 ≤ q) (hf0 : 0 ≤ᵐ[mu] f) (hf : MemLp f 2 mu) (hB : mu B ≠ ⊤)
    (hq : q ≤ ∫ y in B, f y ∂mu) :
    q ^ 2 ≤ (mu B).toReal * ∫ y, (f y) ^ 2 ∂mu := by
  haveI : IsFiniteMeasure (mu.restrict B) :=
    ⟨by rwa [Measure.restrict_apply_univ, lt_top_iff_ne_top]⟩
  have hpq : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) (mu.restrict B) := by
    have := hf.restrict B
    simpa [ENNReal.ofReal_ofNat] using this
  have hg' : MemLp (fun _ : X => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) (mu.restrict B) :=
    memLp_const 1
  have key := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := mu.restrict B) hpq
      (ae_restrict_of_ae hf0) (by filter_upwards with x using zero_le_one) hf' hg'
  simp only [mul_one, integral_const, Real.one_rpow, smul_eq_mul, mul_one] at key
  -- rewrite the two `rpow`s
  have hvol : (mu.restrict B).real Set.univ = (mu B).toReal := by
    simp [Measure.real]
  have hsq : ∀ a : X, f a ^ (2 : ℝ) = f a ^ (2 : ℕ) := by
    intro a
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [hsq, hvol] at key
  -- nonnegativity of the two integrals
  set A := ∫ y in B, (f y) ^ (2 : ℕ) ∂mu with hA
  have hA0 : 0 ≤ A := integral_nonneg fun y => by positivity
  have hM0 : 0 ≤ (mu B).toReal := ENNReal.toReal_nonneg
  have hrw : A ^ (1 / 2 : ℝ) * ((mu B).toReal) ^ (1 / 2 : ℝ)
      = Real.sqrt A * Real.sqrt ((mu B).toReal) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [hrw] at key
  -- square the Cauchy--Schwarz inequality
  have hsqle : q ^ 2 ≤ (Real.sqrt A * Real.sqrt ((mu B).toReal)) ^ 2 :=
    pow_le_pow_left₀ hq0 (le_trans hq key) 2
  have hexp : (Real.sqrt A * Real.sqrt ((mu B).toReal)) ^ 2 = A * (mu B).toReal := by
    rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hM0]
  rw [hexp] at hsqle
  -- finally compare the integral over `B` with the integral over the whole space
  have hle : A ≤ ∫ y, (f y) ^ (2 : ℕ) ∂mu := by
    have hint : Integrable (fun y => (f y) ^ (2 : ℕ)) mu := by
      have := hf.integrable_sq
      simpa using this
    have := integral_mono_measure (μ := mu.restrict B) (ν := mu)
      (f := fun y => (f y) ^ (2 : ℕ)) Measure.restrict_le_self
      (Filter.Eventually.of_forall fun y => by positivity) hint
    simpa [hA] using this
  calc q ^ 2 ≤ A * (mu B).toReal := hsqle
    _ = (mu B).toReal * A := by ring
    _ ≤ (mu B).toReal * ∫ y, (f y) ^ (2 : ℕ) ∂mu := by
        exact mul_le_mul_of_nonneg_left hle hM0

/--
**On-diagonal lower bound (Theorem "general-lower").**

`p` is the heat kernel of the limiting diffusion, `mu` its reference measure and
`x` a point of the state space.  Given

* the survival estimate `pstay ≤ P_x(W_t ∈ B(x,r)) = ∫_{B(x,r)} p t x y dμ(y)`,
* the semigroup identity `∫ (p t x y)² dμ(y) = p (2t) x x`,

one gets `p_{2t}(x,x) ≥ pstay² / μ(B(x,r))`, i.e. the on-diagonal value is at
least the reciprocal of the volume of the ball, up to the constant `pstay²`.
-/
theorem heat_kernel_on_diagonal_lower [PseudoMetricSpace X]
    (p : ℝ → X → X → ℝ) (mu : Measure X) (x : X) (t r pstay : ℝ)
    (hpstay : 0 ≤ pstay)
    (hp0 : 0 ≤ᵐ[mu] fun y => p t x y)
    (hmem : MemLp (fun y => p t x y) 2 mu)
    (hball : mu (Metric.ball x r) ≠ ⊤)
    (hstay : pstay ≤ ∫ y in Metric.ball x r, p t x y ∂mu)
    (hCK : ∫ y, (p t x y) ^ 2 ∂mu = p (2 * t) x x) :
    pstay ^ 2 ≤ (mu (Metric.ball x r)).toReal * p (2 * t) x x := by
  have := sq_le_measure_mul_integral_sq mu (Metric.ball x r) (fun y => p t x y) pstay
    hpstay hp0 hmem hball hstay
  rwa [hCK] at this

/-- The same conclusion written as a genuine lower bound on `p_{2t}(x,x)`. -/
theorem heat_kernel_on_diagonal_lower' [PseudoMetricSpace X]
    (p : ℝ → X → X → ℝ) (mu : Measure X) (x : X) (t r pstay : ℝ)
    (hpstay : 0 ≤ pstay)
    (hp0 : 0 ≤ᵐ[mu] fun y => p t x y)
    (hmem : MemLp (fun y => p t x y) 2 mu)
    (hball : mu (Metric.ball x r) ≠ ⊤)
    (hballpos : 0 < (mu (Metric.ball x r)).toReal)
    (hstay : pstay ≤ ∫ y in Metric.ball x r, p t x y ∂mu)
    (hCK : ∫ y, (p t x y) ^ 2 ∂mu = p (2 * t) x x) :
    pstay ^ 2 / (mu (Metric.ball x r)).toReal ≤ p (2 * t) x x := by
  have h := heat_kernel_on_diagonal_lower p mu x t r pstay hpstay hp0 hmem hball hstay hCK
  rw [div_le_iff₀ hballpos]
  linarith [h]

end IGS
