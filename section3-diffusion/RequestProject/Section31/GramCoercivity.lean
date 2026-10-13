import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Stable coercivity of finite Gram matrices

This is the quantitative coefficient estimate needed in the liminf argument of
Theorem `sec31_mosco`.  Entrywise errors in an actual finite Gram matrix are
controlled uniformly over all coefficient vectors.  A positive lower bound
for the limiting matrix consequently gives a lower bound for every sufficiently
late approximating matrix; bounded represented norms then bound coefficients.

The matrix calculation is independent of any assumed Mosco convergence.  Its
application still requires the paper's actual limiting spline Gram matrix and
its positivity to be identified.
-/

namespace IGS.Sec31

open Filter Topology

variable {Index : Type*} [Fintype Index]

noncomputable def gramQuadratic (matrix : Index → Index → ℝ) (coefficients : Index → ℝ) : ℝ :=
  ∑ first, ∑ second, coefficients first * matrix first second * coefficients second

theorem gramQuadratic_inner_eq_norm_sq
    {Hilbert : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    (vectors : Index → Hilbert) (coefficients : Index → ℝ) :
    gramQuadratic (fun first second => inner ℝ (vectors first) (vectors second)) coefficients =
      ‖∑ index, coefficients index • vectors index‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [gramQuadratic, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  rw [real_inner_comm (vectors second) (vectors first)]
  ring

/-- Positivity of the limiting Gram matrix is proved from independence of the
actual Hilbert-space vectors, rather than postulated as a matrix estimate. -/
theorem exists_gramQuadratic_coercive_of_linearIndependent
    {Hilbert : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    (vectors : Index → Hilbert) (independent : LinearIndependent ℝ vectors) :
    ∃ coercivity : ℝ, 0 < coercivity ∧ ∀ coefficients : Index → ℝ,
      coercivity * (∑ index, (coefficients index) ^ 2) ≤
        gramQuadratic (fun first second => inner ℝ (vectors first) (vectors second)) coefficients := by
  obtain ⟨inverseBound, inverseBoundPositive, inverseEstimate⟩ :=
    (Fintype.linearCombination ℝ vectors).injective_iff_antilipschitz.mp
      independent.fintypeLinearCombination_injective
  refine ⟨1 / (Fintype.card Index * (inverseBound : ℝ) ^ 2 + 1), by positivity, ?_⟩
  intro coefficients
  have coefficientNormBound := ZeroHomClass.bound_of_antilipschitz
    (Fintype.linearCombination ℝ vectors) inverseEstimate coefficients
  have coefficientSquareBound :
      ‖coefficients‖ ^ 2 ≤ (inverseBound : ℝ) ^ 2 * ‖∑ index, coefficients index • vectors index‖ ^ 2 := by
    simpa only [Fintype.linearCombination_apply, mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _) coefficientNormBound 2
  have sumSquareBound : (∑ index, (coefficients index) ^ 2) ≤
      (Fintype.card Index : ℝ) * ‖coefficients‖ ^ 2 := by
    calc
      (∑ index, (coefficients index) ^ 2) ≤ ∑ index : Index, ‖coefficients‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro index _
        have pointBound := norm_le_pi_norm coefficients index
        simpa only [Real.norm_eq_abs, sq_abs] using
          pow_le_pow_left₀ (norm_nonneg _) pointBound 2
      _ = (Fintype.card Index : ℝ) * ‖coefficients‖ ^ 2 := by simp
  rw [gramQuadratic_inner_eq_norm_sq]
  have totalBound := sumSquareBound.trans
    (mul_le_mul_of_nonneg_left coefficientSquareBound (Nat.cast_nonneg _))
  have denominatorPositive : 0 < (Fintype.card Index : ℝ) * (inverseBound : ℝ) ^ 2 + 1 := by positivity
  rw [one_div_mul_eq_div, div_le_iff₀ denominatorPositive]
  nlinarith [sq_nonneg ‖∑ index, coefficients index • vectors index‖]

theorem gramQuadratic_sub (firstMatrix secondMatrix : Index → Index → ℝ)
    (coefficients : Index → ℝ) :
    gramQuadratic firstMatrix coefficients - gramQuadratic secondMatrix coefficients =
      gramQuadratic (fun first second => firstMatrix first second - secondMatrix first second)
        coefficients := by
  simp only [gramQuadratic, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

/-- A uniform entry error bounds the quadratic error for every coefficient vector. -/
theorem gramQuadratic_abs_le (matrix : Index → Index → ℝ) (entryBound : ℝ)
    (matrixBound : ∀ first second, |matrix first second| ≤ entryBound)
    (coefficients : Index → ℝ) :
    |gramQuadratic matrix coefficients| ≤ entryBound * (∑ index, |coefficients index|) ^ 2 := by
  unfold gramQuadratic
  calc
    |∑ first, ∑ second, coefficients first * matrix first second * coefficients second| ≤
        ∑ first, |∑ second, coefficients first * matrix first second * coefficients second| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ first, ∑ second, |coefficients first| * entryBound * |coefficients second| := by
      apply Finset.sum_le_sum
      intro first _
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
      intro second _
      simp only [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (matrixBound first second) (abs_nonneg _)) (abs_nonneg _)
    _ = entryBound * (∑ index, |coefficients index|) ^ 2 := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring

theorem gramQuadratic_error_le (firstMatrix secondMatrix : Index → Index → ℝ)
    (entryBound : ℝ) (entryBoundNonnegative : 0 ≤ entryBound)
    (matrixBound : ∀ first second, |firstMatrix first second - secondMatrix first second| ≤ entryBound)
    (coefficients : Index → ℝ) :
    |gramQuadratic firstMatrix coefficients - gramQuadratic secondMatrix coefficients| ≤
      entryBound * Fintype.card Index * ∑ index, (coefficients index) ^ 2 := by
  rw [gramQuadratic_sub]
  have sumBound := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := fun index => |coefficients index|)
  simp only [Finset.card_univ, sq_abs] at sumBound
  exact (gramQuadratic_abs_le _ entryBound matrixBound coefficients).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left sumBound entryBoundNonnegative)

/-- The elementary perturbation bound supplies stable coercivity. -/
theorem gramQuadratic_coercive_of_entry_bound
    (limitMatrix approximationMatrix : Index → Index → ℝ) (coercivity entryBound : ℝ)
    (entryBoundNonnegative : 0 ≤ entryBound)
    (limitLowerBound : ∀ coefficients,
      coercivity * (∑ index, (coefficients index) ^ 2) ≤ gramQuadratic limitMatrix coefficients)
    (entryErrorBound : ∀ first second,
      |approximationMatrix first second - limitMatrix first second| ≤ entryBound)
    (smallError : entryBound * Fintype.card Index ≤ coercivity / 2)
    (coefficients : Index → ℝ) :
    coercivity / 2 * (∑ index, (coefficients index) ^ 2) ≤
      gramQuadratic approximationMatrix coefficients := by
  have quadraticError := gramQuadratic_error_le approximationMatrix limitMatrix entryBound
    entryBoundNonnegative entryErrorBound coefficients
  have squareSumNonnegative : 0 ≤ ∑ index, (coefficients index) ^ 2 :=
    Finset.sum_nonneg fun index _ => sq_nonneg _
  have errorSmall := mul_le_mul_of_nonneg_right smallError squareSumNonnegative
  have differenceLower := (abs_le.mp quadraticError).1
  have limitingLower := limitLowerBound coefficients
  nlinarith

/-- Bounded norms of represented splines give bounded coefficients once the
approximating Gram matrix is coercive. -/
theorem coefficient_square_sum_le_of_gram_bound
    (matrix : Index → Index → ℝ) (coercivity normBound : ℝ) (coercivityPositive : 0 < coercivity)
    (matrixLowerBound : ∀ coefficients,
      coercivity / 2 * (∑ index, (coefficients index) ^ 2) ≤ gramQuadratic matrix coefficients)
    (coefficients : Index → ℝ) (representedNormBound : gramQuadratic matrix coefficients ≤ normBound) :
    (∑ index, (coefficients index) ^ 2) ≤ 2 * normBound / coercivity := by
  apply (le_div_iff₀ coercivityPositive).2
  nlinarith [matrixLowerBound coefficients]

/-- Entrywise convergence of a finite family gives a uniform eventual coercivity
bound, simultaneously for every coefficient vector. -/
theorem eventually_gramQuadratic_coercive
    (matrices : ℕ → Index → Index → ℝ) (limitMatrix : Index → Index → ℝ)
    (coercivity : ℝ) (coercivityPositive : 0 < coercivity)
    (matrixConvergence : ∀ first second,
      Tendsto (fun level => matrices level first second) atTop (𝓝 (limitMatrix first second)))
    (limitLowerBound : ∀ coefficients,
      coercivity * (∑ index, (coefficients index) ^ 2) ≤ gramQuadratic limitMatrix coefficients) :
    ∀ᶠ level in atTop, ∀ coefficients : Index → ℝ,
      coercivity / 2 * (∑ index, (coefficients index) ^ 2) ≤
        gramQuadratic (matrices level) coefficients := by
  have tolerancePositive : 0 < coercivity / (2 * (Fintype.card Index + 1 : ℝ)) := by positivity
  have entryErrors : ∀ᶠ level in atTop, ∀ first second,
      |matrices level first second - limitMatrix first second| ≤
        coercivity / (2 * (Fintype.card Index + 1 : ℝ)) := by
    apply Filter.eventually_all.2
    intro first
    apply Filter.eventually_all.2
    intro second
    have entryConvergence := Metric.tendsto_nhds.1 (matrixConvergence first second)
      _ tolerancePositive
    filter_upwards [entryConvergence] with level errorBound
    have absoluteError : |matrices level first second - limitMatrix first second| <
        coercivity / (2 * (Fintype.card Index + 1 : ℝ)) := by
      simpa only [Real.dist_eq] using errorBound
    exact absoluteError.le
  filter_upwards [entryErrors] with level errors coefficients
  apply gramQuadratic_coercive_of_entry_bound limitMatrix (matrices level) coercivity
    (coercivity / (2 * (Fintype.card Index + 1 : ℝ))) tolerancePositive.le
    limitLowerBound errors
  · have cardinalNonnegative : 0 ≤ (Fintype.card Index : ℝ) := Nat.cast_nonneg _
    have denominatorPositive : 0 < (2 * (Fintype.card Index + 1 : ℝ)) := by positivity
    have multiplyIdentity :
        coercivity / (2 * (Fintype.card Index + 1 : ℝ)) *
          (2 * (Fintype.card Index + 1 : ℝ)) = coercivity :=
      div_mul_cancel₀ _ (ne_of_gt denominatorPositive)
    nlinarith

end IGS.Sec31
