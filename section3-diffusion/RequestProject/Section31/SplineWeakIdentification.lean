import RequestProject.Section31.GramCoercivity
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Identification of finite spline limits in genuine varying Hilbert spaces.

The spaces at different levels can have different types. All convergence inputs
are scalar inner products and coefficients; no arbitrary predicate called weak
convergence, or assumed identification of its limit, is used here. Application
to the paper still requires its concrete L² spline and measure convergence.
-/

namespace IGS.Sec31

open Filter Topology
open scoped BigOperators

variable {Index Hilbert : Type*} [Fintype Index]
  [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
  {LevelHilbert : ℕ → Type*}
  [∀ level, NormedAddCommGroup (LevelHilbert level)]
  [∀ level, InnerProductSpace ℝ (LevelHilbert level)]

noncomputable def finiteSplineProjection (vectors : Index → Hilbert)
    (function : Hilbert) : Hilbert := by
  letI := FiniteDimensional.span_of_finite ℝ (Set.finite_range vectors)
  exact (Submodule.span ℝ (Set.range vectors)).starProjection function

theorem varying_linearCombination_pairing_tendsto
    (levelVectors : ∀ level, Index → LevelHilbert level)
    (vectors : Index → Hilbert) (coefficients : ℕ → Index → ℝ)
    (limitCoefficients : Index → ℝ)
    (coefficientConvergence : ∀ index,
      Tendsto (fun level => coefficients level index) atTop (𝓝 (limitCoefficients index)))
    (gramConvergence : ∀ first second,
      Tendsto (fun level => inner ℝ (levelVectors level first) (levelVectors level second))
        atTop (𝓝 (inner ℝ (vectors first) (vectors second)))) (index : Index) :
    Tendsto (fun level => inner ℝ
      (∑ first, coefficients level first • levelVectors level first) (levelVectors level index))
      atTop (𝓝 (inner ℝ (∑ first, limitCoefficients first • vectors first) (vectors index))) := by
  simpa only [sum_inner, real_inner_smul_left] using
    tendsto_finset_sum Finset.univ (fun first _ =>
      (coefficientConvergence first).mul (gramConvergence first index))

theorem varying_linearCombination_norm_sq_tendsto
    (levelVectors : ∀ level, Index → LevelHilbert level)
    (vectors : Index → Hilbert) (coefficients : ℕ → Index → ℝ)
    (limitCoefficients : Index → ℝ)
    (coefficientConvergence : ∀ index,
      Tendsto (fun level => coefficients level index) atTop (𝓝 (limitCoefficients index)))
    (gramConvergence : ∀ first second,
      Tendsto (fun level => inner ℝ (levelVectors level first) (levelVectors level second))
        atTop (𝓝 (inner ℝ (vectors first) (vectors second)))) :
    Tendsto (fun level => ‖∑ first, coefficients level first • levelVectors level first‖ ^ 2)
      atTop (𝓝 (‖∑ first, limitCoefficients first • vectors first‖ ^ 2)) := by
  simp_rw [← gramQuadratic_inner_eq_norm_sq]
  exact tendsto_finset_sum Finset.univ (fun first _ =>
    tendsto_finset_sum Finset.univ (fun second _ =>
      ((coefficientConvergence first).mul (gramConvergence first second)).mul
        (coefficientConvergence second)))

theorem finiteSplineProjection_eq_of_basis_pairings
    (vectors : Index → Hilbert) (function : Hilbert) (coefficients : Index → ℝ)
    (pairings : ∀ index,
      inner ℝ (∑ first, coefficients first • vectors first) (vectors index) =
        inner ℝ function (vectors index)) :
    finiteSplineProjection vectors function = ∑ first, coefficients first • vectors first := by
  letI := FiniteDimensional.span_of_finite ℝ (Set.finite_range vectors)
  change (Submodule.span ℝ (Set.range vectors)).starProjection function = _
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.sum_mem _ (fun index _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self index)))
  · intro test test_mem
    induction test_mem using Submodule.span_induction with
    | mem test test_mem =>
        obtain ⟨index, rfl⟩ := test_mem
        simp only [inner_sub_left, pairings index, sub_self]
    | zero => simp
    | add first second _ _ first_orthogonal second_orthogonal =>
        simp only [inner_add_right, first_orthogonal, second_orthogonal, add_zero]
    | smul scalar test _ orthogonal =>
        simp only [inner_smul_right, orthogonal, mul_zero]

theorem varying_projection_limit_identified
    (levelVectors : ∀ level, Index → LevelHilbert level)
    (vectors : Index → Hilbert) (functions : ∀ level, LevelHilbert level)
    (function : Hilbert) (coefficients : ℕ → Index → ℝ)
    (limitCoefficients : Index → ℝ)
    (coefficientConvergence : ∀ index,
      Tendsto (fun level => coefficients level index) atTop (𝓝 (limitCoefficients index)))
    (gramConvergence : ∀ first second,
      Tendsto (fun level => inner ℝ (levelVectors level first) (levelVectors level second))
        atTop (𝓝 (inner ℝ (vectors first) (vectors second))))
    (weakPairings : ∀ index,
      Tendsto (fun level => inner ℝ (functions level) (levelVectors level index))
        atTop (𝓝 (inner ℝ function (vectors index))))
    (normalEquations : ∀ level index,
      inner ℝ (∑ first, coefficients level first • levelVectors level first)
        (levelVectors level index) = inner ℝ (functions level) (levelVectors level index)) :
    finiteSplineProjection vectors function = ∑ first, limitCoefficients first • vectors first := by
  apply finiteSplineProjection_eq_of_basis_pairings
  intro index
  apply tendsto_nhds_unique
    (varying_linearCombination_pairing_tendsto levelVectors vectors coefficients
      limitCoefficients coefficientConvergence gramConvergence index)
  exact (weakPairings index).congr' (Filter.Eventually.of_forall
    (fun level => (normalEquations level index).symm))

end IGS.Sec31
