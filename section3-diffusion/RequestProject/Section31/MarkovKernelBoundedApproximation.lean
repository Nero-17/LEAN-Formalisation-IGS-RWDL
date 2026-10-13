import RequestProject.Section31.MarkovKernelBoundedExtension
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! Uniformly bounded continuous approximations of bounded real L2 inputs.
Clipping preserves the L2 limit because its actual action on L2 is continuous
and fixes an input with the prescribed almost-everywhere bound. The resulting
kernel integral representation uses only the proved continuous representation,
Markov property and measure invariance. -/

namespace IGS.Sec31.CountableMarkov

open MeasureTheory ProbabilityTheory Filter Topology

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X]

def clipContinuous (bound : ℝ) (values : C(X, ℝ)) : C(X, ℝ) :=
  ⟨fun point => min (max (values point) (-bound)) bound,
    (values.continuous.max continuous_const).min continuous_const⟩

theorem clipContinuous_bound (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (values : C(X, ℝ)) (point : X) :
    ‖clipContinuous bound values point‖ ≤ bound := by
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  exact ⟨le_min (le_max_right _ _) (by linarith), min_le_right _ _⟩

variable (measure : Measure X) [IsFiniteMeasure measure]

theorem exists_bounded_continuous_L2_approximation
    (forcing : Lp ℝ 2 measure) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (forcingBounded : ∀ᵐ point ∂measure, ‖forcing point‖ ≤ bound) :
    ∃ sequence : ℕ → C(X, ℝ),
      (∀ index point, ‖sequence index point‖ ≤ bound) ∧
      Tendsto (fun index => ContinuousMap.toLp 2 measure ℝ (sequence index))
        atTop (nhds forcing) := by
  classical
  have dense : DenseRange (ContinuousMap.toLp 2 measure ℝ :
      C(X, ℝ) →L[ℝ] Lp ℝ 2 measure) :=
    ContinuousMap.toLp_denseRange ℝ measure ℝ (by norm_num)
  obtain ⟨approximation, approximationMem, approximationLimit⟩ :=
    mem_closure_iff_seq_limit.mp (dense forcing)
  choose sequence sequenceEquality using approximationMem
  have lipschitz : LipschitzWith 1 (fun value : ℝ => min (max value (-bound)) bound) :=
    (LipschitzWith.id.max_const (-bound)).min_const bound
  have zero : min (max (0 : ℝ) (-bound)) bound = 0 := by
    rw [max_eq_left (by linarith), min_eq_left boundNonnegative]
  have fixed : lipschitz.compLp zero forcing = forcing := by
    apply Lp.ext
    filter_upwards [lipschitz.coeFn_compLp zero forcing, forcingBounded]
      with point evaluation pointBound
    have bounds : -bound ≤ forcing point ∧ forcing point ≤ bound := by
      simpa only [Real.norm_eq_abs, abs_le] using pointBound
    simpa only [Function.comp_apply, max_eq_left bounds.1, min_eq_left bounds.2]
      using evaluation
  have clippedEquality (index : ℕ) :
      ContinuousMap.toLp 2 measure ℝ (clipContinuous bound (sequence index)) =
        lipschitz.compLp zero (approximation index) := by
    rw [← sequenceEquality index]
    apply Lp.ext
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) measure
      (clipContinuous bound (sequence index)),
      lipschitz.coeFn_compLp zero (ContinuousMap.toLp 2 measure ℝ (sequence index)),
      ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) measure (sequence index)]
      with point clippedEvaluation compositionEvaluation inputEvaluation
    simp only [Function.comp_apply] at compositionEvaluation
    rw [clippedEvaluation, compositionEvaluation, inputEvaluation]
    rfl
  refine ⟨fun index => clipContinuous bound (sequence index),
    fun index point => clipContinuous_bound bound boundNonnegative (sequence index) point, ?_⟩
  have clippedLimit := ((lipschitz.continuous_compLp zero).tendsto forcing).comp approximationLimit
  simpa only [clippedEquality, fixed] using clippedLimit

theorem ae_kernel_integral_of_bounded_L2
    (semigroup : Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (kernel : Kernel X X) [IsMarkovKernel kernel] (invariant : kernel.Invariant measure)
    (representation : ∀ values : C(X, ℝ), ∀ᵐ point ∂measure,
      (∫ location, values location ∂kernel point) =
        semigroup (ContinuousMap.toLp 2 measure ℝ values) point)
    (forcing : Lp ℝ 2 measure) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (forcingBounded : ∀ᵐ point ∂measure, ‖forcing point‖ ≤ bound) :
    ∀ᵐ point ∂measure,
      (∫ location, forcing location ∂kernel point) = semigroup forcing point := by
  obtain ⟨sequence, bounded, approximationLimit⟩ :=
    exists_bounded_continuous_L2_approximation measure forcing bound boundNonnegative forcingBounded
  exact ae_kernel_integral_of_bounded_continuous_L2_approximation measure semigroup kernel
    invariant representation sequence forcing bound bounded approximationLimit

end IGS.Sec31.CountableMarkov

#print axioms IGS.Sec31.CountableMarkov.clipContinuous_bound
#print axioms IGS.Sec31.CountableMarkov.exists_bounded_continuous_L2_approximation
#print axioms IGS.Sec31.CountableMarkov.ae_kernel_integral_of_bounded_L2
