import RequestProject.Section31.VaryingHilbert
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! A genuine varying L² core constructed from weakly convergent measures.

The spaces are actual mathlib Lp spaces, not a common abstract type. The core
maps send a bounded continuous function to its equivalence class in each L²
space. Density comes from regular Borel measure approximation, and norm
consistency is proved by weak convergence applied to the square of the same
continuous function. The EIGS compact metric completion and weak convergence
of its pushed-forward speed measures remain concrete geometric obligations.
-/

namespace IGS.Sec31

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

theorem boundedContinuous_L2_inner_tendsto
    (measures : ℕ → ProbabilityMeasure Space) (measure : ProbabilityMeasure Space)
    (weak_convergence : Tendsto measures atTop (𝓝 measure))
    (first second : Space →ᵇ ℝ) :
    Tendsto (fun level => inner ℝ
      (BoundedContinuousFunction.toLp 2 (measures level : Measure Space) ℝ first)
      (BoundedContinuousFunction.toLp 2 (measures level : Measure Space) ℝ second))
      atTop (𝓝 (inner ℝ
        (BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ first)
        (BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ second))) := by
  have integral_convergence :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp weak_convergence (second * first)
  simpa only [BoundedContinuousFunction.inner_toLp, conj_trivial,
    BoundedContinuousFunction.mul_apply] using integral_convergence

theorem boundedContinuous_L2_norm_sq_tendsto
    (measures : ℕ → ProbabilityMeasure Space) (measure : ProbabilityMeasure Space)
    (weak_convergence : Tendsto measures atTop (𝓝 measure))
    (function : Space →ᵇ ℝ) :
    Tendsto (fun level =>
      ‖BoundedContinuousFunction.toLp 2 (measures level : Measure Space) ℝ function‖ ^ 2)
      atTop (𝓝 (‖BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ function‖ ^ 2)) := by
  simpa only [real_inner_self_eq_norm_sq] using
    boundedContinuous_L2_inner_tendsto measures measure weak_convergence function function

theorem boundedContinuous_L2_norm_tendsto
    (measures : ℕ → ProbabilityMeasure Space) (measure : ProbabilityMeasure Space)
    (weak_convergence : Tendsto measures atTop (𝓝 measure))
    (function : Space →ᵇ ℝ) :
    Tendsto (fun level =>
      ‖BoundedContinuousFunction.toLp 2 (measures level : Measure Space) ℝ function‖)
      atTop (𝓝 (‖BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ function‖)) := by
  have squares_converge :=
    boundedContinuous_L2_norm_sq_tendsto measures measure weak_convergence function
  have sqrt_converges := Real.continuous_sqrt.continuousAt.tendsto.comp squares_converge
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm] using sqrt_converges

/-- Density and norm consistency are proved for actual L² equivalence classes. -/
noncomputable def probabilityL2Core
    (measures : ℕ → ProbabilityMeasure Space) (measure : ProbabilityMeasure Space)
    (weak_convergence : Tendsto measures atTop (𝓝 measure)) :
    VaryingHilbertCore (Space →ᵇ ℝ) (Lp ℝ 2 (measure : Measure Space))
      (fun level => Lp ℝ 2 (measures level : Measure Space)) where
  embed := (BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ).toLinearMap
  restrict := fun level =>
    (BoundedContinuousFunction.toLp 2 (measures level : Measure Space) ℝ).toLinearMap
  dense := BoundedContinuousFunction.toLp_denseRange ℝ (measure : Measure Space) ℝ (by norm_num)
  norm_converges := boundedContinuous_L2_norm_tendsto measures measure weak_convergence

theorem probabilityL2Core_restrictions_strong
    (measures : ℕ → ProbabilityMeasure Space) (measure : ProbabilityMeasure Space)
    (weak_convergence : Tendsto measures atTop (𝓝 measure)) (function : Space →ᵇ ℝ) :
    (probabilityL2Core measures measure weak_convergence).Strong
      (fun level => BoundedContinuousFunction.toLp 2 (measures level : Measure Space) ℝ function)
      (BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ function) :=
  (probabilityL2Core measures measure weak_convergence).strong_restrict function

end IGS.Sec31
