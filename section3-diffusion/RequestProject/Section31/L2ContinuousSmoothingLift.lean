import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Operator.Extend

/-! A Feller operator with an actual L² almost-everywhere bound extends to a
bounded map from L² into continuous functions. Full support supplies the sup
estimate; dense extension preserves the actual L² intertwining. -/

namespace IGS.Sec31

open MeasureTheory Filter Topology
noncomputable section

variable {Space : Type*} [TopologicalSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] (law : Measure Space) [IsFiniteMeasure law] [law.IsOpenPosMeasure]

theorem continuous_norm_le_of_ae_abs_le (values : C(Space, ℝ)) (bound : ℝ)
    (boundNonnegative : 0 ≤ bound) (boundAE : ∀ᵐ point ∂law, |values point| ≤ bound) :
    ‖values‖ ≤ bound := by
  have dense : Dense {point : Space | |values point| ≤ bound} := law.dense_of_ae boundAE
  have closed : IsClosed {point : Space | |values point| ≤ bound} :=
    isClosed_le values.continuous.abs continuous_const
  apply (ContinuousMap.norm_le _ boundNonnegative).mpr
  intro point
  have pointBound := dense point
  simpa only [closed.closure_eq, Set.mem_setOf_eq, Real.norm_eq_abs] using pointBound

theorem exists_L2_continuous_smoothing_lift
    (embedding : C(Space, ℝ) →L[ℝ] Lp ℝ 2 law)
    (embeddingDense : DenseRange embedding)
    (embeddingAE : ∀ values : C(Space, ℝ), (embedding values : Space → ℝ) =ᵐ[law] values)
    (continuousOperator : C(Space, ℝ) →L[ℝ] C(Space, ℝ))
    (l2Operator : Lp ℝ 2 law →L[ℝ] Lp ℝ 2 law)
    (intertwining : ∀ values : C(Space, ℝ),
      embedding (continuousOperator values) = l2Operator (embedding values))
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (l2Bound : ∀ values : Lp ℝ 2 law, ∀ᵐ point ∂law, |l2Operator values point| ≤ bound * ‖values‖) :
    ∃ lifted : Lp ℝ 2 law →L[ℝ] C(Space, ℝ), ‖lifted‖ ≤ bound ∧
      (∀ values : C(Space, ℝ), lifted (embedding values) = continuousOperator values) ∧
      ∀ values : Lp ℝ 2 law, embedding (lifted values) = l2Operator values := by
  have continuousBound : ∀ values : C(Space, ℝ), ‖continuousOperator values‖ ≤ bound * ‖embedding values‖ := by
    intro values
    apply continuous_norm_le_of_ae_abs_le law _ _ (mul_nonneg boundNonnegative (norm_nonneg _))
    have boundAE := l2Bound (embedding values)
    rw [← intertwining values] at boundAE
    filter_upwards [boundAE, embeddingAE (continuousOperator values)] with point bound representative
    rw [representative] at bound
    exact bound
  let lifted := continuousOperator.toLinearMap.extendOfNorm embedding.toLinearMap
  have liftedAgreement : ∀ values : C(Space, ℝ), lifted (embedding values) = continuousOperator values := by
    intro values
    exact LinearMap.extendOfNorm_eq embeddingDense ⟨bound, continuousBound⟩ values
  refine ⟨lifted, LinearMap.opNorm_extendOfNorm_le embeddingDense boundNonnegative continuousBound,
    liftedAgreement, ?_⟩
  have operatorEquality : (embedding.comp lifted : Lp ℝ 2 law → Lp ℝ 2 law) = l2Operator := by
    apply embeddingDense.equalizer (embedding.comp lifted).continuous l2Operator.continuous
    funext values
    change embedding (lifted (embedding values)) = l2Operator (embedding values)
    rw [liftedAgreement]
    exact intertwining values
  intro values
  exact congrFun operatorEquality values

end
end IGS.Sec31

#print axioms IGS.Sec31.continuous_norm_le_of_ae_abs_le
#print axioms IGS.Sec31.exists_L2_continuous_smoothing_lift
