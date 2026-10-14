import RequestProject.Section31.CompactContinuousKernelRows
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Composing a continuous L² lift with its self-adjoint L² operator gives
the integral kernel formed by inner products of Riesz rows. Compactness is
needed only for the separate joint-continuity assertion, and is not supplied
as an unproved conclusion about an actual semigroup. -/

namespace IGS.Sec31

open MeasureTheory Filter Topology
noncomputable section

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] (law : Measure Space) [IsFiniteMeasure law]

def continuousOperatorComposedKernel (operator : Lp ℝ 2 law →L[ℝ] C(Space, ℝ))
    (first second : Space) : ℝ :=
  inner ℝ (continuousOperatorKernelRow operator first) (continuousOperatorKernelRow operator second)

theorem continuousOperatorComposedKernel_symmetric
    (operator : Lp ℝ 2 law →L[ℝ] C(Space, ℝ)) (first second : Space) :
    continuousOperatorComposedKernel law operator first second =
      continuousOperatorComposedKernel law operator second first :=
  real_inner_comm _ _

theorem continuousOperatorComposedKernel_continuous
    (operator : Lp ℝ 2 law →L[ℝ] C(Space, ℝ))
    (operatorCompact : IsCompactOperator operator) :
    Continuous (fun points : Space × Space =>
      continuousOperatorComposedKernel law operator points.1 points.2) :=
  continuousOperatorKernelRow_inner_continuous operator operatorCompact

theorem continuousOperatorComposedKernel_integral
    (embedding : C(Space, ℝ) →L[ℝ] Lp ℝ 2 law)
    (embeddingAE : ∀ function : C(Space, ℝ), (embedding function : Space → ℝ) =ᵐ[law] function)
    (operator : Lp ℝ 2 law →L[ℝ] C(Space, ℝ))
    (l2Operator : Lp ℝ 2 law →L[ℝ] Lp ℝ 2 law)
    (operatorSelfAdjoint : IsSelfAdjoint l2Operator)
    (compatibility : ∀ values : Lp ℝ 2 law, embedding (operator values) = l2Operator values)
    (point : Space) (values : Lp ℝ 2 law) :
    operator (l2Operator values) point =
      ∫ other, continuousOperatorComposedKernel law operator point other * values other ∂law := by
  calc
    _ = inner ℝ (continuousOperatorKernelRow operator point) (l2Operator values) :=
      continuousOperatorKernelRow_represents operator point (l2Operator values)
    _ = inner ℝ (l2Operator (continuousOperatorKernelRow operator point)) values :=
      (operatorSelfAdjoint.isSymmetric _ _).symm
    _ = inner ℝ (embedding (operator (continuousOperatorKernelRow operator point))) values := by
      rw [compatibility]
    _ = ∫ other, continuousOperatorComposedKernel law operator point other * values other ∂law := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [embeddingAE (operator (continuousOperatorKernelRow operator point))]
        with other representative
      rw [representative, continuousOperatorKernelRow_represents]
      simp only [continuousOperatorComposedKernel, RCLike.inner_apply, conj_trivial]
      rw [real_inner_comm (continuousOperatorKernelRow operator other)
        (continuousOperatorKernelRow operator point), mul_comm]

end
end IGS.Sec31

#print axioms IGS.Sec31.continuousOperatorComposedKernel_symmetric
#print axioms IGS.Sec31.continuousOperatorComposedKernel_continuous
#print axioms IGS.Sec31.continuousOperatorComposedKernel_integral
