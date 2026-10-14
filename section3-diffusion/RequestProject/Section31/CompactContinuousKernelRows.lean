import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.ContinuousMap.Compact

/-! A compact operator into continuous functions has norm-continuous
evaluation functionals. Riesz representation gives continuous Hilbert-space
kernel rows. Compactness is a hypothesis of this generic lemma and must be
proved separately for any actual semigroup consumer. -/

namespace IGS.Sec31

open Filter Topology
noncomputable section

variable {Space Input : Type*} [MetricSpace Space] [CompactSpace Space]
    [NormedAddCommGroup Input] [NormedSpace ℝ Input]

def continuousOperatorRowFunctional (operator : Input →L[ℝ] C(Space, ℝ))
    (point : Space) : StrongDual ℝ Input :=
  (ContinuousMap.evalCLM ℝ point).comp operator

theorem continuousOperatorRowFunctional_continuous
    (operator : Input →L[ℝ] C(Space, ℝ))
    (operatorCompact : IsCompactOperator operator) :
    Continuous (continuousOperatorRowFunctional operator) := by
  obtain ⟨compactImage, imageCompact, imageSubset⟩ :=
    IsCompactOperator.image_closedBall_subset_compact
      (f := operator.toLinearMap) operatorCompact 1
  letI : CompactSpace compactImage := isCompact_iff_compactSpace.mp imageCompact
  let evaluationFamily : Space → C(compactImage, ℝ) := fun point =>
    ⟨fun function => function.val point,
      (continuous_eval_const point).comp continuous_subtype_val⟩
  have evaluationFamilyContinuous : Continuous evaluationFamily := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_eval.comp
      ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)
  have differenceBound (first second : Space) :
      ‖continuousOperatorRowFunctional operator first - continuousOperatorRowFunctional operator second‖ ≤
        ‖evaluationFamily first - evaluationFamily second‖ := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _)
    intro values valuesUnit
    have imageMembership : operator values ∈ compactImage := by
      apply imageSubset
      refine ⟨values, ?_, rfl⟩
      simpa only [Metric.mem_closedBall, dist_zero_right, valuesUnit] using (le_refl (1 : ℝ))
    change ‖operator values first - operator values second‖ ≤ _
    exact (evaluationFamily first - evaluationFamily second).norm_coe_le_norm
      ⟨operator values, imageMembership⟩
  rw [continuous_iff_continuousAt]
  intro point
  apply Metric.continuousAt_iff.mpr
  intro error errorPositive
  obtain ⟨radius, radiusPositive, withinRadius⟩ :=
    Metric.continuousAt_iff.mp evaluationFamilyContinuous.continuousAt error errorPositive
  refine ⟨radius, radiusPositive, ?_⟩
  intro nearby nearbyClose
  have familyClose := withinRadius nearbyClose
  rw [dist_eq_norm] at familyClose ⊢
  exact (differenceBound nearby point).trans_lt familyClose

variable {Hilbert : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    [CompleteSpace Hilbert]

def continuousOperatorKernelRow (operator : Hilbert →L[ℝ] C(Space, ℝ))
    (point : Space) : Hilbert :=
  (InnerProductSpace.toDual ℝ Hilbert).symm (continuousOperatorRowFunctional operator point)

theorem continuousOperatorKernelRow_continuous
    (operator : Hilbert →L[ℝ] C(Space, ℝ))
    (operatorCompact : IsCompactOperator operator) :
    Continuous (continuousOperatorKernelRow operator) :=
  (InnerProductSpace.toDual ℝ Hilbert).symm.continuous.comp
    (continuousOperatorRowFunctional_continuous operator operatorCompact)

theorem continuousOperatorKernelRow_represents
    (operator : Hilbert →L[ℝ] C(Space, ℝ)) (point : Space) (values : Hilbert) :
    operator values point = inner ℝ (continuousOperatorKernelRow operator point) values := by
  exact (InnerProductSpace.toDual_symm_apply (x := values)
    (y := continuousOperatorRowFunctional operator point)).symm

theorem continuousOperatorKernelRow_inner_continuous
    (operator : Hilbert →L[ℝ] C(Space, ℝ))
    (operatorCompact : IsCompactOperator operator) :
    Continuous (fun points : Space × Space =>
      inner ℝ (continuousOperatorKernelRow operator points.1)
        (continuousOperatorKernelRow operator points.2)) :=
  ((continuousOperatorKernelRow_continuous operator operatorCompact).comp continuous_fst).inner
    ((continuousOperatorKernelRow_continuous operator operatorCompact).comp continuous_snd)

end
end IGS.Sec31

#print axioms IGS.Sec31.continuousOperatorRowFunctional_continuous
#print axioms IGS.Sec31.continuousOperatorKernelRow_continuous
#print axioms IGS.Sec31.continuousOperatorKernelRow_represents
#print axioms IGS.Sec31.continuousOperatorKernelRow_inner_continuous
