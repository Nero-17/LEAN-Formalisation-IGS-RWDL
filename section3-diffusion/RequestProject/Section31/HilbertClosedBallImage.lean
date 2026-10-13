import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Tactic

/-! Bounded Hilbert lifts of ambient limits, proved from Riesz representation
and Banach--Alaoglu. No weak subsequence or closed-range assumption is used. -/

namespace IGS.Sec31

open Filter Topology Metric

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem hilbert_image_closedBall_isClosed (operator : E →L[ℝ] H) (radius : ℝ) :
    IsClosed (operator '' closedBall 0 radius) := by
  classical
  let weakRiesz : H → WeakDual ℝ H := fun point => StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H point)
  let weakOperator : WeakDual ℝ E → WeakDual ℝ H := fun functional =>
    StrongDual.toWeakDual ((WeakDual.toStrongDual functional).comp operator.adjoint)
  have weakOperatorContinuous : Continuous weakOperator := by
    apply WeakDual.continuous_of_continuous_eval
    intro point
    exact WeakDual.eval_continuous (operator.adjoint point)
  have weakRieszContinuous : Continuous weakRiesz :=
    NormedSpace.Dual.toWeakDual_continuous.comp (InnerProductSpace.toDual ℝ H).continuous
  have weakRieszInjective : Function.Injective weakRiesz :=
    StrongDual.toWeakDual.injective.comp (InnerProductSpace.toDual ℝ H).injective
  have imageAgreement (point : E) :
      weakOperator (StrongDual.toWeakDual (InnerProductSpace.toDual ℝ E point)) =
        weakRiesz (operator point) := by
    apply DFunLike.ext
    intro test
    exact operator.adjoint_inner_right point test
  have imageEquality :
      weakOperator '' (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E) radius) =
        weakRiesz '' (operator '' closedBall 0 radius) := by
    ext functional
    constructor
    · rintro ⟨dual, dualBound, rfl⟩
      let point := (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual dual)
      have pointBound : point ∈ closedBall (0 : E) radius := by
        simpa only [Set.mem_preimage, mem_closedBall, dist_zero_right, point,
          LinearIsometryEquiv.norm_map] using dualBound
      refine ⟨operator point, ⟨point, pointBound, rfl⟩, ?_⟩
      have equality : StrongDual.toWeakDual (InnerProductSpace.toDual ℝ E point) = dual := by
        simp [point]
      rw [← equality, imageAgreement]
    · rintro ⟨_, ⟨point, pointBound, rfl⟩, rfl⟩
      refine ⟨StrongDual.toWeakDual (InnerProductSpace.toDual ℝ E point), ?_, imageAgreement point⟩
      simpa only [Set.mem_preimage, WeakDual.toStrongDual, LinearEquiv.symm_apply_apply,
        mem_closedBall, dist_zero_right,
        LinearIsometryEquiv.norm_map] using pointBound
  have compactImage := (WeakDual.isCompact_closedBall ℝ (0 : StrongDual ℝ E) radius).image
    weakOperatorContinuous
  rw [imageEquality] at compactImage
  have preimageEquality : weakRiesz ⁻¹' (weakRiesz '' (operator '' closedBall 0 radius)) =
      operator '' closedBall 0 radius := Set.preimage_image_eq _ weakRieszInjective
  rw [← preimageEquality]
  exact compactImage.isClosed.preimage weakRieszContinuous

theorem hilbert_exists_bounded_lift_of_tendsto (operator : E →L[ℝ] H)
    (sequence : ℕ → E) (target : H) (radius : ℝ)
    (ambientLimit : Tendsto (fun index => operator (sequence index)) atTop (nhds target))
    (eventualBound : ∀ᶠ index in atTop, ‖sequence index‖ ≤ radius) :
    ∃ lift : E, operator lift = target ∧ ‖lift‖ ≤ radius := by
  have membership : target ∈ operator '' closedBall 0 radius :=
    (hilbert_image_closedBall_isClosed operator radius).mem_of_tendsto ambientLimit
      (eventualBound.mono fun index bound =>
        ⟨sequence index, by simpa only [mem_closedBall, dist_zero_right] using bound, rfl⟩)
  obtain ⟨lift, liftBound, liftImage⟩ := membership
  exact ⟨lift, liftImage, by simpa only [mem_closedBall, dist_zero_right] using liftBound⟩

theorem hilbert_exists_lift_of_eventual_approximate_norm_bound (operator : E →L[ℝ] H)
    (injective : Function.Injective operator) (sequence : ℕ → E) (target : H) (radius : ℝ)
    (ambientLimit : Tendsto (fun index => operator (sequence index)) atTop (nhds target))
    (eventualBound : ∀ bound > radius, ∀ᶠ index in atTop, ‖sequence index‖ ≤ bound) :
    ∃ lift : E, operator lift = target ∧ ‖lift‖ ≤ radius := by
  obtain ⟨lift, liftImage, _⟩ := hilbert_exists_bounded_lift_of_tendsto operator sequence target
    (radius + 1) ambientLimit (eventualBound _ (by linarith))
  refine ⟨lift, liftImage, le_of_forall_gt_imp_ge_of_dense fun bound boundGreater => ?_⟩
  obtain ⟨other, otherImage, otherBound⟩ := hilbert_exists_bounded_lift_of_tendsto operator sequence target
    bound ambientLimit (eventualBound bound boundGreater)
  have same : lift = other := injective (liftImage.trans otherImage.symm)
  simpa only [same] using otherBound

end IGS.Sec31

#print axioms IGS.Sec31.hilbert_image_closedBall_isClosed
#print axioms IGS.Sec31.hilbert_exists_bounded_lift_of_tendsto
#print axioms IGS.Sec31.hilbert_exists_lift_of_eventual_approximate_norm_bound
