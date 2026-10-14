import RequestProject.Section31.QuadraticEnergyCompletion

/-! A linear functional bounded by ambient norm and original energy extends
to the constructed closed energy domain. Every original two-scale estimate
passes to this same extension. This does not identify the extension with the
value of an arbitrary continuous representative at a specified point. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology UniformSpace
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem exists_closed_energy_functional
    (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values)
    (closable : SequentiallyClosable domain form)
    (evaluation : domain →ₗ[ℝ] ℝ) (normConstant energyConstant : ℝ)
    (normConstantNonnegative : 0 ≤ normConstant)
    (energyConstantNonnegative : 0 ≤ energyConstant)
    (originalBound : ∀ values : domain,
      evaluation values ^ 2 ≤ normConstant * ‖(values : H)‖ ^ 2 + energyConstant * form values) :
    ∃ extension : closedDomain domain form nonnegative →ₗ[ℝ] ℝ,
      (∀ values : domain,
        extension ⟨(values : H), original_mem_closedDomain domain form nonnegative values⟩ =
          evaluation values) ∧
      ∀ (firstConstant secondConstant : ℝ),
        (∀ values : domain, evaluation values ^ 2 ≤
          firstConstant * ‖(values : H)‖ ^ 2 + secondConstant * form values) →
        ∀ target : closedDomain domain form nonnegative,
          extension target ^ 2 ≤ firstConstant * ‖(target : H)‖ ^ 2 +
            secondConstant * closedForm domain form nonnegative closable target := by
  have normBound : ∀ values : QuadraticEnergySpace domain form nonnegative,
      ‖evaluation values.value‖ ≤ Real.sqrt (normConstant + energyConstant) * ‖values‖ := by
    intro values
    have pointBound := originalBound values.value
    have energyNonnegative := nonnegative values.value
    have normIdentity := norm_sq domain form nonnegative values
    have squaredBound : evaluation values.value ^ 2 ≤
        (normConstant + energyConstant) * ‖values‖ ^ 2 := by
      rw [normIdentity]
      nlinarith [mul_nonneg normConstantNonnegative energyNonnegative,
        mul_nonneg energyConstantNonnegative (sq_nonneg ‖(values.value : H)‖)]
    have squareRootIdentity := Real.sq_sqrt (add_nonneg normConstantNonnegative energyConstantNonnegative)
    have rightNonnegative := mul_nonneg (Real.sqrt_nonneg (normConstant + energyConstant)) (norm_nonneg values)
    have rightSquare : (Real.sqrt (normConstant + energyConstant) * ‖values‖) ^ 2 =
        (normConstant + energyConstant) * ‖values‖ ^ 2 := by
      rw [mul_pow, squareRootIdentity]
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (evaluation values.value), abs_nonneg (evaluation values.value)]
  let onEnergy : QuadraticEnergySpace domain form nonnegative →L[ℝ] ℝ :=
    (evaluation.comp (linearEquivDomain domain form nonnegative).toLinearMap).mkContinuous
      (Real.sqrt (normConstant + energyConstant)) normBound
  let onCompletion : Completion (QuadraticEnergySpace domain form nonnegative) →L[ℝ] ℝ :=
    onEnergy.extend Completion.toComplL
  have completionAgreement (values : QuadraticEnergySpace domain form nonnegative) :
      onCompletion (values : Completion (QuadraticEnergySpace domain form nonnegative)) =
        evaluation values.value := by
    exact ContinuousLinearMap.extend_eq onEnergy Completion.denseRange_coe
      (Completion.isUniformInducing_coe _) values
  let extension : closedDomain domain form nonnegative →ₗ[ℝ] ℝ :=
    onCompletion.toLinearMap.comp (closedDomainEquiv domain form nonnegative closable).symm.toLinearMap
  refine ⟨extension, ?_, ?_⟩
  · intro values
    have inverseValue : (closedDomainEquiv domain form nonnegative closable).symm
        ⟨(values : H), original_mem_closedDomain domain form nonnegative values⟩ =
      ((⟨values⟩ : QuadraticEnergySpace domain form nonnegative) :
        Completion (QuadraticEnergySpace domain form nonnegative)) := by
      apply completionMap_injective domain form nonnegative closable
      rw [completionMap_coe]
      exact congrArg Subtype.val
        ((closedDomainEquiv domain form nonnegative closable).apply_symm_apply _)
    change onCompletion ((closedDomainEquiv domain form nonnegative closable).symm
      ⟨(values : H), original_mem_closedDomain domain form nonnegative values⟩) = evaluation values
    rw [inverseValue]
    exact completionAgreement ⟨values⟩
  · intro firstConstant secondConstant bound target
    have completionBound : ∀ point : Completion (QuadraticEnergySpace domain form nonnegative),
        onCompletion point ^ 2 ≤ firstConstant * ‖completionMap domain form nonnegative point‖ ^ 2 +
          secondConstant * (‖point‖ ^ 2 - ‖completionMap domain form nonnegative point‖ ^ 2) := by
      intro point
      induction point using Completion.induction_on with
      | hp => exact isClosed_le (by fun_prop) (by fun_prop)
      | ih values =>
          rw [completionAgreement, completionMap_coe, Completion.norm_coe, norm_sq, add_sub_cancel_right]
          exact bound values.value
    have imageEquality := congrArg Subtype.val
      ((closedDomainEquiv domain form nonnegative closable).apply_symm_apply target)
    change completionMap domain form nonnegative
      ((closedDomainEquiv domain form nonnegative closable).symm target) = (target : H) at imageEquality
    change onCompletion ((closedDomainEquiv domain form nonnegative closable).symm target) ^ 2 ≤
      firstConstant * ‖(target : H)‖ ^ 2 + secondConstant * closedForm domain form nonnegative closable target
    rw [closedForm_value]
    simpa only [imageEquality] using
      completionBound ((closedDomainEquiv domain form nonnegative closable).symm target)

end
end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.exists_closed_energy_functional
