import RequestProject.Section31.HilbertClosedBallImage
import RequestProject.Section31.QuadraticEnergyClosureRecovery
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! Positivity of point functionals on an energy completion. The essential
step is not assumed: bounded lifts with nonnegative functional values retain
that sign at an ambient limit, by compact scalar subsequences and the closed
image of a Hilbert ball. These are generic helpers, not a locality theorem. -/

namespace IGS.Sec31

open Filter Topology Metric UniformSpace

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem hilbert_functional_nonnegative_of_bounded_lifts
    (operator : E →L[ℝ] H) (injective : Function.Injective operator)
    (functional : E →L[ℝ] ℝ) (sequence : ℕ → E) (target : E)
    (radius : ℝ) (bounded : ∀ index, ‖sequence index‖ ≤ radius)
    (ambientLimit : Tendsto (fun index => operator (sequence index)) atTop (nhds (operator target)))
    (nonnegative : ∀ index, 0 ≤ functional (sequence index)) :
    0 ≤ functional target := by
  classical
  have scalarBound : ∀ index, functional (sequence index) ∈ closedBall (0 : ℝ) (‖functional‖ * radius) := by
    intro index
    simpa only [mem_closedBall, dist_zero_right] using
      (functional.le_opNorm (sequence index)).trans (mul_le_mul_of_nonneg_left (bounded index) (norm_nonneg functional))
  obtain ⟨limit, _, selection, selectionStrict, scalarLimit⟩ :=
    (isCompact_closedBall (0 : ℝ) (‖functional‖ * radius)).tendsto_subseq scalarBound
  let combined : E →L[ℝ] WithLp 2 (H × ℝ) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ H ℝ).symm.toContinuousLinearMap.comp (operator.prod functional)
  have combinedLimit : Tendsto (fun index => combined (sequence (selection index))) atTop
      (nhds ((WithLp.prodContinuousLinearEquiv 2 ℝ H ℝ).symm (operator target, limit))) := by
    exact (WithLp.prodContinuousLinearEquiv 2 ℝ H ℝ).symm.continuous.continuousAt.tendsto.comp
      ((ambientLimit.comp selectionStrict.tendsto_atTop).prodMk_nhds scalarLimit)
  obtain ⟨lift, liftImage, _⟩ := hilbert_exists_bounded_lift_of_tendsto combined
    (fun index => sequence (selection index))
    ((WithLp.prodContinuousLinearEquiv 2 ℝ H ℝ).symm (operator target, limit)) radius
    combinedLimit (Eventually.of_forall fun index => bounded (selection index))
  have pairEquality : (operator lift, functional lift) = (operator target, limit) := by
    exact (WithLp.prodContinuousLinearEquiv 2 ℝ H ℝ).symm.injective liftImage
  have liftEquality : lift = target := injective (congrArg Prod.fst pairEquality)
  have functionalEquality : functional target = limit := by
    simpa only [liftEquality] using congrArg Prod.snd pairEquality
  rw [functionalEquality]
  exact ge_of_tendsto scalarLimit (Eventually.of_forall fun index => nonnegative (selection index))

namespace QuadraticEnergySpace

variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
  (nonnegative : ∀ values, 0 ≤ form values)

theorem exists_original_completion_energy_approximation
    (closable : SequentiallyClosable domain form)
    (target : closedDomain domain form nonnegative) :
    ∃ sequence : ℕ → QuadraticEnergySpace domain form nonnegative,
      Tendsto (fun index => (sequence index : Completion (QuadraticEnergySpace domain form nonnegative))) atTop
        (nhds ((closedDomainEquiv domain form nonnegative closable).symm target)) ∧
      Tendsto (fun index => form (sequence index).value) atTop
        (nhds (closedForm domain form nonnegative closable target)) := by
  classical
  obtain ⟨approximation, approximationInRange, approximationLimit⟩ :=
    mem_closure_iff_seq_limit.mp
      (Completion.denseRange_coe ((closedDomainEquiv domain form nonnegative closable).symm target))
  choose sequence sequenceEquality using approximationInRange
  have sequenceLimit : Tendsto
      (fun index => (sequence index : Completion (QuadraticEnergySpace domain form nonnegative)))
      atTop (nhds ((closedDomainEquiv domain form nonnegative closable).symm target)) := by
    simpa only [sequenceEquality] using approximationLimit
  have targetImage := congrArg Subtype.val
    ((closedDomainEquiv domain form nonnegative closable).apply_symm_apply target)
  change completionMap domain form nonnegative
    ((closedDomainEquiv domain form nonnegative closable).symm target) = (target : H) at targetImage
  have ambientLimit : Tendsto (fun index => ((sequence index).value : H)) atTop (nhds (target : H)) := by
    have mapped := (completionMap domain form nonnegative).continuous.continuousAt.tendsto.comp sequenceLimit
    change Tendsto (fun index => completionMap domain form nonnegative
      (sequence index : Completion (QuadraticEnergySpace domain form nonnegative))) atTop
      (nhds (completionMap domain form nonnegative
        ((closedDomainEquiv domain form nonnegative closable).symm target))) at mapped
    simpa only [completionMap_coe, targetImage] using mapped
  have differenceIdentity : ∀ index,
      ‖(sequence index : Completion (QuadraticEnergySpace domain form nonnegative))‖ ^ 2 -
        ‖((sequence index).value : H)‖ ^ 2 = form (sequence index).value := by
    intro index
    rw [Completion.norm_coe, norm_sq]
    ring
  refine ⟨sequence, sequenceLimit, ?_⟩
  simpa only [differenceIdentity, closedForm_value] using
    ((sequenceLimit.norm.pow 2).sub (ambientLimit.norm.pow 2))

noncomputable def completionFunctional
    (functional : QuadraticEnergySpace domain form nonnegative →L[ℝ] ℝ) :
    Completion (QuadraticEnergySpace domain form nonnegative) →L[ℝ] ℝ :=
  functional.extend Completion.toComplL

theorem closedForm_associated_extends
    (closable : SequentiallyClosable domain form) (first second : domain) :
    (closedForm domain form nonnegative closable).associated
      ⟨(first : H), original_mem_closedDomain domain form nonnegative first⟩
      ⟨(second : H), original_mem_closedDomain domain form nonnegative second⟩ =
      form.associated first second := by
  have addEquality :
      (⟨(first : H), original_mem_closedDomain domain form nonnegative first⟩ : closedDomain domain form nonnegative) +
        ⟨(second : H), original_mem_closedDomain domain form nonnegative second⟩ =
      ⟨((first + second : domain) : H), original_mem_closedDomain domain form nonnegative (first + second)⟩ := rfl
  simp only [QuadraticMap.associated_apply, addEquality, closedForm_extends]

@[simp] theorem completionFunctional_coe
    (functional : QuadraticEnergySpace domain form nonnegative →L[ℝ] ℝ)
    (values : QuadraticEnergySpace domain form nonnegative) :
    completionFunctional domain form nonnegative functional
      (values : Completion (QuadraticEnergySpace domain form nonnegative)) = functional values := by
  exact ContinuousLinearMap.extend_eq _ Completion.denseRange_coe (Completion.isUniformInducing_coe _) values

/-- The actual application takes `positivePart` to be the ambient positive-part
map and proves its core energy contraction and point positivity. Neither
positivity of the extended functional nor a positive approximation is assumed. -/
theorem completionFunctional_nonnegative_of_core_contraction
    (closable : SequentiallyClosable domain form)
    (functional : QuadraticEnergySpace domain form nonnegative →L[ℝ] ℝ)
    (positivePart : H → H) (positivePartContinuous : Continuous positivePart)
    (corePositivePart : ∀ original : domain, ∃ contracted : domain,
      (contracted : H) = positivePart (original : H) ∧ form contracted ≤ form original ∧
        0 ≤ functional ⟨contracted⟩)
    (target : closedDomain domain form nonnegative)
    (targetFixed : positivePart (target : H) = (target : H)) :
    0 ≤ completionFunctional domain form nonnegative functional
      ((closedDomainEquiv domain form nonnegative closable).symm target) := by
  classical
  obtain ⟨original, originalLimit, energyLimit⟩ :=
    exists_original_state_energy_approximation domain form nonnegative closable target
  choose contracted contractedImage contractedEnergy contractedPositive using
    fun index => corePositivePart (original index)
  have contractedLimit : Tendsto (fun index => (contracted index : H)) atTop (nhds (target : H)) := by
    simpa only [contractedImage, targetFixed] using
      positivePartContinuous.continuousAt.tendsto.comp originalLimit
  have majorantLimit := energyLimit.add (contractedLimit.norm.pow 2)
  obtain ⟨bound, boundValid⟩ := (Metric.isBounded_range_of_tendsto
    (fun index => form (original index) + ‖(contracted index : H)‖ ^ 2) majorantLimit).exists_norm_le
  let sequence : ℕ → Completion (QuadraticEnergySpace domain form nonnegative) :=
    fun index => ((⟨contracted index⟩ : QuadraticEnergySpace domain form nonnegative) :
      Completion (QuadraticEnergySpace domain form nonnegative))
  have bounded : ∀ index, ‖sequence index‖ ≤ Real.sqrt (max bound 0) := by
    intro index
    have majorantBound := boundValid _ (Set.mem_range_self index)
    have squareIdentity : ‖sequence index‖ ^ 2 = form (contracted index) + ‖(contracted index : H)‖ ^ 2 := by
      dsimp only [sequence]
      rw [Completion.norm_coe, norm_sq]
    have majorantNonnegative : 0 ≤ form (original index) + ‖(contracted index : H)‖ ^ 2 :=
      add_nonneg (nonnegative _) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg majorantNonnegative] at majorantBound
    nlinarith [Real.sq_sqrt (le_max_right bound 0), Real.sqrt_nonneg (max bound 0),
      le_max_left bound 0, contractedEnergy index, norm_nonneg (sequence index)]
  apply hilbert_functional_nonnegative_of_bounded_lifts
    (completionMap domain form nonnegative) (completionMap_injective domain form nonnegative closable)
    (completionFunctional domain form nonnegative functional) sequence
    ((closedDomainEquiv domain form nonnegative closable).symm target)
    (Real.sqrt (max bound 0)) bounded
  · have targetImage : completionMap domain form nonnegative
        ((closedDomainEquiv domain form nonnegative closable).symm target) = (target : H) :=
      congrArg Subtype.val ((closedDomainEquiv domain form nonnegative closable).apply_symm_apply target)
    simpa only [sequence, completionMap_coe, targetImage] using contractedLimit
  · intro index
    simpa only [sequence, completionFunctional_coe] using contractedPositive index

end QuadraticEnergySpace
end IGS.Sec31

#print axioms IGS.Sec31.hilbert_functional_nonnegative_of_bounded_lifts
#print axioms IGS.Sec31.QuadraticEnergySpace.exists_original_completion_energy_approximation
#print axioms IGS.Sec31.QuadraticEnergySpace.closedForm_associated_extends
#print axioms IGS.Sec31.QuadraticEnergySpace.completionFunctional_coe
#print axioms IGS.Sec31.QuadraticEnergySpace.completionFunctional_nonnegative_of_core_contraction
