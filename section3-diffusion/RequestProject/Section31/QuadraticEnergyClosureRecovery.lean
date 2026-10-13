import RequestProject.Section31.QuadraticEnergyCompletion

/-! Joint ambient-state and energy approximation of every element in the
constructed closed domain by the original form domain. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology UniformSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem exists_original_state_energy_approximation
    (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (target : closedDomain domain form nonnegative) :
    ∃ sequence : ℕ → domain,
      Tendsto (fun index => (sequence index : H)) atTop (nhds (target : H)) ∧
      Tendsto (fun index => form (sequence index)) atTop
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
  have ambientLimit : Tendsto (fun index => ((sequence index).value : H)) atTop (nhds (target : H)) := by
    have mapped := (completionMap domain form nonnegative).continuous.continuousAt.tendsto.comp sequenceLimit
    change Tendsto (fun index => completionMap domain form nonnegative
      (sequence index : Completion (QuadraticEnergySpace domain form nonnegative))) atTop
      (nhds (completionMap domain form nonnegative
        ((closedDomainEquiv domain form nonnegative closable).symm target))) at mapped
    have imageEquality := congrArg Subtype.val
      ((closedDomainEquiv domain form nonnegative closable).apply_symm_apply target)
    change completionMap domain form nonnegative
      ((closedDomainEquiv domain form nonnegative closable).symm target) = (target : H) at imageEquality
    simpa only [completionMap_coe, imageEquality] using mapped
  refine ⟨fun index => (sequence index).value, ambientLimit, ?_⟩
  have differenceLimit := (sequenceLimit.norm.pow 2).sub (ambientLimit.norm.pow 2)
  have differenceIdentity : ∀ index,
      ‖(sequence index : Completion (QuadraticEnergySpace domain form nonnegative))‖ ^ 2 -
        ‖((sequence index).value : H)‖ ^ 2 = form (sequence index).value := by
    intro index
    rw [Completion.norm_coe, norm_sq]
    ring
  simpa only [differenceIdentity, closedForm_value] using differenceLimit

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.exists_original_state_energy_approximation
