import RequestProject.Section31.QuadraticEnergyCompletion

/-! Original-core density in the explicit closed energy-plus-ambient norm. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology UniformSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem exists_original_closed_energy_approximation
    (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (target : closedDomain domain form nonnegative) :
    ∃ sequence : ℕ → domain,
      Tendsto (fun index =>
        closedForm domain form nonnegative closable
          (⟨(sequence index : H), original_mem_closedDomain domain form nonnegative (sequence index)⟩ - target) +
            ‖(sequence index : H) - target.val‖ ^ 2) atTop (nhds 0) := by
  classical
  obtain ⟨approximation, approximationInRange, approximationLimit⟩ :=
    mem_closure_iff_seq_limit.mp
      (Completion.denseRange_coe ((closedDomainEquiv domain form nonnegative closable).symm target))
  choose sequence sequenceEquality using approximationInRange
  have sequenceLimit : Tendsto
      (fun index => (sequence index : Completion (QuadraticEnergySpace domain form nonnegative)))
      atTop (nhds ((closedDomainEquiv domain form nonnegative closable).symm target)) := by
    simpa only [sequenceEquality] using approximationLimit
  have inverseOriginal : ∀ index,
      (closedDomainEquiv domain form nonnegative closable).symm
        ⟨((sequence index).value : H), original_mem_closedDomain domain form nonnegative (sequence index).value⟩ =
      (sequence index : Completion (QuadraticEnergySpace domain form nonnegative)) := by
    intro index
    apply completionMap_injective domain form nonnegative closable
    rw [completionMap_coe]
    exact congrArg Subtype.val ((closedDomainEquiv domain form nonnegative closable).apply_symm_apply _)
  have normIdentity : ∀ index,
      closedForm domain form nonnegative closable
        (⟨((sequence index).value : H), original_mem_closedDomain domain form nonnegative (sequence index).value⟩ - target) +
          ‖((sequence index).value : H) - target.val‖ ^ 2 =
      ‖(sequence index : Completion (QuadraticEnergySpace domain form nonnegative)) -
        (closedDomainEquiv domain form nonnegative closable).symm target‖ ^ 2 := by
    intro index
    rw [closedForm_value, map_sub, inverseOriginal]
    change (_ - ‖((sequence index).value : H) - target.val‖ ^ 2) +
      ‖((sequence index).value : H) - target.val‖ ^ 2 = _
    ring
  refine ⟨fun index => (sequence index).value, ?_⟩
  simp_rw [normIdentity]
  simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
    ((sequenceLimit.sub (tendsto_const_nhds (x :=
      (closedDomainEquiv domain form nonnegative closable).symm target))).norm.pow 2)

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.exists_original_closed_energy_approximation
