import RequestProject.Section31.QuadraticEnergyClosedNorm

/-! Joint original-core recovery in the true energy-plus-ambient norm.
Every energy-bounded closed linear functional converges along this same recovery. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology UniformSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem exists_original_strong_energy_approximation
    (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (target : closedDomain domain form nonnegative) :
    ∃ sequence : ℕ → domain,
      Tendsto (fun index => (sequence index : H)) atTop (nhds (target : H)) ∧
      Tendsto (fun index => form (sequence index)) atTop
        (nhds (closedForm domain form nonnegative closable target)) ∧
      Tendsto (fun index =>
        closedForm domain form nonnegative closable
          (⟨(sequence index : H), original_mem_closedDomain domain form nonnegative (sequence index)⟩ - target) +
        ‖(sequence index : H) - target‖ ^ 2) atTop (nhds 0) := by
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
  have energyConvergence : Tendsto (fun index => form (sequence index).value) atTop
      (nhds (closedForm domain form nonnegative closable target)) := by
    have differenceLimit := (sequenceLimit.norm.pow 2).sub (ambientLimit.norm.pow 2)
    have differenceIdentity : ∀ index,
        ‖(sequence index : Completion (QuadraticEnergySpace domain form nonnegative))‖ ^ 2 -
          ‖((sequence index).value : H)‖ ^ 2 = form (sequence index).value := by
      intro index
      rw [Completion.norm_coe, norm_sq]
      ring
    simpa only [differenceIdentity, closedForm_value] using differenceLimit
  refine ⟨fun index => (sequence index).value, ambientLimit, energyConvergence, ?_⟩
  let embedded : ℕ → closedDomain domain form nonnegative := fun index =>
    ⟨((sequence index).value : H), original_mem_closedDomain domain form nonnegative (sequence index).value⟩
  have inverseEmbedded (index : ℕ) :
      (closedDomainEquiv domain form nonnegative closable).symm (embedded index) =
        (sequence index : Completion (QuadraticEnergySpace domain form nonnegative)) := by
    apply completionMap_injective domain form nonnegative closable
    rw [completionMap_coe]
    exact congrArg Subtype.val
      ((closedDomainEquiv domain form nonnegative closable).apply_symm_apply (embedded index))
  have normIdentity (index : ℕ) :
      closedForm domain form nonnegative closable (embedded index - target) +
        ‖((sequence index).value : H) - target‖ ^ 2 =
      ‖(sequence index : Completion (QuadraticEnergySpace domain form nonnegative)) -
        (closedDomainEquiv domain form nonnegative closable).symm target‖ ^ 2 := by
    rw [closedForm_value, map_sub, inverseEmbedded]
    change (_ - ‖((sequence index).value : H) - target‖ ^ 2) +
      ‖((sequence index).value : H) - target‖ ^ 2 = _
    ring
  have convergence := (sequenceLimit.sub_const
    ((closedDomainEquiv domain form nonnegative closable).symm target)).norm.pow 2
  simpa only [← normIdentity, embedded, sub_self, norm_zero,
    zero_pow (by decide : 2 ≠ 0)] using convergence

theorem exists_original_functional_approximation
    (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (evaluation : closedDomain domain form nonnegative →ₗ[ℝ] ℝ)
    (normConstant energyConstant : ℝ) (normNonnegative : 0 ≤ normConstant)
    (energyNonnegative : 0 ≤ energyConstant)
    (bound : ∀ values : closedDomain domain form nonnegative,
      evaluation values ^ 2 ≤ normConstant * ‖(values : H)‖ ^ 2 +
        energyConstant * closedForm domain form nonnegative closable values)
    (target : closedDomain domain form nonnegative) :
    ∃ sequence : ℕ → domain,
      Tendsto (fun index => (sequence index : H)) atTop (nhds (target : H)) ∧
      Tendsto (fun index => form (sequence index)) atTop
        (nhds (closedForm domain form nonnegative closable target)) ∧
      Tendsto (fun index => evaluation
        ⟨(sequence index : H), original_mem_closedDomain domain form nonnegative (sequence index)⟩)
        atTop (nhds (evaluation target)) := by
  obtain ⟨sequence, ambientConvergence, energyConvergence, strongEnergyConvergence⟩ :=
    exists_original_strong_energy_approximation domain form nonnegative closable target
  let embedded : ℕ → closedDomain domain form nonnegative := fun index =>
    ⟨(sequence index : H), original_mem_closedDomain domain form nonnegative (sequence index)⟩
  have squareBound (index : ℕ) : (evaluation (embedded index) - evaluation target) ^ 2 ≤
      (normConstant + energyConstant) *
        (closedForm domain form nonnegative closable (embedded index - target) +
          ‖(sequence index : H) - target‖ ^ 2) := by
    have estimate := bound (embedded index - target)
    rw [map_sub] at estimate
    change _ ≤ normConstant * ‖(sequence index : H) - target‖ ^ 2 +
      energyConstant * closedForm domain form nonnegative closable (embedded index - target) at estimate
    nlinarith [mul_nonneg normNonnegative
      (closedForm_nonnegative domain form nonnegative closable (embedded index - target)),
      mul_nonneg energyNonnegative (sq_nonneg ‖(sequence index : H) - target‖)]
  have upperConvergence := strongEnergyConvergence.const_mul (normConstant + energyConstant)
  have squareConvergence : Tendsto (fun index =>
      (evaluation (embedded index) - evaluation target) ^ 2) atTop (nhds 0) :=
    squeeze_zero (fun _ => sq_nonneg _) squareBound (by simpa only [mul_zero] using upperConvergence)
  have normConvergence : Tendsto (fun index => ‖evaluation (embedded index) - evaluation target‖)
      atTop (nhds 0) := by
    simpa only [Real.sqrt_sq_eq_abs, Real.norm_eq_abs, Real.sqrt_zero] using squareConvergence.sqrt
  exact ⟨sequence, ambientConvergence, energyConvergence,
    tendsto_iff_norm_sub_tendsto_zero.mpr normConvergence⟩

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.exists_original_strong_energy_approximation

#print axioms IGS.Sec31.QuadraticEnergySpace.exists_original_functional_approximation
