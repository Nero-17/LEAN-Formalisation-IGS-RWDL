import RequestProject.Section31.QuadraticEnergyClosureRecovery
import RequestProject.Section31.HilbertClosedBallImage

/-! Ambient lower semicontinuity of the constructed energy closure, and
inheritance of continuous energy-decreasing maps from its original core. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology UniformSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem exists_closed_limit_of_energy_majorant
    (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (sequence : ℕ → domain) (target : H) (majorant : ℕ → ℝ) (energyBound : ℝ)
    (ambientLimit : Tendsto (fun index => (sequence index : H)) atTop (nhds target))
    (energyControl : ∀ index, form (sequence index) ≤ majorant index)
    (majorantLimit : Tendsto majorant atTop (nhds energyBound)) :
    ∃ membership : target ∈ closedDomain domain form nonnegative,
      closedForm domain form nonnegative closable ⟨target, membership⟩ ≤ energyBound := by
  classical
  have boundNonnegative : 0 ≤ energyBound := ge_of_tendsto majorantLimit
    (Filter.Eventually.of_forall fun index => (nonnegative _).trans (energyControl index))
  let approximation : ℕ → Completion (QuadraticEnergySpace domain form nonnegative) :=
    fun index => ((⟨sequence index⟩ : QuadraticEnergySpace domain form nonnegative) :
      Completion (QuadraticEnergySpace domain form nonnegative))
  have mappedLimit : Tendsto (fun index => completionMap domain form nonnegative (approximation index))
      atTop (nhds target) := by
    simpa only [approximation, completionMap_coe] using ambientLimit
  have combinedLimit := majorantLimit.add (ambientLimit.norm.pow 2)
  have approximateBound : ∀ bound > Real.sqrt (energyBound + ‖target‖ ^ 2),
      ∀ᶠ index in atTop, ‖approximation index‖ ≤ bound := by
    intro bound boundGreater
    have boundPositive : 0 < bound := lt_of_le_of_lt (Real.sqrt_nonneg _) boundGreater
    have combinedNonnegative : 0 ≤ energyBound + ‖target‖ ^ 2 :=
      add_nonneg boundNonnegative (sq_nonneg _)
    have squareGreater : energyBound + ‖target‖ ^ 2 < bound ^ 2 := by
      nlinarith [Real.sq_sqrt combinedNonnegative, Real.sqrt_nonneg (energyBound + ‖target‖ ^ 2)]
    filter_upwards [combinedLimit.eventually (gt_mem_nhds squareGreater)] with index small
    have identity : ‖approximation index‖ ^ 2 = form (sequence index) + ‖(sequence index : H)‖ ^ 2 := by
      dsimp only [approximation]
      rw [Completion.norm_coe, norm_sq]
    nlinarith [energyControl index, norm_nonneg (approximation index)]
  obtain ⟨lift, liftImage, liftBound⟩ := hilbert_exists_lift_of_eventual_approximate_norm_bound
    (completionMap domain form nonnegative) (completionMap_injective domain form nonnegative closable)
    approximation target (Real.sqrt (energyBound + ‖target‖ ^ 2)) mappedLimit approximateBound
  have membership : target ∈ closedDomain domain form nonnegative := ⟨lift, liftImage⟩
  refine ⟨membership, ?_⟩
  have inverseEquality : (closedDomainEquiv domain form nonnegative closable).symm ⟨target, membership⟩ = lift := by
    apply completionMap_injective domain form nonnegative closable
    exact (congrArg Subtype.val ((closedDomainEquiv domain form nonnegative closable).apply_symm_apply
      ⟨target, membership⟩)).trans liftImage.symm
  rw [closedForm_value, inverseEquality]
  nlinarith [norm_nonneg lift, Real.sqrt_nonneg (energyBound + ‖target‖ ^ 2),
    Real.sq_sqrt (add_nonneg boundNonnegative (sq_nonneg ‖target‖))]

theorem closedForm_continuous_core_contraction
    (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (contraction : H → H) (contractionContinuous : Continuous contraction)
    (coreContraction : ∀ original : domain, ∃ contracted : domain,
      (contracted : H) = contraction (original : H) ∧ form contracted ≤ form original)
    (target : closedDomain domain form nonnegative) :
    ∃ membership : contraction (target : H) ∈ closedDomain domain form nonnegative,
      closedForm domain form nonnegative closable ⟨contraction (target : H), membership⟩ ≤
        closedForm domain form nonnegative closable target := by
  classical
  obtain ⟨sequence, ambientLimit, energyLimit⟩ :=
    exists_original_state_energy_approximation domain form nonnegative closable target
  choose contracted contractedImage contractedEnergy using fun index => coreContraction (sequence index)
  apply exists_closed_limit_of_energy_majorant domain form nonnegative closable contracted
    (contraction (target : H)) (fun index => form (sequence index))
    (closedForm domain form nonnegative closable target)
  · simpa only [contractedImage] using contractionContinuous.continuousAt.tendsto.comp ambientLimit
  · exact contractedEnergy
  · exact energyLimit

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.exists_closed_limit_of_energy_majorant
#print axioms IGS.Sec31.QuadraticEnergySpace.closedForm_continuous_core_contraction
