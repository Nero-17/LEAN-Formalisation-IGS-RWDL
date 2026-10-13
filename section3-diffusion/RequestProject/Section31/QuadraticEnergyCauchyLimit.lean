import RequestProject.Section31.QuadraticEnergyCompletion

/-! An original-domain energy-Cauchy sequence with an ambient limit identifies
an element of the constructed closed domain and its exact limiting energy. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology UniformSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem original_energy_cauchy_limit
    (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (sequence : ℕ → domain) (limit : H)
    (ambientConvergence : Tendsto (fun index => (sequence index : H)) atTop (nhds limit))
    (energyCauchy : ∀ tolerance > 0, ∃ threshold, ∀ first ≥ threshold, ∀ second ≥ threshold,
      form (sequence first - sequence second) < tolerance) :
    ∃ membership : limit ∈ closedDomain domain form nonnegative,
      Tendsto (fun index => form (sequence index)) atTop
        (nhds (closedForm domain form nonnegative closable ⟨limit, membership⟩)) := by
  let lifted : ℕ → QuadraticEnergySpace domain form nonnegative := fun index => ⟨sequence index⟩
  let completed : ℕ → Completion (QuadraticEnergySpace domain form nonnegative) := fun index => lifted index
  have completedCauchy : CauchySeq completed := by
    apply Metric.cauchySeq_iff.2
    intro tolerance positive
    obtain ⟨energyThreshold, energySmall⟩ := energyCauchy (tolerance ^ 2 / 2) (by positivity)
    obtain ⟨normThreshold, normSmall⟩ := Metric.cauchySeq_iff.1 ambientConvergence.cauchySeq (tolerance / 2) (half_pos positive)
    refine ⟨max energyThreshold normThreshold, ?_⟩
    intro first firstAfter second secondAfter
    have smallEnergy := energySmall first ((le_max_left _ _).trans firstAfter) second ((le_max_left _ _).trans secondAfter)
    have smallNorm := normSmall first ((le_max_right _ _).trans firstAfter) second ((le_max_right _ _).trans secondAfter)
    change dist (lifted first : Completion (QuadraticEnergySpace domain form nonnegative)) (lifted second) < tolerance
    rw [Completion.dist_eq, dist_eq_norm]
    rw [dist_eq_norm] at smallNorm
    have identity := norm_sq domain form nonnegative (lifted first - lifted second)
    change ‖lifted first - lifted second‖ ^ 2 = form (sequence first - sequence second) +
      ‖(sequence first : H) - sequence second‖ ^ 2 at identity
    nlinarith [norm_nonneg (lifted first - lifted second), norm_nonneg ((sequence first : H) - sequence second)]
  obtain ⟨point, completedConvergence⟩ := cauchySeq_tendsto_of_complete completedCauchy
  have imageEquality : completionMap domain form nonnegative point = limit := by
    apply tendsto_nhds_unique _ ambientConvergence
    have mapped := (completionMap domain form nonnegative).continuous.continuousAt.tendsto.comp completedConvergence
    change Tendsto (fun index => completionMap domain form nonnegative
      (lifted index : Completion (QuadraticEnergySpace domain form nonnegative))) atTop
      (nhds (completionMap domain form nonnegative point)) at mapped
    simpa only [completionMap_coe, lifted] using mapped
  have membership : limit ∈ closedDomain domain form nonnegative := ⟨point, imageEquality⟩
  have inverseEquality : (closedDomainEquiv domain form nonnegative closable).symm ⟨limit, membership⟩ = point := by
    apply completionMap_injective domain form nonnegative closable
    rw [imageEquality]
    exact congrArg Subtype.val ((closedDomainEquiv domain form nonnegative closable).apply_symm_apply _)
  refine ⟨membership, ?_⟩
  have differenceConvergence := (completedConvergence.norm.pow 2).sub (ambientConvergence.norm.pow 2)
  have differenceIdentity : ∀ index, ‖completed index‖ ^ 2 - ‖(sequence index : H)‖ ^ 2 = form (sequence index) := by
    intro index
    change ‖(lifted index : Completion (QuadraticEnergySpace domain form nonnegative))‖ ^ 2 - _ = _
    rw [Completion.norm_coe, norm_sq]
    change form (sequence index) + ‖(sequence index : H)‖ ^ 2 - ‖(sequence index : H)‖ ^ 2 = _
    ring
  rw [closedForm_value, inverseEquality]
  simpa only [differenceIdentity] using differenceConvergence

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.original_energy_cauchy_limit

