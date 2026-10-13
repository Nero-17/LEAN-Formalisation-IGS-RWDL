import RequestProject.Section31.QuadraticEnergyCompletion

/-! The closed-domain norm is exactly the form-plus-ambient norm. The
sequential statement below exposes completeness in those original quantities,
without hiding it behind an arbitrarily transported norm. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values)
    (closable : SequentiallyClosable domain form)

theorem closed_energy_norm_sq
    (values : QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable) (closedForm_nonnegative domain form nonnegative closable)) :
    ‖values‖ ^ 2 = closedForm domain form nonnegative closable values.value + ‖(values.value : H)‖ ^ 2 :=
  norm_sq (closedDomain domain form nonnegative) (closedForm domain form nonnegative closable)
    (closedForm_nonnegative domain form nonnegative closable) values

theorem closed_energy_distance_sq
    (first second : QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable) (closedForm_nonnegative domain form nonnegative closable)) :
    dist first second ^ 2 = closedForm domain form nonnegative closable (first.value - second.value) +
      ‖(first.value : H) - second.value‖ ^ 2 := by
  rw [dist_eq_norm, closed_energy_norm_sq]
  rfl

theorem closedForm_complete_of_energy_cauchy
    (sequence : ℕ → closedDomain domain form nonnegative)
    (energyCauchy : ∀ tolerance > 0, ∃ threshold, ∀ first ≥ threshold, ∀ second ≥ threshold,
      closedForm domain form nonnegative closable (sequence first - sequence second) +
        ‖(sequence first : H) - sequence second‖ ^ 2 < tolerance) :
    ∃ limit : closedDomain domain form nonnegative,
      Tendsto (fun index => closedForm domain form nonnegative closable (sequence index - limit) +
        ‖(sequence index : H) - limit‖ ^ 2) atTop (nhds 0) := by
  letI := closedEnergySpace_complete domain form nonnegative closable
  let lifted : ℕ → QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable) (closedForm_nonnegative domain form nonnegative closable) :=
    fun index => ⟨sequence index⟩
  have liftedCauchy : CauchySeq lifted := by
    apply Metric.cauchySeq_iff.mpr
    intro tolerance tolerancePositive
    obtain ⟨threshold, differenceSmall⟩ := energyCauchy (tolerance ^ 2) (sq_pos_of_pos tolerancePositive)
    refine ⟨threshold, fun first firstLarge second secondLarge => ?_⟩
    have small := differenceSmall first firstLarge second secondLarge
    have distanceIdentity := closed_energy_distance_sq domain form nonnegative closable (lifted first) (lifted second)
    change dist (lifted first) (lifted second) ^ 2 =
      closedForm domain form nonnegative closable (sequence first - sequence second) +
        ‖(sequence first : H) - sequence second‖ ^ 2 at distanceIdentity
    nlinarith [dist_nonneg (x := lifted first) (y := lifted second)]
  obtain ⟨limit, convergence⟩ := cauchySeq_tendsto_of_complete liftedCauchy
  refine ⟨limit.value, ?_⟩
  have squaredDistance := (convergence.dist (tendsto_const_nhds (x := limit))).pow 2
  simpa only [dist_self, zero_pow (by decide : 2 ≠ 0),
    closed_energy_distance_sq, lifted] using squaredDistance

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.closed_energy_norm_sq
#print axioms IGS.Sec31.QuadraticEnergySpace.closed_energy_distance_sq
#print axioms IGS.Sec31.QuadraticEnergySpace.closedForm_complete_of_energy_cauchy
