import RequestProject.Section31.QuadraticEnergyClosedNorm
import RequestProject.Section31.HilbertClosedBallImage

/-! Closed energy sublevels under ambient convergence. A bounded Hilbert lift
is constructed; membership of the ambient limit in the form domain is a
conclusion, not an input. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)

theorem closedForm_sublevel_limit
    (sequence : ℕ → closedDomain domain form nonnegative) (target : H)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (ambientLimit : Tendsto (fun index => (sequence index : H)) atTop (nhds target))
    (energyBound : ∀ᶠ index in atTop, closedForm domain form nonnegative closable (sequence index) ≤ bound) :
    ∃ targetLift : closedDomain domain form nonnegative,
      (targetLift : H) = target ∧ closedForm domain form nonnegative closable targetLift ≤ bound := by
  letI := closedEnergySpace_complete domain form nonnegative closable
  let lifted : ℕ → QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable) (closedForm_nonnegative domain form nonnegative closable) :=
    fun index => ⟨sequence index⟩
  have eventualNormBound : ∀ radius > Real.sqrt (bound + ‖target‖ ^ 2),
      ∀ᶠ index in atTop, ‖lifted index‖ ≤ radius := by
    intro radius radiusGreater
    have rootNonnegative := Real.sqrt_nonneg (bound + ‖target‖ ^ 2)
    have rootSquare := Real.sq_sqrt (add_nonneg boundNonnegative (sq_nonneg ‖target‖))
    have radiusPositive : 0 < radius := lt_of_le_of_lt rootNonnegative radiusGreater
    have squaredGap : ‖target‖ ^ 2 < radius ^ 2 - bound := by
      nlinarith
    have eventuallyAmbient := (ambientLimit.norm.pow 2).eventually_lt_const squaredGap
    filter_upwards [eventuallyAmbient, energyBound] with index ambientSmall energySmall
    have identity := closed_energy_norm_sq domain form nonnegative closable (lifted index)
    change ‖lifted index‖ ^ 2 = closedForm domain form nonnegative closable (sequence index) +
      ‖(sequence index : H)‖ ^ 2 at identity
    nlinarith [norm_nonneg (lifted index)]
  have inclusionInjective : Function.Injective
      (inclusion (closedDomain domain form nonnegative) (closedForm domain form nonnegative closable)
        (closedForm_nonnegative domain form nonnegative closable)) := by
    intro first second same
    apply (equivDomain _ _ _).injective
    exact Subtype.ext same
  obtain ⟨limit, limitImage, limitBound⟩ := hilbert_exists_lift_of_eventual_approximate_norm_bound
    (inclusion (closedDomain domain form nonnegative) (closedForm domain form nonnegative closable)
      (closedForm_nonnegative domain form nonnegative closable)) inclusionInjective lifted target
      (Real.sqrt (bound + ‖target‖ ^ 2)) ambientLimit eventualNormBound
  refine ⟨limit.value, limitImage, ?_⟩
  have identity := closed_energy_norm_sq domain form nonnegative closable limit
  change (limit.value : H) = target at limitImage
  rw [limitImage] at identity
  have rootSquare := Real.sq_sqrt (add_nonneg boundNonnegative (sq_nonneg ‖target‖))
  nlinarith [norm_nonneg limit, Real.sqrt_nonneg (bound + ‖target‖ ^ 2)]

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.closedForm_sublevel_limit
