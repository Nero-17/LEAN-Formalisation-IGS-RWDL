import RequestProject.Section31.QuadraticEnergySmallStepOperator
import RequestProject.Section31.QuadraticEnergyGeneratorDensity

/-! Strong convergence of the constructed small-step resolvents to the
identity on the whole ambient Hilbert space, not just the operator domain. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H))

theorem smallStepResolvent_strong_limit
    (steps : ℕ → ℝ) (stepsPositive : ∀ index, 0 < steps index)
    (stepsAtMostOne : ∀ index, steps index ≤ 1) (stepsLimit : Tendsto steps atTop (nhds 0))
    (forcing : H) :
    Tendsto (fun index => smallStepResolvent domain form nonnegative closable domainDense
      (steps index) (stepsPositive index) (stepsAtMostOne index) forcing) atTop (nhds forcing) := by
  apply Metric.tendsto_nhds.mpr
  intro tolerance tolerancePositive
  obtain ⟨approximation, approximationMember, approximationClose⟩ :=
    Metric.mem_closure_iff.mp (generatorDomain_dense domain form nonnegative closable domainDense forcing)
      (tolerance / 4) (by positivity)
  let values : generatorDomain domain form nonnegative closable := ⟨approximation, approximationMember⟩
  have errorLimit : Tendsto
      (fun index => steps index * ‖closedGenerator domain form nonnegative closable domainDense values‖)
      atTop (nhds 0) := by
    simpa only [zero_mul] using stepsLimit.mul_const
      ‖closedGenerator domain form nonnegative closable domainDense values‖
  have errorSmall : ∀ᶠ index in atTop,
      steps index * ‖closedGenerator domain form nonnegative closable domainDense values‖ < tolerance / 2 :=
    (tendsto_order.mp errorLimit).2 _ (by positivity)
  filter_upwards [errorSmall] with index indexError
  have contraction : dist
      (smallStepResolvent domain form nonnegative closable domainDense
        (steps index) (stepsPositive index) (stepsAtMostOne index) forcing)
      (smallStepResolvent domain form nonnegative closable domainDense
        (steps index) (stepsPositive index) (stepsAtMostOne index) approximation) ≤ dist forcing approximation := by
    simpa only [dist_eq_norm, ← map_sub] using
      smallStepResolvent_norm domain form nonnegative closable domainDense
        (steps index) (stepsPositive index) (stepsAtMostOne index) (forcing - approximation)
  have middle : dist
      (smallStepResolvent domain form nonnegative closable domainDense
        (steps index) (stepsPositive index) (stepsAtMostOne index) approximation) approximation ≤
      steps index * ‖closedGenerator domain form nonnegative closable domainDense values‖ := by
    simpa only [dist_eq_norm, norm_sub_rev] using
      smallStepResolvent_domain_error domain form nonnegative closable domainDense
        (steps index) (stepsPositive index) (stepsAtMostOne index) values
  have triangle := dist_triangle
    (smallStepResolvent domain form nonnegative closable domainDense
      (steps index) (stepsPositive index) (stepsAtMostOne index) forcing)
    (smallStepResolvent domain form nonnegative closable domainDense
      (steps index) (stepsPositive index) (stepsAtMostOne index) approximation) forcing
  have triangleLast := dist_triangle
    (smallStepResolvent domain form nonnegative closable domainDense
      (steps index) (stepsPositive index) (stepsAtMostOne index) approximation) approximation forcing
  rw [dist_comm approximation forcing] at triangleLast
  linarith

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.smallStepResolvent_strong_limit
