import RequestProject.Section31.QuadraticEnergyYosidaSemigroup
import RequestProject.Section31.BoundedSemigroupComparison

/-! The actual exponential approximants are strongly Cauchy at every time.
The Cauchy property and the uniform dense-core time bound are proved here,
not supplied as hypotheses to the eventual semigroup construction. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H))

theorem yosidaSemigroup_domain_time_bound
    (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1)
    (time : ℝ) (timeNonnegative : 0 ≤ time)
    (values : generatorDomain domain form nonnegative closable) :
    ‖yosidaSemigroup domain form nonnegative closable domainDense step stepPositive stepAtMostOne time values - (values : H)‖ ≤
      time * ‖closedGenerator domain form nonnegative closable domainDense values‖ := by
  have bound := BoundedSemigroupComparison.norm_exp_apply_sub_self_le
    (yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne)
    (fun parameter parameterNonnegative =>
      yosidaSemigroup_norm domain form nonnegative closable domainDense step stepPositive stepAtMostOne parameter parameterNonnegative)
    time timeNonnegative (values : H)
  change ‖yosidaSemigroup domain form nonnegative closable domainDense step stepPositive stepAtMostOne time values - (values : H)‖ ≤ _ at bound
  rw [yosidaGenerator_on_domain] at bound
  exact bound.trans (mul_le_mul_of_nonneg_left
    (smallStepResolvent_norm domain form nonnegative closable domainDense step stepPositive stepAtMostOne _) timeNonnegative)

theorem yosidaSemigroup_strong_cauchy
    (steps : ℕ → ℝ) (stepsPositive : ∀ index, 0 < steps index)
    (stepsAtMostOne : ∀ index, steps index ≤ 1) (stepsLimit : Tendsto steps atTop (nhds 0))
    (time : ℝ) (timeNonnegative : 0 ≤ time) (forcing : H) :
    CauchySeq (fun index => yosidaSemigroup domain form nonnegative closable domainDense
      (steps index) (stepsPositive index) (stepsAtMostOne index) time forcing) := by
  apply Metric.cauchySeq_iff.mpr
  intro tolerance tolerancePositive
  obtain ⟨approximation, approximationMember, approximationClose⟩ :=
    Metric.mem_closure_iff.mp (generatorDomain_dense domain form nonnegative closable domainDense forcing)
      (tolerance / 4) (by positivity)
  let values : generatorDomain domain form nonnegative closable := ⟨approximation, approximationMember⟩
  have scaledLimit := (yosidaGenerator_on_domain_limit domain form nonnegative closable domainDense
    steps stepsPositive stepsAtMostOne stepsLimit values).const_smul time
  obtain ⟨threshold, scaledClose⟩ := Metric.cauchySeq_iff.mp scaledLimit.cauchySeq
    (tolerance / 2) (by positivity)
  refine ⟨threshold, ?_⟩
  intro first firstLarge second secondLarge
  have comparison := BoundedSemigroupComparison.norm_exp_apply_sub_le
    (yosidaGenerator domain form nonnegative closable domainDense
      (steps first) (stepsPositive first) (stepsAtMostOne first))
    (yosidaGenerator domain form nonnegative closable domainDense
      (steps second) (stepsPositive second) (stepsAtMostOne second))
    (yosidaGenerator_commute domain form nonnegative closable domainDense
      (steps first) (stepsPositive first) (stepsAtMostOne first)
      (steps second) (stepsPositive second) (stepsAtMostOne second))
    (fun parameter parameterNonnegative => yosidaSemigroup_norm domain form nonnegative closable domainDense
      (steps first) (stepsPositive first) (stepsAtMostOne first) parameter parameterNonnegative)
    (fun parameter parameterNonnegative => yosidaSemigroup_norm domain form nonnegative closable domainDense
      (steps second) (stepsPositive second) (stepsAtMostOne second) parameter parameterNonnegative)
    time timeNonnegative (values : H)
  have scaledSmall := scaledClose first firstLarge second secondLarge
  simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg timeNonnegative] at scaledSmall
  have firstContraction : dist
      (yosidaSemigroup domain form nonnegative closable domainDense
        (steps first) (stepsPositive first) (stepsAtMostOne first) time forcing)
      (yosidaSemigroup domain form nonnegative closable domainDense
        (steps first) (stepsPositive first) (stepsAtMostOne first) time approximation) ≤ dist forcing approximation := by
    simpa only [dist_eq_norm, ← map_sub] using
      yosidaSemigroup_apply_norm domain form nonnegative closable domainDense
        (steps first) (stepsPositive first) (stepsAtMostOne first) time timeNonnegative (forcing - approximation)
  have secondContraction : dist
      (yosidaSemigroup domain form nonnegative closable domainDense
        (steps second) (stepsPositive second) (stepsAtMostOne second) time approximation)
      (yosidaSemigroup domain form nonnegative closable domainDense
        (steps second) (stepsPositive second) (stepsAtMostOne second) time forcing) ≤ dist forcing approximation := by
    rw [dist_comm]
    simpa only [dist_eq_norm, ← map_sub] using
      yosidaSemigroup_apply_norm domain form nonnegative closable domainDense
        (steps second) (stepsPositive second) (stepsAtMostOne second) time timeNonnegative (forcing - approximation)
  have middle : dist
      (yosidaSemigroup domain form nonnegative closable domainDense
        (steps first) (stepsPositive first) (stepsAtMostOne first) time approximation)
      (yosidaSemigroup domain form nonnegative closable domainDense
        (steps second) (stepsPositive second) (stepsAtMostOne second) time approximation) < tolerance / 2 := by
    rw [dist_eq_norm]
    change ‖NormedSpace.exp ((-time) • yosidaGenerator domain form nonnegative closable domainDense
        (steps first) (stepsPositive first) (stepsAtMostOne first)) (values : H) -
      NormedSpace.exp ((-time) • yosidaGenerator domain form nonnegative closable domainDense
        (steps second) (stepsPositive second) (stepsAtMostOne second)) (values : H)‖ < _
    exact comparison.trans_lt scaledSmall
  have firstTriangle := dist_triangle
    (yosidaSemigroup domain form nonnegative closable domainDense (steps first) (stepsPositive first) (stepsAtMostOne first) time forcing)
    (yosidaSemigroup domain form nonnegative closable domainDense (steps first) (stepsPositive first) (stepsAtMostOne first) time approximation)
    (yosidaSemigroup domain form nonnegative closable domainDense (steps second) (stepsPositive second) (stepsAtMostOne second) time forcing)
  have secondTriangle := dist_triangle
    (yosidaSemigroup domain form nonnegative closable domainDense (steps first) (stepsPositive first) (stepsAtMostOne first) time approximation)
    (yosidaSemigroup domain form nonnegative closable domainDense (steps second) (stepsPositive second) (stepsAtMostOne second) time approximation)
    (yosidaSemigroup domain form nonnegative closable domainDense (steps second) (stepsPositive second) (stepsAtMostOne second) time forcing)
  linarith

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.yosidaSemigroup_domain_time_bound
#print axioms IGS.Sec31.QuadraticEnergySpace.yosidaSemigroup_strong_cauchy
