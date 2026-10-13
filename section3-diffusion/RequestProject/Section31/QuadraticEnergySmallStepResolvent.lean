import RequestProject.Section31.QuadraticEnergyGenerator
import RequestProject.Section31.QuadraticEnergyResolventFirm
import Mathlib.Analysis.Normed.Ring.Units

/-! Positive small-step resolvents of the actual operator. Surjectivity is
constructed by a convergent geometric series of bounded operators, using the
proved complementary contraction of the unit resolvent. -/

namespace IGS.Sec31.QuadraticEnergySpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)

theorem smallStep_resolvent_surjective (domainDense : Dense (domain : Set H))
    (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1) :
    Function.Surjective (fun values : generatorDomain domain form nonnegative closable =>
      (values : H) + step • closedGenerator domain form nonnegative closable domainDense values) := by
  have perturbationBound :
      ‖(1 - step) • (ContinuousLinearMap.id ℝ H - resolventState domain form nonnegative closable)‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr stepAtMostOne)]
    have bound := identity_sub_resolvent_operator_norm_le domain form nonnegative closable
    nlinarith
  let inverseUnit := Units.oneSub
    ((1 - step) • (ContinuousLinearMap.id ℝ H - resolventState domain form nonnegative closable))
    perturbationBound
  intro forcing
  refine ⟨resolventRangeEquiv domain form nonnegative closable domainDense (inverseUnit.inv forcing), ?_⟩
  dsimp only
  rw [closedGenerator_resolvent]
  change resolventState domain form nonnegative closable (inverseUnit.inv forcing) +
    step • (inverseUnit.inv forcing - resolventState domain form nonnegative closable
      (inverseUnit.inv forcing)) = forcing
  have inversion := congrArg (fun operator : H →L[ℝ] H => operator forcing) inverseUnit.val_inv
  change inverseUnit.inv forcing - (1 - step) •
    (inverseUnit.inv forcing - resolventState domain form nonnegative closable
      (inverseUnit.inv forcing)) = forcing at inversion
  calc
    _ = inverseUnit.inv forcing - (1 - step) •
        (inverseUnit.inv forcing - resolventState domain form nonnegative closable
          (inverseUnit.inv forcing)) := by module
    _ = forcing := inversion

theorem positiveStep_resolvent_norm_bound (domainDense : Dense (domain : Set H))
    (step : ℝ) (stepNonnegative : 0 ≤ step)
    (values : generatorDomain domain form nonnegative closable) :
    ‖(values : H)‖ ≤
      ‖(values : H) + step • closedGenerator domain form nonnegative closable domainDense values‖ := by
  have nonnegativeGenerator := closedGenerator_nonnegative domain form nonnegative closable domainDense values
  have identity : inner ℝ
      ((values : H) + step • closedGenerator domain form nonnegative closable domainDense values)
      (values : H) = ‖(values : H)‖ ^ 2 + step *
        inner ℝ (closedGenerator domain form nonnegative closable domainDense values) (values : H) := by
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have bound := real_inner_le_norm
    ((values : H) + step • closedGenerator domain form nonnegative closable domainDense values)
    (values : H)
  have productNonnegative := mul_nonneg stepNonnegative nonnegativeGenerator
  by_cases normZero : ‖(values : H)‖ = 0
  · rw [normZero]
    exact norm_nonneg _
  · have normPositive : 0 < ‖(values : H)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm normZero)
    nlinarith

theorem positiveStep_resolvent_injective (domainDense : Dense (domain : Set H))
    (step : ℝ) (stepNonnegative : 0 ≤ step) :
    Function.Injective (fun values : generatorDomain domain form nonnegative closable =>
      (values : H) + step • closedGenerator domain form nonnegative closable domainDense values) := by
  intro first second equality
  have differenceIdentity : ((first - second : generatorDomain domain form nonnegative closable) : H) +
      step • closedGenerator domain form nonnegative closable domainDense (first - second) = 0 := by
    simp only [map_sub, Submodule.coe_sub, smul_sub]
    have difference := sub_eq_zero.mpr equality
    dsimp only at difference
    convert difference using 1 <;> abel
  have bound := positiveStep_resolvent_norm_bound domain form nonnegative closable domainDense
    step stepNonnegative (first - second)
  rw [differenceIdentity, norm_zero] at bound
  apply Subtype.ext
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm bound (norm_nonneg _)))

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.smallStep_resolvent_surjective
#print axioms IGS.Sec31.QuadraticEnergySpace.positiveStep_resolvent_norm_bound
#print axioms IGS.Sec31.QuadraticEnergySpace.positiveStep_resolvent_injective
