import RequestProject.Section31.BoundedSemigroupEnergy
import RequestProject.Section31.QuadraticEnergySemigroupSymmetry
import RequestProject.Section31.QuadraticEnergySmallStepMinimum

/-! The smoothed actual Yosida orbit has uniformly bounded original closed
energy. All operators and the closed form are the previously constructed ones. -/

namespace IGS.Sec31.QuadraticEnergySpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H))
    (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1)

theorem yosidaGenerator_selfAdjoint :
    IsSelfAdjoint (yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne) := by
  exact (IsSelfAdjoint.all (step⁻¹)).smul
    ((IsSelfAdjoint.one (H →L[ℝ] H)).sub
      (smallStepResolvent_selfAdjoint domain form nonnegative closable domainDense step stepPositive stepAtMostOne))

theorem smallStepLift_energy_le_yosida_pairing (forcing : H) :
    closedForm domain form nonnegative closable
      (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value ≤
    inner ℝ (yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing) forcing := by
  have generatorPairing := closedGenerator_variational domain form nonnegative closable domainDense
    ((resolventRangeEquiv domain form nonnegative closable domainDense).symm
      ((smallStepEquiv domain form nonnegative closable domainDense step stepPositive stepAtMostOne).symm forcing))
    (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing)
  rw [LinearEquiv.apply_symm_apply, ← yosidaGenerator_eq_closedGenerator] at generatorPairing
  change inner ℝ
      (yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing)
      ((smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value : H) =
    (closedForm domain form nonnegative closable).associated
      (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value
      (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value at generatorPairing
  rw [QuadraticMap.associated_eq_self_apply, smallStepLift_value] at generatorPairing
  have equation := smallStepSolution_identity domain form nonnegative closable domainDense
    step stepPositive stepAtMostOne forcing
  rw [← yosidaGenerator_eq_closedGenerator] at equation
  change smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing +
    step • yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing = forcing at equation
  have pairing := congrArg (fun vector : H =>
    inner ℝ (yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing) vector) equation
  dsimp only at pairing
  rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, generatorPairing] at pairing
  have correctionNonnegative := mul_nonneg stepPositive.le
    (sq_nonneg ‖yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing‖)
  linarith

theorem yosidaSmoothed_energy_time_bound (forcing : H) (time : ℝ) (timeNonnegative : 0 ≤ time) :
    2 * time * closedForm domain form nonnegative closable
      (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne
        (yosidaSemigroup domain form nonnegative closable domainDense step stepPositive stepAtMostOne time forcing)).value ≤
      ‖forcing‖ ^ 2 := by
  have energyBound := smallStepLift_energy_le_yosida_pairing domain form nonnegative closable domainDense
    step stepPositive stepAtMostOne
    (yosidaSemigroup domain form nonnegative closable domainDense step stepPositive stepAtMostOne time forcing)
  have dissipationBound := BoundedSemigroupEnergy.energy_time_bound
    (yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne)
    (yosidaGenerator_selfAdjoint domain form nonnegative closable domainDense step stepPositive stepAtMostOne)
    forcing time timeNonnegative
  rw [← yosidaSemigroup_eq_exp] at dissipationBound
  exact (mul_le_mul_of_nonneg_left energyBound (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) timeNonnegative)).trans
    dissipationBound

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.yosidaGenerator_selfAdjoint
#print axioms IGS.Sec31.QuadraticEnergySpace.smallStepLift_energy_le_yosida_pairing
#print axioms IGS.Sec31.QuadraticEnergySpace.yosidaSmoothed_energy_time_bound
