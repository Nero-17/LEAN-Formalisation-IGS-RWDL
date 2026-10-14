import RequestProject.Section31.QuadraticEnergyYosidaEnergy

/-! The bounded Yosida quadratic energy is dominated by the original
closed energy, by the actual resolvent minimum principle. -/

namespace IGS.Sec31.QuadraticEnergySpace

variable {Hilbert : Type*} [NormedAddCommGroup Hilbert]
    [InnerProductSpace ℝ Hilbert] [CompleteSpace Hilbert]
variable (domain : Submodule ℝ Hilbert) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set Hilbert))
    (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1)

theorem smallStep_energy_correction_eq_yosida_pairing (forcing : Hilbert) :
    closedForm domain form nonnegative closable
        (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value +
      step * ‖yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing‖ ^ 2 =
        inner ℝ (yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing) forcing := by
  have generatorPairing := closedGenerator_variational domain form nonnegative closable domainDense
    ((resolventRangeEquiv domain form nonnegative closable domainDense).symm
      ((smallStepEquiv domain form nonnegative closable domainDense step stepPositive stepAtMostOne).symm forcing))
    (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing)
  rw [LinearEquiv.apply_symm_apply, ← yosidaGenerator_eq_closedGenerator] at generatorPairing
  change inner ℝ
      (yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing)
      ((smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value : Hilbert) =
    (closedForm domain form nonnegative closable).associated
      (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value
      (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value at generatorPairing
  rw [QuadraticMap.associated_eq_self_apply, smallStepLift_value] at generatorPairing
  have equation := smallStepSolution_identity domain form nonnegative closable domainDense
    step stepPositive stepAtMostOne forcing
  rw [← yosidaGenerator_eq_closedGenerator] at equation
  change smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing +
    step • yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing = forcing at equation
  have pairing := congrArg (fun values : Hilbert =>
    inner ℝ (yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing) values) equation
  simpa only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, generatorPairing] using pairing

theorem yosida_pairing_le_closed_energy (target : closedDomain domain form nonnegative) :
    inner ℝ (yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne target.val)
      target.val ≤ closedForm domain form nonnegative closable target := by
  have minimum := smallStep_minimizes domain form nonnegative closable domainDense
    step stepPositive stepAtMostOne target.val ⟨target⟩
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero] at minimum
  have equation := smallStepSolution_identity domain form nonnegative closable domainDense
    step stepPositive stepAtMostOne target.val
  rw [← yosidaGenerator_eq_closedGenerator] at equation
  change smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne target.val +
    step • yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne target.val = target.val at equation
  have difference : smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne target.val -
      target.val = -(step • yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne target.val) := by
    rw [eq_sub_iff_add_eq.mpr equation]
    abel
  rw [smallStepLift_value, difference, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos stepPositive, mul_pow] at minimum
  have pairing := smallStep_energy_correction_eq_yosida_pairing domain form nonnegative closable domainDense
    step stepPositive stepAtMostOne target.val
  nlinarith

theorem yosidaSmoothed_energy_le_closed_energy
    (target : closedDomain domain form nonnegative) (time : ℝ) (timeNonnegative : 0 ≤ time) :
    closedForm domain form nonnegative closable
      (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne
        (yosidaSemigroup domain form nonnegative closable domainDense step stepPositive stepAtMostOne time target.val)).value ≤
      closedForm domain form nonnegative closable target := by
  have comparison := BoundedSemigroupEnergy.energy_antitone
    (yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne)
    (yosidaGenerator_selfAdjoint domain form nonnegative closable domainDense step stepPositive stepAtMostOne)
    target.val timeNonnegative
  simp only [neg_zero, zero_smul, NormedSpace.exp_zero, ContinuousLinearMap.one_apply] at comparison
  rw [← yosidaSemigroup_eq_exp] at comparison
  exact (smallStepLift_energy_le_yosida_pairing domain form nonnegative closable domainDense
    step stepPositive stepAtMostOne _).trans (comparison.trans
      (yosida_pairing_le_closed_energy domain form nonnegative closable domainDense step stepPositive stepAtMostOne target))

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.smallStep_energy_correction_eq_yosida_pairing
#print axioms IGS.Sec31.QuadraticEnergySpace.yosida_pairing_le_closed_energy
#print axioms IGS.Sec31.QuadraticEnergySpace.yosidaSmoothed_energy_le_closed_energy
