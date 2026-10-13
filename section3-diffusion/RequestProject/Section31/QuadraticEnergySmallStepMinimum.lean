import RequestProject.Section31.QuadraticEnergySmallStepOperator

/-! The actual small-step resolvent minimizes step times the existing closed
energy plus squared ambient distance.  The proof uses the existing generator
and its variational identity, without constructing a second closure. -/

namespace IGS.Sec31.QuadraticEnergySpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H))
    (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1)

noncomputable def smallStepLift (forcing : H) :
    QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable)
      (closedForm_nonnegative domain form nonnegative closable) :=
  resolventLift domain form nonnegative closable
    ((resolventRangeEquiv domain form nonnegative closable domainDense).symm
      ((smallStepEquiv domain form nonnegative closable domainDense step stepPositive stepAtMostOne).symm forcing))

theorem smallStepLift_value (forcing : H) :
    ((smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value : H) =
      smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing := by
  exact congrArg (fun values : generatorDomain domain form nonnegative closable => (values : H))
    ((resolventRangeEquiv domain form nonnegative closable domainDense).apply_symm_apply
      ((smallStepEquiv domain form nonnegative closable domainDense step stepPositive stepAtMostOne).symm forcing))

theorem smallStep_variational (forcing : H)
    (test : QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable)
      (closedForm_nonnegative domain form nonnegative closable)) :
    step * (closedForm domain form nonnegative closable).associated
        (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value test.value +
      inner ℝ ((smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value : H)
        (test.value : H) = inner ℝ forcing (test.value : H) := by
  have generatorPairing := closedGenerator_variational domain form nonnegative closable domainDense
    ((resolventRangeEquiv domain form nonnegative closable domainDense).symm
      ((smallStepEquiv domain form nonnegative closable domainDense step stepPositive stepAtMostOne).symm forcing)) test
  rw [LinearEquiv.apply_symm_apply] at generatorPairing
  have solutionPairing := congrArg (fun values : H => inner ℝ values (test.value : H))
    (smallStepSolution_identity domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing)
  dsimp only at solutionPairing
  rw [inner_add_left, inner_smul_left, conj_trivial, generatorPairing] at solutionPairing
  rw [smallStepLift_value]
  change step * (closedForm domain form nonnegative closable).associated
      (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value test.value +
    inner ℝ (((smallStepEquiv domain form nonnegative closable domainDense step stepPositive stepAtMostOne).symm forcing) : H)
      (test.value : H) = inner ℝ forcing (test.value : H)
  simpa only [smallStepLift, add_comm] using solutionPairing

theorem smallStep_minimum_gap (forcing : H)
    (test : QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable)
      (closedForm_nonnegative domain form nonnegative closable)) :
    step * closedForm domain form nonnegative closable test.value + ‖(test.value : H) - forcing‖ ^ 2 =
      step * closedForm domain form nonnegative closable
        (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value +
      ‖((smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value : H) - forcing‖ ^ 2 +
      step * closedForm domain form nonnegative closable
        (test.value - (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value) +
      ‖(test.value : H) -
        ((smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value : H)‖ ^ 2 := by
  have energyDifference : closedForm domain form nonnegative closable
      (test.value - (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value) =
      closedForm domain form nonnegative closable test.value +
        closedForm domain form nonnegative closable
          (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value -
        2 * (closedForm domain form nonnegative closable).associated
          (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value test.value := by
    calc
      _ = (closedForm domain form nonnegative closable).associated
          (test.value - (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value)
          (test.value - (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value) :=
        (QuadraticMap.associated_eq_self_apply ℝ _ _).symm
      _ = _ := by
        simp only [map_sub, LinearMap.sub_apply, QuadraticMap.associated_eq_self_apply]
        rw [QuadraticMap.associated_isSymm ℝ (closedForm domain form nonnegative closable) test.value]
        ring
  have testPairing := smallStep_variational domain form nonnegative closable domainDense
    step stepPositive stepAtMostOne forcing test
  have selfPairing := smallStep_variational domain form nonnegative closable domainDense
    step stepPositive stepAtMostOne forcing
    (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing)
  rw [QuadraticMap.associated_eq_self_apply, real_inner_self_eq_norm_sq] at selfPairing
  rw [energyDifference, norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real,
    real_inner_comm forcing (test.value : H),
    real_inner_comm forcing
      ((smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value : H),
    real_inner_comm
      ((smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value : H)
      (test.value : H)]
  nlinarith

theorem smallStep_minimizes (forcing : H)
    (test : QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable)
      (closedForm_nonnegative domain form nonnegative closable)) :
    step * closedForm domain form nonnegative closable
        (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value +
      ‖((smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value : H) - forcing‖ ^ 2 ≤
      step * closedForm domain form nonnegative closable test.value + ‖(test.value : H) - forcing‖ ^ 2 := by
  rw [smallStep_minimum_gap domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing test]
  have energyNonnegative := mul_nonneg stepPositive.le
    (closedForm_nonnegative domain form nonnegative closable
      (test.value - (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value))
  nlinarith [sq_nonneg ‖(test.value : H) -
    ((smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value : H)‖]

theorem smallStep_minimizer_unique (forcing : H)
    (test : QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable)
      (closedForm_nonnegative domain form nonnegative closable))
    (minimal : step * closedForm domain form nonnegative closable test.value + ‖(test.value : H) - forcing‖ ^ 2 ≤
      step * closedForm domain form nonnegative closable
        (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value +
      ‖((smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value : H) - forcing‖ ^ 2) :
    test = smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing := by
  rw [smallStep_minimum_gap domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing test] at minimal
  have energyNonnegative := mul_nonneg stepPositive.le
    (closedForm_nonnegative domain form nonnegative closable
      (test.value - (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value))
  have differenceZero : ‖(test.value : H) -
      ((smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value : H)‖ = 0 := by
    nlinarith [norm_nonneg ((test.value : H) -
      ((smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value : H))]
  apply (equivDomain (closedDomain domain form nonnegative)
    (closedForm domain form nonnegative closable)
    (closedForm_nonnegative domain form nonnegative closable)).injective
  apply Subtype.ext
  exact sub_eq_zero.mp (norm_eq_zero.mp differenceZero)

#print axioms smallStepLift_value
#print axioms smallStep_variational
#print axioms smallStep_minimum_gap
#print axioms smallStep_minimizes
#print axioms smallStep_minimizer_unique

end IGS.Sec31.QuadraticEnergySpace
