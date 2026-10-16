import RequestProject.Section31.QuadraticEnergySmallStepOperator
import RequestProject.Section31.EIGSSelectedMoscoLower
import RequestProject.Section31.EIGSNativeFiniteResolventMinimum
import RequestProject.Section31.EIGSL2EnergyDensity
import RequestProject.Section31.EIGSNativeResolventContinuousIdentification
import RequestProject.Section31.EIGSNativeResolventReindexedSubsequence


/-! Every positive step is invertible for the existing closed generator.
For steps above one, invert `1 - (1 - 1 / step) R₁` by the Neumann series.
No new form or generator is constructed. -/

namespace IGS.Sec31.QuadraticEnergySpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)

theorem allPositiveStep_resolvent_surjective (domainDense : Dense (domain : Set H))
    (step : ℝ) (stepPositive : 0 < step) :
    Function.Surjective (fun values : generatorDomain domain form nonnegative closable =>
      (values : H) + step • closedGenerator domain form nonnegative closable domainDense values) := by
  by_cases stepAtMostOne : step ≤ 1
  · exact smallStep_resolvent_surjective domain form nonnegative closable domainDense
      step stepPositive stepAtMostOne
  have inversePositive : 0 < 1 / step := one_div_pos.mpr stepPositive
  have inverseAtMostOne : 1 / step ≤ 1 := by
    apply (div_le_iff₀ stepPositive).mpr
    simpa only [one_mul] using le_of_not_ge stepAtMostOne
  have operatorBound : ‖resolventState domain form nonnegative closable‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro forcing
    simpa only [one_mul] using resolvent_state_norm_le domain form nonnegative closable forcing
  have perturbationBound :
      ‖(1 - 1 / step) • resolventState domain form nonnegative closable‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr inverseAtMostOne)]
    nlinarith
  let inverseUnit := Units.oneSub
    ((1 - 1 / step) • resolventState domain form nonnegative closable) perturbationBound
  intro forcing
  refine ⟨resolventRangeEquiv domain form nonnegative closable domainDense
    (inverseUnit.inv ((1 / step) • forcing)), ?_⟩
  dsimp only
  rw [closedGenerator_resolvent]
  change resolventState domain form nonnegative closable (inverseUnit.inv ((1 / step) • forcing)) +
    step • (inverseUnit.inv ((1 / step) • forcing) -
      resolventState domain form nonnegative closable (inverseUnit.inv ((1 / step) • forcing))) = forcing
  have inversion := congrArg (fun operator : H →L[ℝ] H => operator ((1 / step) • forcing))
    inverseUnit.val_inv
  change inverseUnit.inv ((1 / step) • forcing) - (1 - 1 / step) •
    resolventState domain form nonnegative closable (inverseUnit.inv ((1 / step) • forcing)) =
      (1 / step) • forcing at inversion
  have scaled := congrArg (fun values : H => step • values) inversion
  dsimp only at scaled
  have cancellation : step * (1 / step) = 1 := by field_simp [ne_of_gt stepPositive]
  have coefficient : step * (1 - 1 / step) = step - 1 := by
    rw [mul_sub, mul_one, cancellation]
  rw [smul_smul, cancellation, one_smul] at scaled
  calc
    _ = step • (inverseUnit.inv ((1 / step) • forcing) - (1 - 1 / step) •
        resolventState domain form nonnegative closable (inverseUnit.inv ((1 / step) • forcing))) := by
      simp only [smul_sub, smul_smul]
      rw [coefficient]
      module
    _ = forcing := scaled

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.allPositiveStep_resolvent_surjective



/-! The bounded resolvent for every positive step and its quantitative approximation on
the actual generator domain. No semigroup existence is assumed. -/

namespace IGS.Sec31.QuadraticEnergySpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H))
    (step : ℝ) (stepPositive : 0 < step)

noncomputable def allPositiveStepEquiv :
    generatorDomain domain form nonnegative closable ≃ₗ[ℝ] H :=
  LinearEquiv.ofBijective
    ((generatorDomain domain form nonnegative closable).subtype +
      step • closedGenerator domain form nonnegative closable domainDense)
    ⟨positiveStep_resolvent_injective domain form nonnegative closable domainDense step stepPositive.le,
      allPositiveStep_resolvent_surjective domain form nonnegative closable domainDense step stepPositive⟩

theorem allPositiveStepSolution_identity (forcing : H) :
    ((allPositiveStepEquiv domain form nonnegative closable domainDense step stepPositive).symm forcing : H) +
        step • closedGenerator domain form nonnegative closable domainDense
          ((allPositiveStepEquiv domain form nonnegative closable domainDense step stepPositive).symm forcing) =
      forcing :=
  (allPositiveStepEquiv domain form nonnegative closable domainDense step stepPositive).apply_symm_apply forcing

theorem allPositiveStepSolution_norm (forcing : H) :
    ‖((allPositiveStepEquiv domain form nonnegative closable domainDense step stepPositive).symm forcing : H)‖ ≤
      ‖forcing‖ := by
  have bound := positiveStep_resolvent_norm_bound domain form nonnegative closable domainDense step stepPositive.le
    ((allPositiveStepEquiv domain form nonnegative closable domainDense step stepPositive).symm forcing)
  rwa [allPositiveStepSolution_identity] at bound

noncomputable def allPositiveStepResolvent : H →L[ℝ] H :=
  ((generatorDomain domain form nonnegative closable).subtype.comp
    (allPositiveStepEquiv domain form nonnegative closable domainDense step stepPositive).symm.toLinearMap).mkContinuous 1
    (fun forcing => by simpa only [one_mul] using
      allPositiveStepSolution_norm domain form nonnegative closable domainDense step stepPositive forcing)

theorem allPositiveStepResolvent_norm (forcing : H) :
    ‖allPositiveStepResolvent domain form nonnegative closable domainDense step stepPositive forcing‖ ≤ ‖forcing‖ :=
  allPositiveStepSolution_norm domain form nonnegative closable domainDense step stepPositive forcing

theorem allPositiveStepResolvent_operator_norm :
    ‖allPositiveStepResolvent domain form nonnegative closable domainDense step stepPositive‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro forcing
  simpa only [one_mul] using
    allPositiveStepResolvent_norm domain form nonnegative closable domainDense step stepPositive forcing

theorem allPositiveStepResolvent_inverse (values : generatorDomain domain form nonnegative closable) :
    allPositiveStepResolvent domain form nonnegative closable domainDense step stepPositive
        ((values : H) + step • closedGenerator domain form nonnegative closable domainDense values) =
      (values : H) := by
  exact congrArg (fun point : generatorDomain domain form nonnegative closable => (point : H))
    ((allPositiveStepEquiv domain form nonnegative closable domainDense step stepPositive).symm_apply_apply values)

theorem allPositiveStepResolvent_domain_error (values : generatorDomain domain form nonnegative closable) :
    ‖(values : H) - allPositiveStepResolvent domain form nonnegative closable domainDense step stepPositive values‖ ≤
      step * ‖closedGenerator domain form nonnegative closable domainDense values‖ := by
  have identity := allPositiveStepResolvent_inverse domain form nonnegative closable domainDense step stepPositive values
  rw [map_add, map_smul] at identity
  have difference : (values : H) -
      allPositiveStepResolvent domain form nonnegative closable domainDense step stepPositive values =
      step • allPositiveStepResolvent domain form nonnegative closable domainDense step stepPositive
        (closedGenerator domain form nonnegative closable domainDense values) := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using identity.symm
  rw [difference, norm_smul, Real.norm_eq_abs, abs_of_pos stepPositive]
  exact mul_le_mul_of_nonneg_left
    (allPositiveStepResolvent_norm domain form nonnegative closable domainDense step stepPositive _) stepPositive.le

theorem allPositiveStepResolvent_eq_smallStepResolvent (stepAtMostOne : step ≤ 1) :
    allPositiveStepResolvent domain form nonnegative closable domainDense step stepPositive =
      smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne := by
  ext forcing
  have solutionEquality := positiveStep_resolvent_injective domain form nonnegative closable domainDense
    step stepPositive.le
    (allPositiveStepSolution_identity domain form nonnegative closable domainDense step stepPositive forcing |>.trans
      (smallStepSolution_identity domain form nonnegative closable domainDense
        step stepPositive stepAtMostOne forcing).symm)
  exact congrArg (fun values : generatorDomain domain form nonnegative closable => (values : H)) solutionEquality

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.allPositiveStepSolution_identity
#print axioms IGS.Sec31.QuadraticEnergySpace.allPositiveStepResolvent_norm
#print axioms IGS.Sec31.QuadraticEnergySpace.allPositiveStepResolvent_operator_norm
#print axioms IGS.Sec31.QuadraticEnergySpace.allPositiveStepResolvent_inverse
#print axioms IGS.Sec31.QuadraticEnergySpace.allPositiveStepResolvent_domain_error
#print axioms IGS.Sec31.QuadraticEnergySpace.allPositiveStepResolvent_eq_smallStepResolvent




/-! The actual positive-step resolvent minimizes step times the existing closed
energy plus squared ambient distance.  The proof uses the existing generator
and its variational identity, without constructing a second closure. -/

namespace IGS.Sec31.QuadraticEnergySpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H))
    (step : ℝ) (stepPositive : 0 < step)

noncomputable def allPositiveStepLift (forcing : H) :
    QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable)
      (closedForm_nonnegative domain form nonnegative closable) :=
  resolventLift domain form nonnegative closable
    ((resolventRangeEquiv domain form nonnegative closable domainDense).symm
      ((allPositiveStepEquiv domain form nonnegative closable domainDense step stepPositive).symm forcing))

theorem allPositiveStepLift_value (forcing : H) :
    ((allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value : H) =
      allPositiveStepResolvent domain form nonnegative closable domainDense step stepPositive forcing := by
  exact congrArg (fun values : generatorDomain domain form nonnegative closable => (values : H))
    ((resolventRangeEquiv domain form nonnegative closable domainDense).apply_symm_apply
      ((allPositiveStepEquiv domain form nonnegative closable domainDense step stepPositive).symm forcing))

theorem allPositiveStep_variational (forcing : H)
    (test : QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable)
      (closedForm_nonnegative domain form nonnegative closable)) :
    step * (closedForm domain form nonnegative closable).associated
        (allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value test.value +
      inner ℝ ((allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value : H)
        (test.value : H) = inner ℝ forcing (test.value : H) := by
  have generatorPairing := closedGenerator_variational domain form nonnegative closable domainDense
    ((resolventRangeEquiv domain form nonnegative closable domainDense).symm
      ((allPositiveStepEquiv domain form nonnegative closable domainDense step stepPositive).symm forcing)) test
  rw [LinearEquiv.apply_symm_apply] at generatorPairing
  have solutionPairing := congrArg (fun values : H => inner ℝ values (test.value : H))
    (allPositiveStepSolution_identity domain form nonnegative closable domainDense step stepPositive forcing)
  dsimp only at solutionPairing
  rw [inner_add_left, inner_smul_left, conj_trivial, generatorPairing] at solutionPairing
  rw [allPositiveStepLift_value]
  change step * (closedForm domain form nonnegative closable).associated
      (allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value test.value +
    inner ℝ (((allPositiveStepEquiv domain form nonnegative closable domainDense step stepPositive).symm forcing) : H)
      (test.value : H) = inner ℝ forcing (test.value : H)
  simpa only [allPositiveStepLift, add_comm] using solutionPairing

theorem allPositiveStep_minimum_gap (forcing : H)
    (test : QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable)
      (closedForm_nonnegative domain form nonnegative closable)) :
    step * closedForm domain form nonnegative closable test.value + ‖(test.value : H) - forcing‖ ^ 2 =
      step * closedForm domain form nonnegative closable
        (allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value +
      ‖((allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value : H) - forcing‖ ^ 2 +
      step * closedForm domain form nonnegative closable
        (test.value - (allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value) +
      ‖(test.value : H) -
        ((allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value : H)‖ ^ 2 := by
  have energyDifference : closedForm domain form nonnegative closable
      (test.value - (allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value) =
      closedForm domain form nonnegative closable test.value +
        closedForm domain form nonnegative closable
          (allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value -
        2 * (closedForm domain form nonnegative closable).associated
          (allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value test.value := by
    calc
      _ = (closedForm domain form nonnegative closable).associated
          (test.value - (allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value)
          (test.value - (allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value) :=
        (QuadraticMap.associated_eq_self_apply ℝ _ _).symm
      _ = _ := by
        simp only [map_sub, LinearMap.sub_apply, QuadraticMap.associated_eq_self_apply]
        rw [QuadraticMap.associated_isSymm ℝ (closedForm domain form nonnegative closable) test.value]
        ring
  have testPairing := allPositiveStep_variational domain form nonnegative closable domainDense
    step stepPositive forcing test
  have selfPairing := allPositiveStep_variational domain form nonnegative closable domainDense
    step stepPositive forcing
    (allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing)
  rw [QuadraticMap.associated_eq_self_apply, real_inner_self_eq_norm_sq] at selfPairing
  rw [energyDifference, norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real,
    real_inner_comm forcing (test.value : H),
    real_inner_comm forcing
      ((allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value : H),
    real_inner_comm
      ((allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value : H)
      (test.value : H)]
  nlinarith

theorem allPositiveStep_minimizes (forcing : H)
    (test : QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable)
      (closedForm_nonnegative domain form nonnegative closable)) :
    step * closedForm domain form nonnegative closable
        (allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value +
      ‖((allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value : H) - forcing‖ ^ 2 ≤
      step * closedForm domain form nonnegative closable test.value + ‖(test.value : H) - forcing‖ ^ 2 := by
  rw [allPositiveStep_minimum_gap domain form nonnegative closable domainDense step stepPositive forcing test]
  have energyNonnegative := mul_nonneg stepPositive.le
    (closedForm_nonnegative domain form nonnegative closable
      (test.value - (allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value))
  nlinarith [sq_nonneg ‖(test.value : H) -
    ((allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value : H)‖]

theorem allPositiveStep_minimizer_unique (forcing : H)
    (test : QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable)
      (closedForm_nonnegative domain form nonnegative closable))
    (minimal : step * closedForm domain form nonnegative closable test.value + ‖(test.value : H) - forcing‖ ^ 2 ≤
      step * closedForm domain form nonnegative closable
        (allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value +
      ‖((allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value : H) - forcing‖ ^ 2) :
    test = allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing := by
  rw [allPositiveStep_minimum_gap domain form nonnegative closable domainDense step stepPositive forcing test] at minimal
  have energyNonnegative := mul_nonneg stepPositive.le
    (closedForm_nonnegative domain form nonnegative closable
      (test.value - (allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value))
  have differenceZero : ‖(test.value : H) -
      ((allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value : H)‖ = 0 := by
    nlinarith [norm_nonneg ((test.value : H) -
      ((allPositiveStepLift domain form nonnegative closable domainDense step stepPositive forcing).value : H))]
  apply (equivDomain (closedDomain domain form nonnegative)
    (closedForm domain form nonnegative closable)
    (closedForm_nonnegative domain form nonnegative closable)).injective
  apply Subtype.ext
  exact sub_eq_zero.mp (norm_eq_zero.mp differenceZero)

#print axioms allPositiveStepLift_value
#print axioms allPositiveStep_variational
#print axioms allPositiveStep_minimum_gap
#print axioms allPositiveStep_minimizes
#print axioms allPositiveStep_minimizer_unique

end IGS.Sec31.QuadraticEnergySpace




/-! Actual native finite resolvents converge strongly to the actual closed-form
resolvent. The proof uses genuine forcing Strong convergence, the proved native
compactness and selected lower bound, exact joint recovery, and actual minimum
gaps. Every step is positive, with no upper bound. The target is the inverse of the same closed generator. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped ENNReal

set_option maxHeartbeats 4000000

private theorem b1_objective_le_of_energy_liminf
    (step : ℝ) (stepPositive : 0 < step)
    (energies recoveryEnergies solutionDistances recoveryDistances : ℕ → ℝ)
    (limitEnergy recoveryEnergy solutionDistance recoveryDistance : ℝ)
    (energiesNonnegative : ∀ index, 0 ≤ energies index)
    (lower : ENNReal.ofReal limitEnergy ≤ liminf (fun index => ENNReal.ofReal (energies index)) atTop)
    (recoveryLimit : Tendsto recoveryEnergies atTop (nhds recoveryEnergy))
    (solutionDistanceLimit : Tendsto solutionDistances atTop (nhds solutionDistance))
    (recoveryDistanceLimit : Tendsto recoveryDistances atTop (nhds recoveryDistance))
    (minimal : ∀ index, step * energies index + solutionDistances index ≤
      step * recoveryEnergies index + recoveryDistances index) :
    step * limitEnergy + solutionDistance ≤ step * recoveryEnergy + recoveryDistance := by
  have upperLimit : Tendsto
      (fun index => (step * recoveryEnergies index + recoveryDistances index - solutionDistances index) / step)
      atTop (nhds ((step * recoveryEnergy + recoveryDistance - solutionDistance) / step)) :=
    (((tendsto_const_nhds.mul recoveryLimit).add recoveryDistanceLimit).sub solutionDistanceLimit).div_const step
  have pointwise : ∀ index, energies index ≤
      (step * recoveryEnergies index + recoveryDistances index - solutionDistances index) / step := by
    intro index
    apply (le_div_iff₀ stepPositive).mpr
    nlinarith [minimal index]
  have upperNonnegative : 0 ≤ (step * recoveryEnergy + recoveryDistance - solutionDistance) / step := by
    apply ge_of_tendsto upperLimit
    exact Eventually.of_forall fun index => (energiesNonnegative index).trans (pointwise index)
  have upperExtended := ENNReal.continuous_ofReal.continuousAt.tendsto.comp upperLimit
  have upperComparison := limsup_le_limsup (f := atTop)
    (Eventually.of_forall fun index => ENNReal.ofReal_le_ofReal (pointwise index))
  have realComparison : limitEnergy ≤ (step * recoveryEnergy + recoveryDistance - solutionDistance) / step :=
    (ENNReal.ofReal_le_ofReal_iff upperNonnegative).mp
      (lower.trans ((liminf_le_limsup).trans (upperComparison.trans upperExtended.limsup_eq.le)))
  have scaled := (le_div_iff₀ stepPositive).mp realComparison
  nlinarith

variable {K : ℕ}

theorem b1_xiNativeFiniteResolvent_strong_limit (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector))) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
      intro sequence energyCauchy ambientZero
      exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
        mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
        (by simpa using ambientZero.norm)
    ∀ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass))),
      ∀ (step : ℝ) (stepPositive : 0 < step)
        (forcing : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
        (target : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass)),
      core.Strong forcing target →
      core.Strong (fun level => xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive (forcing level))
        (QuadraticEnergySpace.allPositiveStepResolvent originalDomain originalForm nonnegative closable
          originalDense step stepPositive target) := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  have closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  dsimp only
  intro originalDense step stepPositive forcing target forcingStrong
  let solutions := fun level => xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive (forcing level)
  let targetLift := QuadraticEnergySpace.allPositiveStepLift originalDomain originalForm nonnegative closable
    originalDense step stepPositive target
  have targetLiftImage : (targetLift.value : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass)) =
      QuadraticEnergySpace.allPositiveStepResolvent originalDomain originalForm nonnegative closable
        originalDense step stepPositive target :=
    QuadraticEnergySpace.allPositiveStepLift_value originalDomain originalForm nonnegative closable originalDense
      step stepPositive target
  obtain ⟨recovery, recoveryStrong, recoveryEnergy⟩ :=
    exists_xiClosed_native_joint_recovery_fixed_normalization_without_primitive system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive normalizedConvergence targetLift.value
  have recoveryStrongResolvent : core.Strong recovery
      (QuadraticEnergySpace.allPositiveStepResolvent originalDomain originalForm nonnegative closable
        originalDense step stepPositive target) := by
    simpa only [targetLiftImage] using recoveryStrong
  obtain ⟨normBound, forcingNormBound⟩ := core.weak_norm_bounded (core.strong_implies_weak forcingStrong)
  have normBoundNonnegative : 0 ≤ normBound := (norm_nonneg (forcing 0)).trans (forcingNormBound 0)
  have solutionNormBound : ∀ level, ‖solutions level‖ ≤ normBound := by
    intro level
    exact ((xiNativeFiniteResolvent_properties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive).1
        (forcing level)).2.2 |>.trans (forcingNormBound level)
  have solutionEnergyBound : ∀ level,
      xiNativeScaledUnitEnergy system mass resistanceRate normalization level (solutions level) ≤ normBound ^ 2 / step := by
    intro level
    have minimal := xiNativeFiniteResolvent_minimizes system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive (forcing level) 0
    simp only [xiNativeScaledUnitEnergy_zero system rulesConnected, mul_zero, zero_sub, norm_neg, zero_add] at minimal
    change step * xiNativeScaledUnitEnergy system mass resistanceRate normalization level (solutions level) +
      ‖solutions level - forcing level‖ ^ 2 ≤ ‖forcing level‖ ^ 2 at minimal
    have squareBound := pow_le_pow_left₀ (norm_nonneg (forcing level)) (forcingNormBound level) 2
    apply (le_div_iff₀ stepPositive).mpr
    nlinarith [sq_nonneg ‖solutions level - forcing level‖]
  have subsequentialLimit : ∀ (levels : ℕ → ℕ) (levelsStrict : StrictMono levels),
      ∃ selection : ℕ → ℕ, ∃ selectionStrict : StrictMono selection,
        (core.reindex (levels ∘ selection) (levelsStrict.comp selectionStrict).tendsto_atTop).Strong
          (fun index => solutions (levels (selection index)))
          (QuadraticEnergySpace.allPositiveStepResolvent originalDomain originalForm nonnegative closable
            originalDense step stepPositive target) := by
    intro levels levelsStrict
    obtain ⟨selection, selectionStrict, limit, strongConvergence, limitBound⟩ :=
      exists_xiNativeEnergy_closed_subsequence system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive
        normalizedConvergence levels levelsStrict solutions normBound (normBound ^ 2 / step)
        (fun index => solutionNormBound (levels index)) (fun index => solutionEnergyBound (levels index))
    have limitMembership : limit ∈ QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative :=
      (QuadraticEnergySpace.closedExtendedEnergy_ne_top_iff originalDomain originalForm nonnegative closable limit).mp
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top limitBound)
    have lower := xiClosedExtendedEnergy_selected_mosco_lower system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive
      normalizedConvergence (levels ∘ selection) (levelsStrict.comp selectionStrict) solutions limit
      ((core.reindex (levels ∘ selection) (levelsStrict.comp selectionStrict).tendsto_atTop).strong_implies_weak strongConvergence)
    rw [QuadraticEnergySpace.closedExtendedEnergy_of_mem originalDomain originalForm nonnegative closable limit limitMembership] at lower
    simp only [Function.comp_def] at lower
    have selectedForcing := core.strong_reindex (levels ∘ selection)
      (levelsStrict.comp selectionStrict).tendsto_atTop forcingStrong
    have selectedRecovery := core.strong_reindex (levels ∘ selection)
      (levelsStrict.comp selectionStrict).tendsto_atTop recoveryStrong
    have solutionDistance := (core.reindex (levels ∘ selection)
      (levelsStrict.comp selectionStrict).tendsto_atTop).strong_norm_sub_tendsto strongConvergence selectedForcing
    have recoveryDistance := (core.reindex (levels ∘ selection)
      (levelsStrict.comp selectionStrict).tendsto_atTop).strong_norm_sub_tendsto selectedRecovery selectedForcing
    have limitMinimal := b1_objective_le_of_energy_liminf step stepPositive
      (fun index => xiNativeScaledUnitEnergy system mass resistanceRate normalization (levels (selection index))
        (solutions (levels (selection index))))
      (fun index => xiNativeScaledUnitEnergy system mass resistanceRate normalization (levels (selection index))
        (recovery (levels (selection index))))
      (fun index => ‖solutions (levels (selection index)) - forcing (levels (selection index))‖ ^ 2)
      (fun index => ‖recovery (levels (selection index)) - forcing (levels (selection index))‖ ^ 2)
      (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable ⟨limit, limitMembership⟩)
      (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable targetLift.value)
      (‖limit - target‖ ^ 2) (‖(targetLift.value : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass)) - target‖ ^ 2)
      (fun index => xiNativeScaledUnitEnergy_nonnegative system mass resistanceRate normalization ratePositive.le
        normalizationPositive.le _ _)
      lower (recoveryEnergy.comp (levelsStrict.comp selectionStrict).tendsto_atTop)
      (solutionDistance.pow 2) (recoveryDistance.pow 2)
      (fun index => xiNativeFiniteResolvent_minimizes system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass (levels (selection index)) resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive
        (forcing (levels (selection index))) (recovery (levels (selection index))))
    let closedLimit : QuadraticEnergySpace
        (QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative)
        (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable)
        (QuadraticEnergySpace.closedForm_nonnegative originalDomain originalForm nonnegative closable) :=
      ⟨⟨limit, limitMembership⟩⟩
    have unique := QuadraticEnergySpace.allPositiveStep_minimizer_unique originalDomain originalForm nonnegative closable
      originalDense step stepPositive target closedLimit limitMinimal
    have limitEquality : limit = QuadraticEnergySpace.allPositiveStepResolvent originalDomain originalForm nonnegative closable
        originalDense step stepPositive target := by
      have equality := congrArg
        (fun values : QuadraticEnergySpace
          (QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative)
          (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable)
          (QuadraticEnergySpace.closedForm_nonnegative originalDomain originalForm nonnegative closable) =>
          (values.value : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass))) unique
      simpa only [closedLimit, targetLiftImage, QuadraticEnergySpace.allPositiveStepLift_value] using equality
    refine ⟨selection, selectionStrict, ?_⟩
    simpa only [limitEquality] using strongConvergence
  apply core.strong_of_norm_sub_tendsto_zero solutions recovery _ recoveryStrongResolvent
  apply Metric.tendsto_nhds.mpr
  intro tolerance tolerancePositive
  simp only [Real.dist_eq, sub_zero, abs_norm]
  by_contra notEventually
  have frequent : ∃ᶠ level in atTop, tolerance ≤ ‖solutions level - recovery level‖ :=
    (Filter.not_eventually.mp notEventually).mono fun _ contrary => le_of_not_gt contrary
  obtain ⟨levels, levelsStrict, bad⟩ := extraction_forall_of_frequently (fun _ : ℕ => frequent)
  obtain ⟨selection, selectionStrict, selectedStrong⟩ := subsequentialLimit levels levelsStrict
  have differenceLimit := (core.reindex (levels ∘ selection)
    (levelsStrict.comp selectionStrict).tendsto_atTop).strong_norm_sub_tendsto selectedStrong
    (core.strong_reindex (levels ∘ selection) (levelsStrict.comp selectionStrict).tendsto_atTop recoveryStrongResolvent)
  have differenceZero : Tendsto (fun index => ‖solutions (levels (selection index)) - recovery (levels (selection index))‖)
      atTop (nhds 0) := by
    simpa only [Function.comp_def, sub_self, norm_zero] using differenceLimit
  obtain ⟨index, small⟩ := (differenceZero.eventually_lt_const tolerancePositive).exists
  exact (not_le_of_gt small) (bad (selection index))

theorem b1_exists_xiNativeFiniteResolventStrong_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
    let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    let oneColourDistance : K = 1 → ∀ colour,
        2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
      intro _ colour
      exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
        (system.plant_ne colour) (plantingNonadjacent colour)
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ ratePositive : 0 < resistanceRate, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (nhds (normalization • resistanceVector)) ∧
      let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive
      let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
        intro sequence energyCauchy ambientZero
        exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
          mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
          (by simpa using ambientZero.norm)
      ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass))),
        ∀ (step : ℝ) (stepPositive : 0 < step)
          (forcing : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
          (target : Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass)),
        core.Strong forcing target →
        core.Strong (fun level => xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive (forcing level))
          (QuadraticEnergySpace.allPositiveStepResolvent originalDomain originalForm nonnegative closable
            originalDense step stepPositive target) := by
  classical
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
      originalDense, originalNonnegative⟩ :=
    exists_xiDenseLpQuadraticEnergy_of_rules system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  obtain ⟨normalization, normalizationPositive, normalizedConvergence⟩ :=
    exists_normalized_resistance_limit_of_positive_eigenpair system rulesConnected distancePositive resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, originalDense, ?_⟩
  exact b1_xiNativeFiniteResolvent_strong_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence originalDense

end EIGS

#print axioms EIGS.b1_xiNativeFiniteResolvent_strong_limit

#print axioms EIGS.b1_exists_xiNativeFiniteResolventStrong_of_rules



namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000
variable {K : ℕ}
def B1NativeContinuousResolventProperties (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization) : Prop :=
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass))),
    ∀ (step : ℝ) (stepPositive : 0 < step)
      (function : C(parameters.LimitSpace, ℝ)),
    let forcing := fun level => core.restrict level (BoundedContinuousFunction.mkOfCompact function)
    let solution := fun level => xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive (forcing level)
    let closedSolution := QuadraticEnergySpace.allPositiveStepResolvent originalDomain originalForm nonnegative closable
      originalDense step stepPositive (core.embed (BoundedContinuousFunction.mkOfCompact function))
    ∃ limit : C(parameters.LimitSpace, ℝ),
      core.embed (BoundedContinuousFunction.mkOfCompact limit) = closedSolution ∧
      (∀ other : C(parameters.LimitSpace, ℝ),
        core.embed (BoundedContinuousFunction.mkOfCompact other) = closedSolution → other = limit) ∧
      ∃ selection : ℕ → ℕ, StrictMono selection ∧
        Tendsto (fun index => ‖fun vertex : XiVtx system (selection index) =>
          solution (selection index) vertex - limit (parameters.vertexEmbedding (selection index) vertex)‖)
          atTop (nhds 0)

theorem b1_exists_xiNativeContinuousResolvent_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
      ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (nhds (normalization • resistanceVector)) ∧
      B1NativeContinuousResolventProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
      originalDense, originalNonnegative⟩ :=
    exists_xiDenseLpQuadraticEnergy_of_rules system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  obtain ⟨normalization, normalizationPositive, normalizedConvergence⟩ :=
    exists_normalized_resistance_limit_of_positive_eigenpair system rulesConnected distancePositive resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  dsimp only [B1NativeContinuousResolventProperties]
  refine ⟨originalDense, ?_⟩
  intro step stepPositive function
  let forcing := fun level => core.restrict level (BoundedContinuousFunction.mkOfCompact function)
  let solution := fun level => xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive (forcing level)
  have forcingBound (level : ℕ) :
      ‖fun vertex : XiVtx system level => forcing level vertex‖ ≤ ‖BoundedContinuousFunction.mkOfCompact function‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro vertex
    dsimp only [forcing]
    rw [xiSpeedL2Core_restrict_eq_finiteSpeedL2, xiFiniteSpeedL2_apply system rulesConnected]
    exact (BoundedContinuousFunction.mkOfCompact function).norm_coe_le_norm _
  have rateEquality := system.resistanceSpectralRadius_eq_of_positive_eigenpair rulesConnected distancePositive
    ratePositive vectorPositive (funext renormalizationEigenpair)
  obtain ⟨selection, selectionStrict, limit, uniformConvergence⟩ :
      ∃ selection : ℕ → ℕ, StrictMono selection ∧ ∃ limit : C(parameters.LimitSpace, ℝ),
        Tendsto (fun index => ‖fun vertex : XiVtx system (selection index) =>
          solution (selection index) vertex - limit (parameters.vertexEmbedding (selection index) vertex)‖)
          atTop (nhds 0) := by
    simpa only [solution, rateEquality] using
      xiNativeFiniteResolvent_exists_uniform_subsequence system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive mass normalization normalizationPositive step stepPositive forcing
        ‖BoundedContinuousFunction.mkOfCompact function‖ (norm_nonneg _) forcingBound
  have uniformStrong := xiNativeL2_strong_of_uniform_subsequence system rulesConnected parameters
    distanceGreaterThanOne mass selection selectionStrict solution limit uniformConvergence
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  have nativeStrong := b1_xiNativeFiniteResolvent_strong_limit system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence originalDense step stepPositive
    forcing (core.embed (BoundedContinuousFunction.mkOfCompact function))
    (core.strong_restrict (BoundedContinuousFunction.mkOfCompact function))
  have sameClass := (core.reindex selection selectionStrict.tendsto_atTop).strong_limit_unique
    (fun index => solution (selection index)) _ _ uniformStrong
    (core.strong_reindex selection selectionStrict.tendsto_atTop nativeStrong)
  refine ⟨limit, sameClass, ?_, selection, selectionStrict, uniformConvergence⟩
  intro other otherClass
  apply xiContinuousL2Map_injective system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  change core.embed (BoundedContinuousFunction.mkOfCompact other) =
    core.embed (BoundedContinuousFunction.mkOfCompact limit)
  exact otherClass.trans sameClass.symm

end
end EIGS

#print axioms EIGS.b1_exists_xiNativeContinuousResolvent_of_rules



/-! Full-sequence uniform convergence of actual finite resolvents of continuous
forcing. Every selected set of levels admits a further uniform limit; the
actual Strong closed-resolvent limit and full support identify it uniquely.
No subsequential compactness or target uniform convergence is assumed in the
original-rule result. Every positive step is allowed, with no upper bound. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

variable {K : ℕ}

def B1NativeUniformResolventProperties (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization) : Prop :=
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass))),
    ∀ (step : ℝ) (stepPositive : 0 < step)
      (function : C(parameters.LimitSpace, ℝ)),
    let forcing := fun level => core.restrict level (BoundedContinuousFunction.mkOfCompact function)
    let solution := fun level => xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive (forcing level)
    let closedSolution := QuadraticEnergySpace.allPositiveStepResolvent originalDomain originalForm nonnegative closable
      originalDense step stepPositive (core.embed (BoundedContinuousFunction.mkOfCompact function))
    ∃ limit : C(parameters.LimitSpace, ℝ),
      core.embed (BoundedContinuousFunction.mkOfCompact limit) = closedSolution ∧
      (∀ other : C(parameters.LimitSpace, ℝ),
        core.embed (BoundedContinuousFunction.mkOfCompact other) = closedSolution → other = limit) ∧
      Tendsto (fun level => ‖fun vertex : XiVtx system level =>
        solution level vertex - limit (parameters.vertexEmbedding level vertex)‖) atTop (nhds 0)

theorem b1_xiNativeUniformResolventProperties_of_continuous (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector)))
    (continuousProperties : B1NativeContinuousResolventProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive) :
    B1NativeUniformResolventProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  dsimp only [B1NativeContinuousResolventProperties, B1NativeUniformResolventProperties]
    at continuousProperties ⊢
  obtain ⟨originalDense, continuousProperties⟩ := continuousProperties
  refine ⟨originalDense, ?_⟩
  intro step stepPositive function
  obtain ⟨limit, sameClass, unique, uniformSubsequence⟩ :=
    continuousProperties step stepPositive function
  refine ⟨limit, sameClass, unique, ?_⟩
  let forcing := fun level => core.restrict level (BoundedContinuousFunction.mkOfCompact function)
  let solution := fun level => xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive (forcing level)
  have forcingBound (level : ℕ) :
      ‖fun vertex : XiVtx system level => forcing level vertex‖ ≤ ‖BoundedContinuousFunction.mkOfCompact function‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro vertex
    dsimp only [forcing]
    rw [xiSpeedL2Core_restrict_eq_finiteSpeedL2, xiFiniteSpeedL2_apply system rulesConnected]
    exact (BoundedContinuousFunction.mkOfCompact function).norm_coe_le_norm _
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  have nativeStrong := b1_xiNativeFiniteResolvent_strong_limit system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence originalDense step stepPositive
    forcing (core.embed (BoundedContinuousFunction.mkOfCompact function))
    (core.strong_restrict (BoundedContinuousFunction.mkOfCompact function))
  rw [← sameClass] at nativeStrong
  apply tendsto_of_every_strict_subsequence_has_further_limit
    (fun level => ‖fun vertex : XiVtx system level =>
      solution level vertex - limit (parameters.vertexEmbedding level vertex)‖) 0
  intro levels levelsStrict
  have rateEquality := system.resistanceSpectralRadius_eq_of_positive_eigenpair rulesConnected distancePositive
    ratePositive vectorPositive (funext renormalizationEigenpair)
  obtain ⟨selection, selectionStrict, other, otherUniform⟩ :
      ∃ selection : ℕ → ℕ, StrictMono selection ∧ ∃ other : C(parameters.LimitSpace, ℝ),
        Tendsto (fun index => ‖fun vertex : XiVtx system (levels (selection index)) =>
          solution (levels (selection index)) vertex - other (parameters.vertexEmbedding (levels (selection index)) vertex)‖)
          atTop (nhds 0) := by
    simpa only [solution, rateEquality] using
      xiNativeFiniteResolvent_exists_uniform_subsequence_along system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive mass normalization normalizationPositive step stepPositive forcing
        ‖BoundedContinuousFunction.mkOfCompact function‖ (norm_nonneg _) forcingBound levels levelsStrict
  have composedStrict : StrictMono (levels ∘ selection) := levelsStrict.comp selectionStrict
  have otherStrong := xiNativeL2_strong_of_uniform_subsequence system rulesConnected parameters
    distanceGreaterThanOne mass (levels ∘ selection) composedStrict solution other otherUniform
  have selectedNativeStrong := core.strong_reindex (levels ∘ selection) composedStrict.tendsto_atTop
    (sequence := solution) (limit := core.embed (BoundedContinuousFunction.mkOfCompact limit)) nativeStrong
  have otherClass := (core.reindex (levels ∘ selection) composedStrict.tendsto_atTop).strong_limit_unique
    (fun index => solution ((levels ∘ selection) index)) _ _ otherStrong selectedNativeStrong
  have otherEquality : other = limit := unique other (otherClass.trans sameClass)
  refine ⟨selection, ?_⟩
  simpa only [otherEquality] using otherUniform

theorem b1_exists_xiNativeUniformResolvent_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
      ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (nhds (normalization • resistanceVector)) ∧
      B1NativeUniformResolventProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, continuousProperties⟩ :=
    b1_exists_xiNativeContinuousResolvent_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact b1_xiNativeUniformResolventProperties_of_continuous system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair normalization normalizationPositive normalizedConvergence continuousProperties

end
end EIGS

#print axioms EIGS.b1_xiNativeUniformResolventProperties_of_continuous
#print axioms EIGS.b1_exists_xiNativeUniformResolvent_of_rules



namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000
variable {K : ℕ}
def B1NativeUniformLambdaResolventProperties (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization) : Prop :=
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass))),
    ∀ (lambda : ℝ) (lambdaPositive : 0 < lambda)
      (function : C(parameters.LimitSpace, ℝ)),
    let step := 1 / lambda
    let stepPositive : 0 < step := one_div_pos.mpr lambdaPositive
    let forcing := fun level => core.restrict level (BoundedContinuousFunction.mkOfCompact function)
    let solution := fun level vertex => step * (xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive (forcing level) vertex)
    let closedSolution := step • QuadraticEnergySpace.allPositiveStepResolvent originalDomain originalForm nonnegative closable
      originalDense step stepPositive (core.embed (BoundedContinuousFunction.mkOfCompact function))
    ∃ limit : C(parameters.LimitSpace, ℝ),
      core.embed (BoundedContinuousFunction.mkOfCompact limit) = closedSolution ∧
      (∀ other : C(parameters.LimitSpace, ℝ),
        core.embed (BoundedContinuousFunction.mkOfCompact other) = closedSolution → other = limit) ∧
      Tendsto (fun level => ‖fun vertex : XiVtx system level =>
        solution level vertex - limit (parameters.vertexEmbedding level vertex)‖) atTop (nhds 0)

theorem b1_uniformLambdaResolvent_of_uniformPositiveStep (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (properties : B1NativeUniformResolventProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive) :
    B1NativeUniformLambdaResolventProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  dsimp only [B1NativeUniformResolventProperties, B1NativeUniformLambdaResolventProperties] at properties ⊢
  obtain ⟨originalDense, properties⟩ := properties
  refine ⟨originalDense, ?_⟩
  intro lambda lambdaPositive function
  obtain ⟨limit, sameClass, unique, uniform⟩ := properties (1 / lambda) (one_div_pos.mpr lambdaPositive) function
  refine ⟨(1 / lambda) • limit, ?_, ?_, ?_⟩
  · change core.embed (BoundedContinuousFunction.mkOfCompact ((1 / lambda) • limit)) = _
    rw [show BoundedContinuousFunction.mkOfCompact ((1 / lambda) • limit) =
      (1 / lambda) • BoundedContinuousFunction.mkOfCompact limit from rfl, map_smul]
    exact congrArg (fun values => (1 / lambda) • values) sameClass
  · intro other otherClass
    apply xiContinuousL2Map_injective system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    change core.embed (BoundedContinuousFunction.mkOfCompact other) =
      core.embed (BoundedContinuousFunction.mkOfCompact ((1 / lambda) • limit))
    rw [show BoundedContinuousFunction.mkOfCompact ((1 / lambda) • limit) =
      (1 / lambda) • BoundedContinuousFunction.mkOfCompact limit from rfl, map_smul, sameClass]
    exact otherClass
  · have scaled := uniform.const_mul |1 / lambda|
    simp only [mul_zero] at scaled
    convert scaled using 1
    ext level
    rw [← Real.norm_eq_abs, ← norm_smul]
    congr 1
    ext vertex
    simp only [Pi.smul_apply, ContinuousMap.smul_apply, smul_eq_mul]
    ring

theorem b1_exists_xiNativeUniformLambdaResolvent_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
      ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (nhds (normalization • resistanceVector)) ∧
      B1NativeUniformLambdaResolventProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, properties⟩ :=
    b1_exists_xiNativeUniformResolvent_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact b1_uniformLambdaResolvent_of_uniformPositiveStep system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair normalization normalizationPositive properties
end
end EIGS

#print axioms EIGS.b1_uniformLambdaResolvent_of_uniformPositiveStep




#print axioms EIGS.b1_exists_xiNativeUniformLambdaResolvent_of_rules

