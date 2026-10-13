import RequestProject.Section31.QuadraticEnergySmallStepMinimum
import Mathlib.MeasureTheory.Function.L2Space

/-! A closed-energy contraction fixing the forcing also fixes the actual small-step
resolvent, by the proved unique minimum.  The L2 consequences are positivity
and preservation of the almost-everywhere unit interval. -/

namespace IGS.Sec31.QuadraticEnergySpace

open MeasureTheory

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H))
    (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1)

theorem smallStep_resolvent_fixed_of_contraction (contraction : H → H)
    (distanceBound : ∀ first second, ‖contraction first - contraction second‖ ≤ ‖first - second‖)
    (energyBound : ∀ target : closedDomain domain form nonnegative,
      ∃ membership : contraction target.val ∈ closedDomain domain form nonnegative,
        closedForm domain form nonnegative closable ⟨contraction target.val, membership⟩ ≤
          closedForm domain form nonnegative closable target)
    (forcing : H) (forcingFixed : contraction forcing = forcing) :
    contraction (smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing) =
      smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing := by
  obtain ⟨membership, energyDecreases⟩ :=
    energyBound (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value
  have membershipState : contraction (smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing) ∈ closedDomain domain form nonnegative := by
    simpa only [smallStepLift_value] using membership
  let candidate : QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable)
      (closedForm_nonnegative domain form nonnegative closable) :=
    ⟨⟨contraction (smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing), membershipState⟩⟩
  have distanceDecreases :=
    distanceBound (smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing) forcing
  rw [forcingFixed] at distanceDecreases
  have squaredDistanceDecreases :
      ‖contraction (smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing) - forcing‖ ^ 2 ≤
        ‖smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing - forcing‖ ^ 2 := by
    nlinarith [norm_nonneg (contraction (smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing) - forcing),
      norm_nonneg (smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing - forcing)]
  have candidateEnergy : closedForm domain form nonnegative closable candidate.value ≤
      closedForm domain form nonnegative closable
        (smallStepLift domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing).value := by
    simpa only [candidate, smallStepLift_value] using energyDecreases
  have uniqueness := smallStep_minimizer_unique domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing candidate
    (by simpa only [smallStepLift_value] using
      add_le_add (mul_le_mul_of_nonneg_left candidateEnergy stepPositive.le) squaredDistanceDecreases)
  simpa only [candidate, smallStepLift_value] using congrArg (fun test => (test.value : H)) uniqueness

end Hilbert

section L2

variable {X : Type*} [MeasurableSpace X] (measure : Measure X)
variable (domain : Submodule ℝ (Lp ℝ 2 measure)) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set (Lp ℝ 2 measure)))
    (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1)

theorem lp_smallStep_resolvent_preserves_nonnegative
    (normalContractions : ∀ (contraction : ℝ → ℝ)
      (lipschitz : LipschitzWith 1 contraction) (zero : contraction 0 = 0)
      (target : closedDomain domain form nonnegative),
      ∃ membership : lipschitz.compLp zero target.val ∈ closedDomain domain form nonnegative,
        closedForm domain form nonnegative closable ⟨lipschitz.compLp zero target.val, membership⟩ ≤
          closedForm domain form nonnegative closable target)
    (forcing : Lp ℝ 2 measure) (forcingNonnegative : ∀ᵐ point ∂measure, 0 ≤ forcing point) :
    ∀ᵐ point ∂measure, 0 ≤ smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing point := by
  have lipschitz : LipschitzWith 1 (fun value : ℝ => max value 0) := Lp.lipschitzWith_pos_part
  have zero : max (0 : ℝ) 0 = 0 := max_self _
  have forcingFixed : lipschitz.compLp zero forcing = forcing := by
    apply Lp.ext
    filter_upwards [lipschitz.coeFn_compLp zero forcing, forcingNonnegative] with point evaluation positive
    simpa only [Function.comp_apply, max_eq_left positive] using evaluation
  have fixed := smallStep_resolvent_fixed_of_contraction domain form nonnegative closable domainDense step stepPositive stepAtMostOne
    (lipschitz.compLp zero)
    (fun first second => by simpa only [NNReal.coe_one, one_mul] using
      lipschitz.norm_compLp_sub_le zero first second)
    (normalContractions _ lipschitz zero) forcing forcingFixed
  have evaluation := lipschitz.coeFn_compLp zero
    (smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing)
  rw [fixed] at evaluation
  filter_upwards [evaluation] with point equality
  change smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing point =
    max (smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing point) 0 at equality
  rw [equality]
  exact le_max_right _ _

theorem lp_smallStep_resolvent_preserves_unit_interval
    (normalContractions : ∀ (contraction : ℝ → ℝ)
      (lipschitz : LipschitzWith 1 contraction) (zero : contraction 0 = 0)
      (target : closedDomain domain form nonnegative),
      ∃ membership : lipschitz.compLp zero target.val ∈ closedDomain domain form nonnegative,
        closedForm domain form nonnegative closable ⟨lipschitz.compLp zero target.val, membership⟩ ≤
          closedForm domain form nonnegative closable target)
    (forcing : Lp ℝ 2 measure)
    (forcingBounds : ∀ᵐ point ∂measure, 0 ≤ forcing point ∧ forcing point ≤ 1) :
    ∀ᵐ point ∂measure,
      0 ≤ smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing point ∧
        smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing point ≤ 1 := by
  have lipschitz : LipschitzWith 1 (fun value : ℝ => min (max value 0) 1) :=
    Lp.lipschitzWith_pos_part.min_const 1
  have zero : min (max (0 : ℝ) 0) 1 = 0 := by norm_num
  have forcingFixed : lipschitz.compLp zero forcing = forcing := by
    apply Lp.ext
    filter_upwards [lipschitz.coeFn_compLp zero forcing, forcingBounds] with point evaluation bounds
    simpa only [Function.comp_apply, max_eq_left bounds.1, min_eq_left bounds.2] using evaluation
  have fixed := smallStep_resolvent_fixed_of_contraction domain form nonnegative closable domainDense step stepPositive stepAtMostOne
    (lipschitz.compLp zero)
    (fun first second => by simpa only [NNReal.coe_one, one_mul] using
      lipschitz.norm_compLp_sub_le zero first second)
    (normalContractions _ lipschitz zero) forcing forcingFixed
  have evaluation := lipschitz.coeFn_compLp zero
    (smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing)
  rw [fixed] at evaluation
  filter_upwards [evaluation] with point equality
  change smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing point =
    min (max (smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne forcing point) 0) 1 at equality
  rw [equality]
  exact ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩

end L2

#print axioms smallStep_resolvent_fixed_of_contraction
#print axioms lp_smallStep_resolvent_preserves_nonnegative
#print axioms lp_smallStep_resolvent_preserves_unit_interval

end IGS.Sec31.QuadraticEnergySpace
