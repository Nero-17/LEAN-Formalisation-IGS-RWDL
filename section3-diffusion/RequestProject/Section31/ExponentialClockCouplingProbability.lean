import RequestProject.Section31.ExponentialFloorClockCoupling
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace IGS.Sec31.PoissonClock
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology

/-- On the genuine independent walk/holding-clock sample spaces, the
continuous-time path and its fixed-floor version are uniformly close in
probability on every compact interval. Only the true chain modulus and
diverging positive clocks are inputs, not a path convergence premise. -/
theorem continuousClock_uniform_coupling_probability
    {Space : Type} [MetricSpace Space]
    (Vertices : ℕ → Type) [∀ depth, Fintype (Vertices depth)] [∀ depth, MeasurableSpace (Vertices depth)]
    [∀ depth, MeasurableSingletonClass (Vertices depth)]
    (laws : ∀ depth, Measure (ℕ → Vertices depth)) [∀ depth, IsProbabilityMeasure (laws depth)]
    (placement : ∀ depth, Vertices depth → Space)
    (acceleration : ℕ → ℝ) (accelerationPositive : ∀ depth, 0 < acceleration depth)
    (diverge : Tendsto acceleration atTop atTop)
    (chainModulus : ∀ horizon : ℕ, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ depth in atTop,
        (laws depth).real (floorClockBadModulus
          (placement depth) (acceleration depth) horizon duration tolerance) ≤ error)
    (horizon : ℕ) (tolerance error : ℝ) (tolerancePositive : 0 < tolerance) (errorPositive : 0 < error) :
    ∀ᶠ depth in atTop,
      ∃ bad : Set ((ℕ → Vertices depth) × (ℕ → ℝ)),
        MeasurableSet bad ∧ ((laws depth).prod exponentialHoldingTimeLaw).real bad ≤ error ∧
        ∀ outcome ∉ bad, ∀ time : ℝ, 0 ≤ time → time ≤ horizon →
          dist (placement depth (holdingTimePath outcome.1 outcome.2 (acceleration depth * time)))
            (placement depth (outcome.1 ⌊acceleration depth * time⌋₊)) ≤ tolerance := by
  have regularAE : ∀ᵐ holdingTimes ∂exponentialHoldingTimeLaw,
      (∀ index, 0 < holdingTimes index) ∧ Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop :=
    exponentialHoldingTimeLaw_positive.and exponentialHoldingTimeLaw_nonexplosion
  let irregular := {holdingTimes : ℕ → ℝ | ¬((∀ index, 0 < holdingTimes index) ∧
    Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)}
  let irregularBad := toMeasurable exponentialHoldingTimeLaw irregular
  have irregularBadMeasurable : MeasurableSet irregularBad := measurableSet_toMeasurable _ _
  have irregularBadZero : exponentialHoldingTimeLaw.real irregularBad = 0 := by
    change (exponentialHoldingTimeLaw irregularBad).toReal = 0
    rw [measure_toMeasurable]
    have zero : exponentialHoldingTimeLaw irregular = 0 := (ae_iff).mp regularAE
    rw [zero, ENNReal.toReal_zero]
  obtain ⟨duration, durationPositive, chainProbabilities⟩ := chainModulus (horizon + 1) tolerance (error / 2)
    tolerancePositive (by positivity)
  let clockTolerance : ℝ := min (duration / 4) (1 / 4)
  have clockTolerancePositive : 0 < clockTolerance := lt_min (by positivity) (by norm_num)
  obtain ⟨grid, mesh⟩ := (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds clockTolerancePositive)).exists
  have clockWithinDuration : clockTolerance + 1 / (grid + 1 : ℝ) ≤ duration := by
    have bound := min_le_left (duration / 4) (1 / 4 : ℝ)
    dsimp only [clockTolerance] at mesh ⊢
    linarith
  have clockWithinOne : clockTolerance + 1 / (grid + 1 : ℝ) ≤ 1 := by
    have bound := min_le_right (duration / 4) (1 / 4 : ℝ)
    dsimp only [clockTolerance] at mesh ⊢
    linarith
  have clockProbabilities := (exponential_clock_finite_grid_bad_probability acceleration
    accelerationPositive diverge horizon grid clockTolerance clockTolerancePositive).eventually (gt_mem_nhds (by positivity : (0 : ℝ) < error / 2))
  filter_upwards [chainProbabilities, clockProbabilities] with depth chainProbability clockProbability
  let chainBad := floorClockBadModulus (placement depth) (acceleration depth) (horizon + 1 : ℕ) duration tolerance
  let gridBad := clockFiniteGridBad (acceleration depth) horizon grid clockTolerance
  let bad := (chainBad ×ˢ (Set.univ : Set (ℕ → ℝ))) ∪
    ((Set.univ : Set (ℕ → Vertices depth)) ×ˢ (gridBad ∪ irregularBad))
  have chainMeasurable : MeasurableSet chainBad := floorClockBadModulus_measurable
    (placement depth) _ _ _ _ (accelerationPositive depth).le
  have gridMeasurable : MeasurableSet gridBad := clockFiniteGridBad_measurable _ _ _ _
  refine ⟨bad, (chainMeasurable.prod MeasurableSet.univ).union
    (MeasurableSet.univ.prod (gridMeasurable.union irregularBadMeasurable)), ?_, ?_⟩
  · have bound := measureReal_union_le (μ := (laws depth).prod exponentialHoldingTimeLaw)
      (chainBad ×ˢ (Set.univ : Set (ℕ → ℝ))) ((Set.univ : Set (ℕ → Vertices depth)) ×ˢ (gridBad ∪ irregularBad))
    simp only [measureReal_prod_prod, measureReal_univ_eq_one, mul_one, one_mul] at bound
    have clockUnion := measureReal_union_le (μ := exponentialHoldingTimeLaw) gridBad irregularBad
    rw [irregularBadZero, add_zero] at clockUnion
    exact bound.trans (by linarith)
  · intro outcome outside time timeNonnegative timeBound
    have chainGood : outcome.1 ∉ chainBad := by
      intro failure
      exact outside (Or.inl ⟨failure, Set.mem_univ _⟩)
    have gridGood : outcome.2 ∉ gridBad := by
      intro failure
      exact outside (Or.inr ⟨Set.mem_univ _, Or.inl failure⟩)
    have regularGood : outcome.2 ∉ irregularBad := by
      intro failure
      exact outside (Or.inr ⟨Set.mem_univ _, Or.inr failure⟩)
    have regular : (∀ index, 0 < outcome.2 index) ∧ Tendsto (cumulativeHoldingTime outcome.2) atTop atTop := by
      by_contra failure
      exact regularGood ((subset_toMeasurable exponentialHoldingTimeLaw irregular) failure)
    exact floorChain_good_clock_coupling (placement depth) outcome.1 outcome.2
      (acceleration depth) (accelerationPositive depth) horizon duration (clockTolerance + 1 / (grid + 1 : ℝ)) tolerance
      clockWithinDuration clockWithinOne chainGood
      (fun time nonnegative before => holdingJumpClock_uniform_of_finite_grid outcome.2 regular.1 regular.2
        (acceleration depth) (accelerationPositive depth) horizon grid clockTolerance gridGood time nonnegative before)
      time timeNonnegative timeBound

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.continuousClock_uniform_coupling_probability

