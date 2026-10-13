import RequestProject.Section31.EIGSCompletedCoarseLaplaceIteration
import RequestProject.Section31.EIGSDiscreteFiniteObservations

/-! Uniform control of the genuine native clock on anchored two-window
intervals. The difference of absolute floors retains its one-step error.
Actual mass growth bounds the resulting Laplace correction uniformly over
both coarse level and refinement depth. -/

namespace IGS.Sec31.PoissonizedWalk

theorem floor_clock_grid_increment_le (rate window time : ℝ) (index : ℕ)
    (rateNonnegative : 0 ≤ rate) (windowPositive : 0 < window)
    (afterAnchor : (index : ℝ) * window ≤ time)
    (beforeEnd : time ≤ ((index : ℝ) + 2) * window) :
    Nat.floor (time * rate) - Nat.floor ((index : ℝ) * window * rate) ≤
      Nat.floor (2 * rate * window) + 1 := by
  have anchorNonnegative : 0 ≤ (index : ℝ) * window := mul_nonneg (Nat.cast_nonneg index) windowPositive.le
  have increment := (floor_increment_bounds rate ((index : ℝ) * window) time
    rateNonnegative anchorNonnegative afterAnchor).2
  have intervalBound : (time - (index : ℝ) * window) * rate ≤ 2 * rate * window := by
    have scaled := mul_le_mul_of_nonneg_right
      (show time - (index : ℝ) * window ≤ 2 * window by nlinarith) rateNonnegative
    convert scaled using 1 <;> ring
  exact increment.trans (Nat.add_le_add_right (Nat.floor_mono intervalBound) 1)

theorem floor_clock_grid_increment_ratio_le (rate fraction spatial window time : ℝ) (index : ℕ)
    (ratePositive : 0 < rate) (fractionPositive : 0 < fraction)
    (spatialPositive : 0 < spatial) (windowPositive : 0 < window)
    (afterAnchor : (index : ℝ) * window ≤ time)
    (beforeEnd : time ≤ ((index : ℝ) + 2) * window) :
    ((Nat.floor (time * rate) - Nat.floor ((index : ℝ) * window * rate) : ℕ) : ℝ) /
        (rate * fraction * spatial) ≤
      2 * window / (fraction * spatial) + 1 / (rate * fraction * spatial) := by
  have castBound : ((Nat.floor (time * rate) - Nat.floor ((index : ℝ) * window * rate) : ℕ) : ℝ) ≤
      (Nat.floor (2 * rate * window) : ℝ) + 1 := by
    exact_mod_cast floor_clock_grid_increment_le rate window time index ratePositive.le windowPositive afterAnchor beforeEnd
  have floorBound := Nat.floor_le (by positivity : 0 ≤ 2 * rate * window)
  have numeratorBound : ((Nat.floor (time * rate) - Nat.floor ((index : ℝ) * window * rate) : ℕ) : ℝ) ≤
      2 * rate * window + 1 := by linarith
  calc
    _ ≤ (2 * rate * window + 1) / (rate * fraction * spatial) :=
      div_le_div_of_nonneg_right numeratorBound (by positivity)
    _ = _ := by field_simp [ratePositive.ne', fractionPositive.ne', spatialPositive.ne'] <;> ring

end IGS.Sec31.PoissonizedWalk

namespace EIGS

open scoped Classical
noncomputable section
variable {K : ℕ}

theorem xiNativeFiniteJumpRate_spectral_lower (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization) :
    ∃ lower : ℝ, 0 < lower ∧ ∀ level,
      lower * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rulesConnected distancePositive) ^ level ≤
      xiNativeFiniteJumpRate system level
        (system.resistanceSpectralRadius rulesConnected distancePositive) normalization := by
  obtain ⟨massPositive, massLower, massUpper, massLowerPositive, massUpperPositive, growth⟩ :=
    eigs_mass_spectral_growth system rulesConnected distancePositive
  have resistancePositive := (system.resistanceSpectralRadius_positive_eigenpair rulesConnected distancePositive).1
  refine ⟨2 * normalization * massLower, by positivity, ?_⟩
  intro level
  calc
    _ = (2 * normalization * (system.resistanceSpectralRadius rulesConnected distancePositive) ^ level) *
        (massLower * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ level) := by
      rw [mul_pow]
      ring
    _ ≤ (2 * normalization * (system.resistanceSpectralRadius rulesConnected distancePositive) ^ level) *
        (totalEdges system.toRuleData level : ℝ) :=
      mul_le_mul_of_nonneg_left (growth level).1 (by positivity)
    _ = _ := rfl

theorem xiCoarseNativeLaplaceScale_uniform_lower_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization fraction : ℝ) (normalizationPositive : 0 < normalization) (fractionPositive : 0 < fraction) :
    ∃ lower : ℝ, 0 < lower ∧ ∀ coarse steps,
      lower ≤ xiCoarseNativeLaplaceScale system rulesConnected distancePositive normalization fraction coarse steps := by
  obtain ⟨jumpLower, jumpLowerPositive, jumpBound⟩ :=
    xiNativeFiniteJumpRate_spectral_lower system rulesConnected distancePositive normalization normalizationPositive
  have distanceBound := system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive
  have squareBound := system.distanceSpectralRadius_sq_le_mass_mul_resistance rulesConnected rulesLoopless rulesUnique distancePositive
  have timeRateGeOne : 1 ≤ realMatrixSpectralRadius (massMatrixR system.toRuleData) *
      system.resistanceSpectralRadius rulesConnected distancePositive := by nlinarith
  have timeRatePositive : 0 < realMatrixSpectralRadius (massMatrixR system.toRuleData) *
      system.resistanceSpectralRadius rulesConnected distancePositive := zero_lt_one.trans_le timeRateGeOne
  refine ⟨jumpLower * fraction, mul_pos jumpLowerPositive fractionPositive, ?_⟩
  intro coarse steps
  have scaledJump := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (jumpBound (coarse + steps)) fractionPositive.le)
    (pow_nonneg (inv_nonneg.mpr timeRatePositive.le) coarse)
  have cancellation :
      (jumpLower * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rulesConnected distancePositive) ^ (coarse + steps)) * fraction *
          (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
            system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse =
      (jumpLower * fraction) * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps := by
    rw [pow_add, inv_pow]
    field_simp [pow_ne_zero coarse timeRatePositive.ne'] <;> ring
  rw [cancellation] at scaledJump
  exact (le_mul_of_one_le_right (mul_pos jumpLowerPositive fractionPositive).le
    (one_le_pow₀ timeRateGeOne)).trans scaledJump

theorem xiNativeGridWindow_exponential_bound_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization fraction : ℝ) (normalizationPositive : 0 < normalization) (fractionPositive : 0 < fraction) :
    ∃ factor : ℝ, 0 < factor ∧ ∀ coarse steps (window time : ℝ) (index : ℕ),
      0 < window → (index : ℝ) * window ≤ time → time ≤ ((index : ℝ) + 2) * window →
      Real.exp (((Nat.floor (time * xiNativeFiniteJumpRate system (coarse + steps)
          (system.resistanceSpectralRadius rulesConnected distancePositive) normalization) -
        Nat.floor ((index : ℝ) * window * xiNativeFiniteJumpRate system (coarse + steps)
          (system.resistanceSpectralRadius rulesConnected distancePositive) normalization) : ℕ) : ℝ) /
            xiCoarseNativeLaplaceScale system rulesConnected distancePositive normalization fraction coarse steps) ≤
        factor * Real.exp (2 * window / (fraction *
          (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
            system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse)) := by
  obtain ⟨lower, lowerPositive, scaleLower⟩ := xiCoarseNativeLaplaceScale_uniform_lower_of_rules
    system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
    normalization fraction normalizationPositive fractionPositive
  refine ⟨Real.exp (1 / lower), Real.exp_pos _, ?_⟩
  intro coarse steps window time index windowPositive afterAnchor beforeEnd
  have scalePositive := lowerPositive.trans_le (scaleLower coarse steps)
  have resistancePositive := (system.resistanceSpectralRadius_positive_eigenpair rulesConnected distancePositive).1
  have timeRatePositive := mul_pos (eigs_mass_spectral_growth system rulesConnected distancePositive).1 resistancePositive
  have spatialPositive : 0 < (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
      system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse :=
    pow_pos (inv_pos.mpr timeRatePositive) coarse
  have jumpPositive : 0 < xiNativeFiniteJumpRate system (coarse + steps)
      (system.resistanceSpectralRadius rulesConnected distancePositive) normalization := by
    have productPositive := (mul_pos_iff_of_pos_right spatialPositive).mp scalePositive
    exact (mul_pos_iff_of_pos_right fractionPositive).mp productPositive
  have clockBound := IGS.Sec31.PoissonizedWalk.floor_clock_grid_increment_ratio_le
    (xiNativeFiniteJumpRate system (coarse + steps)
      (system.resistanceSpectralRadius rulesConnected distancePositive) normalization)
    fraction ((realMatrixSpectralRadius (massMatrixR system.toRuleData) *
      system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse)
    window time index jumpPositive fractionPositive spatialPositive windowPositive afterAnchor beforeEnd
  have inverseBound := one_div_le_one_div_of_le lowerPositive (scaleLower coarse steps)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  exact clockBound.trans (by
    change 2 * window / (fraction * _) + 1 / xiCoarseNativeLaplaceScale system rulesConnected
      distancePositive normalization fraction coarse steps ≤ _
    linarith)

end
end EIGS

#print axioms IGS.Sec31.PoissonizedWalk.floor_clock_grid_increment_le
#print axioms IGS.Sec31.PoissonizedWalk.floor_clock_grid_increment_ratio_le
#print axioms EIGS.xiNativeFiniteJumpRate_spectral_lower
#print axioms EIGS.xiCoarseNativeLaplaceScale_uniform_lower_of_rules
#print axioms EIGS.xiNativeGridWindow_exponential_bound_of_rules
