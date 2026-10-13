import RequestProject.Section31.EIGSAllStartSkeletonExit
import RequestProject.Section31.EIGSNativeResolventHarmonicError
import RequestProject.Section31.EIGSAnalyticTimeScale

/-! Uniform harmonic tails for actual native finite resolvents. The actual
all-start skeleton exit estimate is consumed internally. Mass growth cancels
the finer-cell depth, leaving inverse powers of the actual coarse time rate.
No resistance-rate-greater-than-one or desired uniform bound is assumed. -/

namespace EIGS

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem resolvent_harmonic_scale_identity (exitUpper normalization massLower step rate values : ℝ)
    (normalizationPositive : 0 < normalization) (massLowerPositive : 0 < massLower)
    (stepPositive : 0 < step) (ratePositive : 0 < rate) (coarse steps : ℕ) :
    (2 * values / (step * ((2 * normalization * massLower) * rate ^ (coarse + steps)))) *
        (exitUpper * rate ^ steps) =
      ((exitUpper / (normalization * massLower)) / step) * values * rate⁻¹ ^ coarse := by
  rw [pow_add, inv_pow]
  field_simp [normalizationPositive.ne', massLowerPositive.ne', stepPositive.ne',
    pow_ne_zero coarse ratePositive.ne', pow_ne_zero steps ratePositive.ne'] <;> ring

variable {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (mass : XiMassParameters system) (normalization : ℝ) (normalizationPositive : 0 < normalization)

include rulesLoopless rulesUnique plantingNonadjacent

theorem xiNativeFiniteResolvent_uniform_harmonic_error_spectral :
    ∃ upper : ℝ, 0 < upper ∧ ∀ coarse steps (step : ℝ) (stepPositive : 0 < step)
      (forcing : Lp ℝ 2 (xiVertexSpeedMeasure system mass (coarse + steps)))
      (vertex : XiVtx system (coarse + steps)),
      let resistanceRate := system.resistanceSpectralRadius rulesConnected distancePositive
      let ratePositive := (system.resistanceSpectralRadius_positive_eigenpair
        rulesConnected distancePositive).1
      let solution := xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent mass (coarse + steps) resistanceRate normalization ratePositive.le
          normalizationPositive.le step stepPositive forcing
      |solution vertex - xiUnitTraceExtension system rulesConnected coarse steps
          (fun oldVertex => solution (xiForward system coarse steps oldVertex)) vertex| ≤
        (upper / step) * ‖fun target : XiVtx system (coarse + steps) => forcing target‖ *
          (mass.rate * resistanceRate)⁻¹ ^ coarse := by
  obtain ⟨exitUpper, exitUpperPositive, exitBound⟩ := xiSkeleton_expExit_spectral_upper
    system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  obtain ⟨_, massLower, massUpper, massLowerPositive, _, massGrowth⟩ :=
    eigs_mass_spectral_growth system rulesConnected distancePositive
  have ratePositive := (system.resistanceSpectralRadius_positive_eigenpair
    rulesConnected distancePositive).1
  have timeRatePositive := mul_pos mass.rate_positive ratePositive
  refine ⟨exitUpper / (normalization * massLower),
    div_pos exitUpperPositive (mul_pos normalizationPositive massLowerPositive), ?_⟩
  intro coarse steps step stepPositive forcing vertex
  dsimp only
  have edgeLower := (massGrowth (coarse + steps)).1
  rw [← XiMassParameters.rate_eq_spectralRadius system mass] at edgeLower
  have jumpLower :
      (2 * normalization * massLower) *
          (mass.rate * system.resistanceSpectralRadius rulesConnected distancePositive) ^ (coarse + steps) ≤
        xiNativeFiniteJumpRate system (coarse + steps)
          (system.resistanceSpectralRadius rulesConnected distancePositive) normalization := by
    calc
      _ = (2 * normalization *
          (system.resistanceSpectralRadius rulesConnected distancePositive) ^ (coarse + steps)) *
            (massLower * mass.rate ^ (coarse + steps)) := by rw [mul_pow]; ring
      _ ≤ (2 * normalization *
          (system.resistanceSpectralRadius rulesConnected distancePositive) ^ (coarse + steps)) *
            (totalEdges system.toRuleData (coarse + steps) : ℝ) :=
        mul_le_mul_of_nonneg_left edgeLower (by positivity)
      _ = _ := rfl
  have coefficientLowerPositive : 0 < (2 * normalization * massLower) *
      (mass.rate * system.resistanceSpectralRadius rulesConnected distancePositive) ^ (coarse + steps) :=
    mul_pos (by positivity) (pow_pos timeRatePositive (coarse + steps))
  have coefficientComparison :
      2 * ‖fun target : XiVtx system (coarse + steps) => forcing target‖ /
          (step * xiNativeFiniteJumpRate system (coarse + steps)
            (system.resistanceSpectralRadius rulesConnected distancePositive) normalization) ≤
        2 * ‖fun target : XiVtx system (coarse + steps) => forcing target‖ /
          (step * ((2 * normalization * massLower) *
            (mass.rate * system.resistanceSpectralRadius rulesConnected distancePositive) ^ (coarse + steps))) :=
    div_le_div_of_nonneg_left (by positivity) (mul_pos stepPositive coefficientLowerPositive)
      (mul_le_mul_of_nonneg_left jumpLower stepPositive.le)
  have actualExitBound := exitBound coarse steps vertex
  rw [← XiMassParameters.rate_eq_spectralRadius system mass] at actualExitBound
  have nativeBound := xiNativeFiniteResolvent_skeleton_error_le_exit system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent mass coarse steps
    (system.resistanceSpectralRadius rulesConnected distancePositive) normalization ratePositive
    normalizationPositive step stepPositive forcing vertex
  dsimp only at nativeBound
  apply nativeBound.trans
  calc
    _ ≤ (2 * ‖fun target : XiVtx system (coarse + steps) => forcing target‖ /
        (step * ((2 * normalization * massLower) *
          (mass.rate * system.resistanceSpectralRadius rulesConnected distancePositive) ^ (coarse + steps)))) *
      (exitUpper * (mass.rate * system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps) :=
      mul_le_mul coefficientComparison actualExitBound (expExit_nonneg vertex) (by positivity)
    _ = _ := resolvent_harmonic_scale_identity exitUpper normalization massLower step
      (mass.rate * system.resistanceSpectralRadius rulesConnected distancePositive)
      ‖fun target : XiVtx system (coarse + steps) => forcing target‖ normalizationPositive
      massLowerPositive stepPositive timeRatePositive coarse steps

include distancePositive

theorem xiNativeFiniteResolvent_uniform_harmonic_error_of_positive_eigenpair
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : (system.ruleFamily rulesConnected).Psi resistanceVector =
      resistanceRate • resistanceVector) :
    ∃ upper : ℝ, 0 < upper ∧ ∀ coarse steps (step : ℝ) (stepPositive : 0 < step)
      (forcing : Lp ℝ 2 (xiVertexSpeedMeasure system mass (coarse + steps)))
      (vertex : XiVtx system (coarse + steps)),
      let solution := xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent mass (coarse + steps) resistanceRate normalization ratePositive.le
          normalizationPositive.le step stepPositive forcing
      |solution vertex - xiUnitTraceExtension system rulesConnected coarse steps
          (fun oldVertex => solution (xiForward system coarse steps oldVertex)) vertex| ≤
        (upper / step) * ‖fun target : XiVtx system (coarse + steps) => forcing target‖ *
          (mass.rate * resistanceRate)⁻¹ ^ coarse := by
  have rateEquality := system.resistanceSpectralRadius_eq_of_positive_eigenpair rulesConnected
    distancePositive ratePositive vectorPositive renormalizationEigenpair
  have spectral := xiNativeFiniteResolvent_uniform_harmonic_error_spectral system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive mass normalization normalizationPositive
  simpa only [rateEquality] using spectral

end
end EIGS

#print axioms EIGS.resolvent_harmonic_scale_identity
#print axioms EIGS.xiNativeFiniteResolvent_uniform_harmonic_error_spectral
#print axioms EIGS.xiNativeFiniteResolvent_uniform_harmonic_error_of_positive_eigenpair
