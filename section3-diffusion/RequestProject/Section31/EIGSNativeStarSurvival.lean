import RequestProject.Section31.EIGSAllStartStarSurvival
import RequestProject.Section31.EIGSNativePoissonizedWalk
import RequestProject.Section31.EIGSAnalyticTimeScale

/-! A genuine uniformly positive star-survival probability at the native
finite walk clock. The jump-rate upper bound is derived from actual edge
mass growth. There is no assumed jump bound, survival bound or rho > 1. -/

namespace EIGS

open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

variable {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization)

include normalizationPositive

theorem xiNativeFiniteJumpRate_spectral_upper :
    ∃ upper : ℝ, 0 < upper ∧ ∀ level,
      xiNativeFiniteJumpRate system level
        (system.resistanceSpectralRadius rulesConnected distancePositive) normalization ≤
      upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rulesConnected distancePositive) ^ level := by
  obtain ⟨_, massLower, massUpper, _, massUpperPositive, massGrowth⟩ :=
    eigs_mass_spectral_growth system rulesConnected distancePositive
  have resistancePositive := (system.resistanceSpectralRadius_positive_eigenpair
    rulesConnected distancePositive).1
  refine ⟨2 * normalization * massUpper, by positivity, ?_⟩
  intro level
  calc
    _ ≤ (2 * normalization *
        (system.resistanceSpectralRadius rulesConnected distancePositive) ^ level) *
          (massUpper * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ level) :=
      mul_le_mul_of_nonneg_left (massGrowth level).2 (by positivity)
    _ = _ := by rw [mul_pow]; ring

variable
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))

include rulesLoopless rulesUnique plantingNonadjacent

theorem xiIncidentStarDomain_native_clock_positive_survival :
    ∃ timeFraction survivalProbability : ℝ,
      0 < timeFraction ∧ 0 < survivalProbability ∧
      ∀ coarse steps (center : XiVtx system coarse),
      survivalProbability ≤ surv (XiSimpleGraph system (coarse + steps))
        (xiIncidentStarDomain system coarse steps center)
        ⌊xiNativeFiniteJumpRate system (coarse + steps)
            (system.resistanceSpectralRadius rulesConnected distancePositive) normalization *
          timeFraction * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
            system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse⌋₊
        (xiForward system coarse steps center) := by
  obtain ⟨lower, upper, lowerPositive, upperPositive, survivalBound⟩ :=
    xiIncidentStarDomain_uniform_positive_survival system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive
  obtain ⟨jumpUpper, jumpUpperPositive, jumpBound⟩ :=
    xiNativeFiniteJumpRate_spectral_upper system rulesConnected distancePositive
      normalization normalizationPositive
  have resistancePositive := (system.resistanceSpectralRadius_positive_eigenpair
    rulesConnected distancePositive).1
  have timeRatePositive := mul_pos
    (eigs_mass_spectral_growth system rulesConnected distancePositive).1 resistancePositive
  refine ⟨lower / (2 * jumpUpper), lower / (2 * upper),
    div_pos lowerPositive (by positivity), div_pos lowerPositive (by positivity), ?_⟩
  intro coarse steps center
  apply survivalBound coarse steps center
  have clockNonnegative : 0 ≤
      xiNativeFiniteJumpRate system (coarse + steps)
          (system.resistanceSpectralRadius rulesConnected distancePositive) normalization *
        (lower / (2 * jumpUpper)) *
        (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse := by
    apply mul_nonneg
    · exact mul_nonneg
        (xiNativeFiniteJumpRate_nonnegative system (coarse + steps) _ normalization
          resistancePositive.le normalizationPositive.le)
        (div_nonneg lowerPositive.le (by positivity))
    · exact pow_nonneg (inv_nonneg.mpr timeRatePositive.le) coarse
  apply (Nat.floor_le clockNonnegative).trans
  calc
    _ ≤ (jumpUpper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rulesConnected distancePositive) ^ (coarse + steps)) *
        (lower / (2 * jumpUpper)) *
        (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (jumpBound (coarse + steps))
          (div_nonneg lowerPositive.le (by positivity)))
        (pow_nonneg (inv_nonneg.mpr timeRatePositive.le) coarse)
    _ = _ := by
      rw [pow_add, inv_pow]
      field_simp [jumpUpperPositive.ne', pow_ne_zero coarse timeRatePositive.ne'] <;> ring

include distancePositive

theorem xiIncidentStarDomain_native_clock_positive_survival_of_positive_eigenpair
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : (system.ruleFamily rulesConnected).Psi resistanceVector =
      resistanceRate • resistanceVector) :
    ∃ timeFraction survivalProbability : ℝ,
      0 < timeFraction ∧ 0 < survivalProbability ∧
      ∀ coarse steps (center : XiVtx system coarse),
      survivalProbability ≤ surv (XiSimpleGraph system (coarse + steps))
        (xiIncidentStarDomain system coarse steps center)
        ⌊xiNativeFiniteJumpRate system (coarse + steps) resistanceRate normalization *
          timeFraction * (mass.rate * resistanceRate)⁻¹ ^ coarse⌋₊
        (xiForward system coarse steps center) := by
  have massEquality := XiMassParameters.rate_eq_spectralRadius system mass
  have resistanceEquality := system.resistanceSpectralRadius_eq_of_positive_eigenpair
    rulesConnected distancePositive ratePositive vectorPositive renormalizationEigenpair
  have native := xiIncidentStarDomain_native_clock_positive_survival system rulesConnected
    distancePositive normalization normalizationPositive rulesLoopless rulesUnique plantingNonadjacent
  rw [← massEquality, ← resistanceEquality] at native
  exact native

end
end EIGS

#print axioms EIGS.xiNativeFiniteJumpRate_spectral_upper
#print axioms EIGS.xiIncidentStarDomain_native_clock_positive_survival
#print axioms EIGS.xiIncidentStarDomain_native_clock_positive_survival_of_positive_eigenpair
