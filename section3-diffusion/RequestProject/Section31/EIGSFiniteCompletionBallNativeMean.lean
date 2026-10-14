import RequestProject.Section31.EIGSFiniteCompletionBallExitUpper
import RequestProject.Section31.EIGSNativeGridWindowClock
import RequestProject.Section31.EIGSFiniteHorizonStepPathLawOfRules

/-! Divide the actual arbitrary-source ball exit mean by the same native
finite jump rate. The spectral mass lower bound cancels the fine depth;
the remaining bound is the coarse time scale. -/

namespace EIGS
open IGS.Sec31
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 7000000
variable {K : ℕ}

theorem xiFiniteCompletionBall_native_mean_upper (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = rate • lengths)
    (lowerLength : ℝ) (lowerLengthPositive : 0 < lowerLength)
    (lengthLower : ∀ colour, lowerLength ≤ lengths colour) :
    ∃ upper : ℝ, 0 < upper ∧ ∀ coarse, 1 ≤ coarse → ∀ steps
      (center source : XiVtx system (coarse + steps)),
      expExit (XiSimpleGraph system (coarse + steps))
        (Finset.univ.filter fun target =>
          dist (xiCompletionEmbedding system rulesConnected lengths lengthsPositive rate
              (zero_lt_one.trans rateGreaterThanOne) eigenpair (coarse + steps) center)
            (xiCompletionEmbedding system rulesConnected lengths lengthsPositive rate
              (zero_lt_one.trans rateGreaterThanOne) eigenpair (coarse + steps) target) <
            lowerLength * rate⁻¹ ^ coarse) source /
        (xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive
          normalization normalizationPositive (coarse + steps) : ℝ) ≤
        upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse := by
  obtain ⟨exitUpper, exitUpperPositive, exitBounds⟩ :=
    xiFiniteCompletionBall_allSource_expExit_spectral_upper system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive lengths lengthsPositive rate rateGreaterThanOne
      eigenpair lowerLength lowerLengthPositive lengthLower
  obtain ⟨jumpLower, jumpLowerPositive, jumpBounds⟩ :=
    xiNativeFiniteJumpRate_spectral_lower system rulesConnected distancePositive
      normalization normalizationPositive
  have timePositive : 0 < realMatrixSpectralRadius (massMatrixR system.toRuleData) *
      system.resistanceSpectralRadius rulesConnected distancePositive :=
    mul_pos (eigs_mass_spectral_growth system rulesConnected distancePositive).1
      (system.resistanceSpectralRadius_positive_eigenpair rulesConnected distancePositive).1
  refine ⟨exitUpper / jumpLower, div_pos exitUpperPositive jumpLowerPositive, ?_⟩
  intro coarse coarsePositive steps center source
  have nativePositive : 0 < (xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive
      normalization normalizationPositive (coarse + steps) : ℝ) :=
    (mul_pos jumpLowerPositive (pow_pos timePositive _)).trans_le (jumpBounds _)
  apply (div_le_iff₀ nativePositive).mpr
  calc
    _ ≤ exitUpper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps :=
      exitBounds coarse coarsePositive steps center source
    _ = (exitUpper / jumpLower *
          (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
            system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse) *
        (jumpLower * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rulesConnected distancePositive) ^ (coarse + steps)) := by
      rw [pow_add, inv_pow]
      field_simp [jumpLowerPositive.ne', pow_ne_zero coarse timePositive.ne']
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (jumpBounds (coarse + steps)) (by positivity)

end
end EIGS

#print axioms EIGS.xiFiniteCompletionBall_native_mean_upper
