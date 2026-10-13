import RequestProject.Section31.EIGSNativeSupTransition
import RequestProject.Section31.EIGSNativeSemigroupComparison
import RequestProject.Section31.EIGSNativeResolventHarmonicError
import RequestProject.Section31.AffineContractionTruncation

/-! The actual finite resolvent equation on vertex functions. Evaluation of
the native speed L² equation gives the affine equation for the actual sup
transition. Its finite expansion is therefore an identity for the existing
resolvent, rather than a separately postulated probabilistic resolvent. -/

namespace EIGS

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 3000000

variable {K : ℕ}

theorem xiNativeFiniteResolvent_sup_affine_equation
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (mass : XiMassParameters system) (level : ℕ)
    (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (step : ℝ) (stepPositive : 0 < step)
    (forcing : XiVtx system level → ℝ) :
    let rate := xiNativeFiniteJumpRate system level resistanceRate normalization
    let solution := fun vertex =>
      xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
        (xiFiniteSpeedL2 system mass level forcing) vertex
    solution = (1 + step * rate)⁻¹ • forcing +
      (step * rate / (1 + step * rate)) • xiNativeSupTransition system rulesConnected level solution := by
  let rate := xiNativeFiniteJumpRate system level resistanceRate normalization
  let solution := xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass level resistanceRate normalization rateNonnegative
    normalizationNonnegative step stepPositive (xiFiniteSpeedL2 system mass level forcing)
  have rateNonnegative' : 0 ≤ rate :=
    xiNativeFiniteJumpRate_nonnegative system level resistanceRate normalization
      rateNonnegative normalizationNonnegative
  have denominatorPositive : 0 < 1 + step * rate := by positivity
  change (fun vertex => solution vertex) = _
  funext vertex
  have pointEquation := xiNativeFiniteResolvent_pointwise_equation system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent mass level resistanceRate normalization
    rateNonnegative normalizationNonnegative step stepPositive
    (xiFiniteSpeedL2 system mass level forcing) vertex
  rw [xiFiniteSpeedL2_apply system rulesConnected] at pointEquation
  change solution vertex + (step * rate) *
    (solution vertex - ∑ target, transProb (XiSimpleGraph system level) vertex target *
      solution target) = forcing vertex at pointEquation
  change solution vertex = (1 + step * rate)⁻¹ * forcing vertex +
    (step * rate / (1 + step * rate)) *
      xiNativeSupTransition system rulesConnected level (fun vertex => solution vertex) vertex
  rw [xiNativeSupTransition_apply]
  field_simp [ne_of_gt denominatorPositive]
  nlinarith [pointEquation]

theorem xiNativeFiniteResolvent_sup_finite_expansion
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (mass : XiMassParameters system) (level : ℕ)
    (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (step : ℝ) (stepPositive : 0 < step) (forcing : XiVtx system level → ℝ) (count : ℕ) :
    let rate := xiNativeFiniteJumpRate system level resistanceRate normalization
    let operator := (step * rate / (1 + step * rate)) •
      xiNativeSupTransition system rulesConnected level
    let solution := fun vertex =>
      xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
        (xiFiniteSpeedL2 system mass level forcing) vertex
    solution = (∑ index ∈ Finset.range count,
      (operator ^ index) ((1 + step * rate)⁻¹ • forcing)) + (operator ^ count) solution := by
  apply IGS.Sec31.affine_fixedPoint_finite_expansion
  exact xiNativeFiniteResolvent_sup_affine_equation system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass level resistanceRate normalization rateNonnegative
      normalizationNonnegative step stepPositive forcing

end
end EIGS

#print axioms EIGS.xiNativeFiniteResolvent_sup_affine_equation
#print axioms EIGS.xiNativeFiniteResolvent_sup_finite_expansion
