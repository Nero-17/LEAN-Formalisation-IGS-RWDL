import RequestProject.Section31.EIGSNativeFiniteResolvent

/-! Exact minimization by the genuine finite native random-walk resolvent.
The gap identity uses the proved transition-kernel symmetry, the actual
energy/operator normalization, and the actual inverse equation. No quadratic
form or minimization property is an additional input. -/

namespace EIGS

open MeasureTheory

noncomputable section

set_option maxHeartbeats 2400000

variable {K : ℕ}
variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (mass : XiMassParameters system) (level : ℕ)
    (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (step : ℝ) (stepPositive : 0 < step)

theorem xiNativeFiniteResolvent_minimum_gap
    (forcing competitor : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    let solution := xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing
    step * xiNativeScaledUnitEnergy system mass resistanceRate normalization level competitor + ‖competitor - forcing‖ ^ 2 =
      step * xiNativeScaledUnitEnergy system mass resistanceRate normalization level solution + ‖solution - forcing‖ ^ 2 +
        step * xiNativeScaledUnitEnergy system mass resistanceRate normalization level (competitor - solution) +
          ‖competitor - solution‖ ^ 2 := by
  let solution := xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing
  change step * xiNativeScaledUnitEnergy system mass resistanceRate normalization level competitor + ‖competitor - forcing‖ ^ 2 =
    step * xiNativeScaledUnitEnergy system mass resistanceRate normalization level solution + ‖solution - forcing‖ ^ 2 +
      step * xiNativeScaledUnitEnergy system mass resistanceRate normalization level (competitor - solution) +
        ‖competitor - solution‖ ^ 2
  have energyPairing (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
      xiNativeScaledUnitEnergy system mass resistanceRate normalization level values =
        inner ℝ values (xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization values) := by
    simpa only [xiNativeFiniteGenerator, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, real_inner_smul_right] using
      xiNativeScaledUnitEnergy_eq_randomWalk_form system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent mass level resistanceRate normalization values
  have generatorSymmetry (first second : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
      inner ℝ (xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization first) second =
        inner ℝ first (xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization second) := by
    simp only [xiNativeFiniteGenerator, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right]
    rw [xiNativeRandomWalk_inner_symmetric system rulesConnected rulesLoopless rulesUnique plantingNonadjacent]
  have energyDifference : xiNativeScaledUnitEnergy system mass resistanceRate normalization level (competitor - solution) =
      xiNativeScaledUnitEnergy system mass resistanceRate normalization level competitor +
        xiNativeScaledUnitEnergy system mass resistanceRate normalization level solution -
          2 * inner ℝ (xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization solution) competitor := by
    rw [energyPairing, map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
      ← generatorSymmetry solution competitor,
      real_inner_comm (xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization solution) competitor,
      ← energyPairing competitor, ← energyPairing solution]
    ring
  have solutionIdentity := (xiNativeFiniteResolvent_properties system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive).1 forcing |>.1
  change solution + step • xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization solution = forcing at solutionIdentity
  have competitorPairing := congrArg (fun values => inner ℝ values competitor) solutionIdentity
  have selfPairing := congrArg (fun values => inner ℝ values solution) solutionIdentity
  dsimp only at competitorPairing selfPairing
  rw [inner_add_left, real_inner_smul_left] at competitorPairing
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    real_inner_comm solution (xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization solution),
    ← energyPairing solution] at selfPairing
  rw [energyDifference, norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real,
    real_inner_comm forcing competitor, real_inner_comm forcing solution, real_inner_comm solution competitor]
  nlinarith

theorem xiNativeFiniteResolvent_minimizes
    (forcing competitor : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    let solution := xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing
    step * xiNativeScaledUnitEnergy system mass resistanceRate normalization level solution + ‖solution - forcing‖ ^ 2 ≤
      step * xiNativeScaledUnitEnergy system mass resistanceRate normalization level competitor + ‖competitor - forcing‖ ^ 2 := by
  rw [xiNativeFiniteResolvent_minimum_gap system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing competitor]
  have energyNonnegative := xiNativeScaledUnitEnergy_nonnegative system mass resistanceRate normalization
    rateNonnegative normalizationNonnegative level
    (competitor - xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing)
  nlinarith [mul_nonneg stepPositive.le energyNonnegative, sq_nonneg ‖competitor -
    xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing‖]

theorem xiNativeFiniteResolvent_minimizer_unique
    (forcing competitor : Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
    (minimal : step * xiNativeScaledUnitEnergy system mass resistanceRate normalization level competitor + ‖competitor - forcing‖ ^ 2 ≤
      step * xiNativeScaledUnitEnergy system mass resistanceRate normalization level
        (xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing) +
        ‖xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing - forcing‖ ^ 2) :
    competitor = xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing := by
  rw [xiNativeFiniteResolvent_minimum_gap system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing competitor] at minimal
  have energyNonnegative := xiNativeScaledUnitEnergy_nonnegative system mass resistanceRate normalization
    rateNonnegative normalizationNonnegative level
    (competitor - xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing)
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [mul_nonneg stepPositive.le energyNonnegative, norm_nonneg (competitor -
    xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing)]

end
end EIGS

#print axioms EIGS.xiNativeFiniteResolvent_minimum_gap
#print axioms EIGS.xiNativeFiniteResolvent_minimizes
#print axioms EIGS.xiNativeFiniteResolvent_minimizer_unique
