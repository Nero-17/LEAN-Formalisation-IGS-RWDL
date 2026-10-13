import RequestProject.Section31.EIGSNativeRandomWalkEnergy
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Concrete resolvents of the normalized native finite random-walk operator.
The operator is built from the actual transition probabilities. Detailed
balance proves its symmetry; positivity and finite dimension construct its
resolvent for every positive step. No convergence assertion is assumed. -/

namespace EIGS

open MeasureTheory
open scoped BigOperators Classical

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

include rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativeRandomWalk_inner_symmetric
    (first second : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    inner ℝ first (xiNativeRandomWalk system rulesConnected mass level second) =
      inner ℝ (xiNativeRandomWalk system rulesConnected mass level first) second := by
  have detailedBalance (source target : XiVtx system level) :
      ((XiSimpleGraph system level).degree source : ℝ) *
          transProb (XiSimpleGraph system level) source target =
        ((XiSimpleGraph system level).degree target : ℝ) *
          transProb (XiSimpleGraph system level) target source := by
    by_cases adjacent : (XiSimpleGraph system level).Adj source target
    · have sourceDegree : ((XiSimpleGraph system level).degree source : ℝ) ≠ 0 := by
        have sourcePositive : 0 < (XiSimpleGraph system level).degree source :=
          ((XiSimpleGraph system level).degree_pos_iff_exists_adj source).mpr ⟨target, adjacent⟩
        exact_mod_cast (ne_of_gt sourcePositive)
      have targetDegree : ((XiSimpleGraph system level).degree target : ℝ) ≠ 0 := by
        have targetPositive : 0 < (XiSimpleGraph system level).degree target :=
          ((XiSimpleGraph system level).degree_pos_iff_exists_adj target).mpr ⟨source, adjacent.symm⟩
        exact_mod_cast (ne_of_gt targetPositive)
      simp only [transProb, if_pos adjacent, if_pos adjacent.symm,
        mul_inv_cancel₀ sourceDegree, mul_inv_cancel₀ targetDegree]
    · have reverseNonadjacent : ¬ (XiSimpleGraph system level).Adj target source :=
        fun reverse => adjacent reverse.symm
      simp only [transProb, if_neg adjacent, if_neg reverseNonadjacent, mul_zero]
  rw [xiNativeL2_inner_degree system rulesConnected rulesLoopless rulesUnique plantingNonadjacent,
    xiNativeL2_inner_degree system rulesConnected rulesLoopless rulesUnique plantingNonadjacent]
  simp_rw [xiNativeRandomWalk_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro target _
  have balance := detailedBalance target source
  calc
    _ = (((XiSimpleGraph system level).degree target : ℝ) *
        transProb (XiSimpleGraph system level) target source) /
          (2 * (totalEdges system.toRuleData level : ℝ)) * first target * second source := by ring
    _ = _ := by rw [balance]; ring

def xiNativeFiniteGenerator (resistanceRate normalization : ℝ) :
    Lp ℝ 2 (xiVertexSpeedMeasure system mass level) →L[ℝ]
      Lp ℝ 2 (xiVertexSpeedMeasure system mass level) :=
  (2 * normalization * resistanceRate ^ level * (totalEdges system.toRuleData level : ℝ)) •
    (ContinuousLinearMap.id ℝ _ - xiNativeRandomWalk system rulesConnected mass level)

include rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativeFiniteGenerator_nonnegative (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    0 ≤ inner ℝ (xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization values) values := by
  have energyIdentity := xiNativeScaledUnitEnergy_eq_randomWalk_form system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent mass level resistanceRate normalization values
  have energyNonnegative := xiNativeScaledUnitEnergy_nonnegative system mass resistanceRate normalization
    rateNonnegative normalizationNonnegative level values
  change 0 ≤ inner ℝ
    ((2 * normalization * resistanceRate ^ level * (totalEdges system.toRuleData level : ℝ)) •
      (values - xiNativeRandomWalk system rulesConnected mass level values)) values
  rw [real_inner_smul_left, real_inner_comm values
    (values - xiNativeRandomWalk system rulesConnected mass level values), ← energyIdentity]
  exact energyNonnegative

def xiNativeFiniteResolventEquiv (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (step : ℝ) (stepPositive : 0 < step) :
    Lp ℝ 2 (xiVertexSpeedMeasure system mass level) ≃ₗ[ℝ]
      Lp ℝ 2 (xiVertexSpeedMeasure system mass level) := by
  letI : FiniteDimensional ℝ (Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :=
    (xiNativeEvaluationLinearEquiv system rulesConnected mass level).symm.finiteDimensional
  apply LinearEquiv.ofInjectiveEndo
    (ContinuousLinearMap.id ℝ _ + step •
      xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization).toLinearMap
  intro first second equality
  have differenceIdentity : first - second + step •
      xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization (first - second) = 0 := by
    have difference := sub_eq_zero.mpr equality
    change (first + step • xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization first) -
      (second + step • xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization second) = 0 at difference
    rw [map_sub, smul_sub]
    convert difference using 1 <;> abel
  have pairing := congrArg (fun values => inner ℝ values (first - second)) differenceIdentity
  dsimp only at pairing
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, inner_zero_left] at pairing
  have nonnegative := xiNativeFiniteGenerator_nonnegative system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass level resistanceRate normalization rateNonnegative normalizationNonnegative (first - second)
  have normZero : ‖first - second‖ = 0 := by
    nlinarith [norm_nonneg (first - second), mul_nonneg stepPositive.le nonnegative]
  exact sub_eq_zero.mp (norm_eq_zero.mp normZero)

def xiNativeFiniteResolvent (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (step : ℝ) (stepPositive : 0 < step) :
    Lp ℝ 2 (xiVertexSpeedMeasure system mass level) →L[ℝ]
      Lp ℝ 2 (xiVertexSpeedMeasure system mass level) := by
  letI : FiniteDimensional ℝ (Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :=
    (xiNativeEvaluationLinearEquiv system rulesConnected mass level).symm.finiteDimensional
  exact (xiNativeFiniteResolventEquiv system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive).symm.toLinearMap.toContinuousLinearMap

theorem xiNativeFiniteResolvent_properties (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (step : ℝ) (stepPositive : 0 < step) :
    (∀ forcing : Lp ℝ 2 (xiVertexSpeedMeasure system mass level),
      let solution := xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing
      solution + step • xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization solution = forcing ∧
      (∀ values, values + step • xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization values = forcing →
        values = solution) ∧ ‖solution‖ ≤ ‖forcing‖) ∧
    ‖xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive‖ ≤ 1 := by
  have solutions : ∀ forcing : Lp ℝ 2 (xiVertexSpeedMeasure system mass level),
        let solution := xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing
        solution + step • xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization solution = forcing ∧
        (∀ values, values + step • xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization values = forcing →
          values = solution) ∧ ‖solution‖ ≤ ‖forcing‖ := by
    intro forcing
    let solution := xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing
    have solutionIdentity : solution + step •
        xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization solution = forcing :=
      (xiNativeFiniteResolventEquiv system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive).apply_symm_apply forcing
    refine ⟨solutionIdentity, ?_, ?_⟩
    · intro values identity
      apply (xiNativeFiniteResolventEquiv system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive).injective
      exact identity.trans solutionIdentity.symm
    · have pairing := congrArg (fun values => inner ℝ values solution) solutionIdentity
      dsimp only at pairing
      rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at pairing
      have nonnegative := xiNativeFiniteGenerator_nonnegative system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent mass level resistanceRate normalization rateNonnegative normalizationNonnegative solution
      have bound := real_inner_le_norm forcing solution
      by_cases normZero : ‖solution‖ = 0
      · rw [normZero]
        exact norm_nonneg forcing
      · have normPositive : 0 < ‖solution‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm normZero)
        nlinarith [mul_nonneg stepPositive.le nonnegative]
  refine ⟨solutions, ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_⟩
  intro forcing
  simpa only [one_mul] using (solutions forcing).2.2

end
end EIGS

#print axioms EIGS.xiNativeRandomWalk_inner_symmetric
#print axioms EIGS.xiNativeFiniteGenerator_nonnegative
#print axioms EIGS.xiNativeFiniteResolvent_properties
