import RequestProject.Section31.EIGSNativeFiniteResolvent
import RequestProject.Section31.BoundedSemigroupEnergy

/-! Actual finite random-walk semigroups. Contraction follows directly from
nonnegative generator pairings and the derivative of the actual exponential;
neither a spectral representation nor semigroup convergence is assumed. -/

namespace IGS.Sec31.BoundedSemigroupEnergy

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable local instance : NormedAlgebra ℚ (H →L[ℝ] H) :=
  NormedAlgebra.restrictScalars ℚ ℝ (H →L[ℝ] H)

theorem exp_apply_norm_le_of_nonnegative (generator : H →L[ℝ] H)
    (nonnegative : ∀ values, 0 ≤ inner ℝ (generator values) values)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (values : H) :
    ‖NormedSpace.exp ((-time) • generator) values‖ ≤ ‖values‖ := by
  have monotonicity : Antitone (fun parameter : ℝ =>
      ‖NormedSpace.exp ((-parameter) • generator) values‖ ^ 2) := by
    apply antitone_of_hasDerivAt_nonpos (norm_sq_hasDerivAt generator values)
    intro parameter
    have pairingNonnegative := nonnegative (NormedSpace.exp ((-parameter) • generator) values)
    dsimp
    linarith
  have squared := monotonicity timeNonnegative
  simp only [neg_zero, zero_smul, NormedSpace.exp_zero, ContinuousLinearMap.one_apply] at squared
  nlinarith [norm_nonneg (NormedSpace.exp ((-time) • generator) values), norm_nonneg values]

theorem exp_operator_norm_le_of_nonnegative (generator : H →L[ℝ] H)
    (nonnegative : ∀ values, 0 ≤ inner ℝ (generator values) values)
    (time : ℝ) (timeNonnegative : 0 ≤ time) :
    ‖NormedSpace.exp ((-time) • generator)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro values
  simpa only [one_mul] using exp_apply_norm_le_of_nonnegative generator nonnegative time timeNonnegative values

end IGS.Sec31.BoundedSemigroupEnergy

namespace EIGS

open MeasureTheory IGS.Sec31

noncomputable section

set_option maxHeartbeats 2000000

variable {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (mass : XiMassParameters system) (level : ℕ)

noncomputable local instance : NormedAlgebra ℚ
    (Lp ℝ 2 (xiVertexSpeedMeasure system mass level) →L[ℝ]
      Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

include rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativeRandomWalk_selfAdjoint :
    IsSelfAdjoint (xiNativeRandomWalk system rulesConnected mass level) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro first second
  exact (xiNativeRandomWalk_inner_symmetric system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass level first second).symm

include rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativeFiniteGenerator_selfAdjoint (resistanceRate normalization : ℝ) :
    IsSelfAdjoint (xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization) := by
  exact (IsSelfAdjoint.all _).smul
    ((IsSelfAdjoint.one _).sub
      (xiNativeRandomWalk_selfAdjoint system rulesConnected rulesLoopless rulesUnique plantingNonadjacent mass level))

def xiNativeFiniteSemigroup (resistanceRate normalization time : ℝ) :
    Lp ℝ 2 (xiVertexSpeedMeasure system mass level) →L[ℝ]
      Lp ℝ 2 (xiVertexSpeedMeasure system mass level) :=
  NormedSpace.exp ((-time) • xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization)

include rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativeFiniteSemigroup_apply_norm (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (time : ℝ) (timeNonnegative : 0 ≤ time)
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    ‖xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization time values‖ ≤ ‖values‖ :=
  BoundedSemigroupEnergy.exp_apply_norm_le_of_nonnegative _
    (xiNativeFiniteGenerator_nonnegative system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative) time timeNonnegative values

include rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativeFiniteSemigroup_norm (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (time : ℝ) (timeNonnegative : 0 ≤ time) :
    ‖xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization time‖ ≤ 1 :=
  BoundedSemigroupEnergy.exp_operator_norm_le_of_nonnegative _
    (xiNativeFiniteGenerator_nonnegative system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative) time timeNonnegative

@[simp] theorem xiNativeFiniteSemigroup_zero (resistanceRate normalization : ℝ) :
    xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization 0 = 1 := by
  simp only [xiNativeFiniteSemigroup, neg_zero, zero_smul, NormedSpace.exp_zero]

theorem xiNativeFiniteSemigroup_add (resistanceRate normalization firstTime secondTime : ℝ) :
    xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization (firstTime + secondTime) =
      xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization firstTime *
        xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization secondTime := by
  have commuting := ((Commute.refl
    (xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization)).smul_left (-firstTime)).smul_right (-secondTime)
  simpa only [xiNativeFiniteSemigroup, neg_add, add_smul] using NormedSpace.exp_add_of_commute commuting

theorem xiNativeFiniteSemigroup_continuous (resistanceRate normalization : ℝ) :
    Continuous (xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization) :=
  NormedSpace.exp_continuous.comp (continuous_neg.smul continuous_const)

end
end EIGS

#print axioms IGS.Sec31.BoundedSemigroupEnergy.exp_apply_norm_le_of_nonnegative
#print axioms IGS.Sec31.BoundedSemigroupEnergy.exp_operator_norm_le_of_nonnegative
#print axioms EIGS.xiNativeRandomWalk_selfAdjoint
#print axioms EIGS.xiNativeFiniteGenerator_selfAdjoint
#print axioms EIGS.xiNativeFiniteSemigroup_apply_norm
#print axioms EIGS.xiNativeFiniteSemigroup_norm
#print axioms EIGS.xiNativeFiniteSemigroup_zero
#print axioms EIGS.xiNativeFiniteSemigroup_add
#print axioms EIGS.xiNativeFiniteSemigroup_continuous
