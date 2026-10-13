import RequestProject.Section31.QuadraticEnergySemigroupIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Exact identification of the infinitesimal-generator graph of the actual
constructed semigroup, using contraction and the proved surjectivity of I+A. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology
open scoped NNReal

set_option maxHeartbeats 2000000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H))

theorem closedSemigroup_orbit_norm_antitone (values : H) :
    AntitoneOn (fun time : ℝ =>
      ‖closedSemigroup domain form nonnegative closable domainDense time.toNNReal values‖ ^ 2)
      (Set.Ici 0) := by
  intro firstTime firstNonnegative secondTime secondNonnegative ordered
  change ‖closedSemigroup domain form nonnegative closable domainDense secondTime.toNNReal values‖ ^ 2 ≤
    ‖closedSemigroup domain form nonnegative closable domainDense firstTime.toNNReal values‖ ^ 2
  have decomposition : secondTime.toNNReal =
      (secondTime - firstTime).toNNReal + firstTime.toNNReal := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, Real.coe_toNNReal _ firstNonnegative,
      Real.coe_toNNReal _ secondNonnegative, Real.coe_toNNReal _ (sub_nonneg.mpr ordered)]
    ring
  rw [decomposition, closedSemigroup_add, ContinuousLinearMap.comp_apply]
  have bound := (closedSemigroup domain form nonnegative closable domainDense
    (secondTime - firstTime).toNNReal).le_of_opNorm_le
    (closedSemigroup_norm domain form nonnegative closable domainDense _)
    (closedSemigroup domain form nonnegative closable domainDense firstTime.toNNReal values)
  simp only [one_mul] at bound
  exact pow_le_pow_left₀ (norm_nonneg _) bound 2

theorem closedSemigroup_rightDerivative_nonpositive (values derivative : H)
    (hasDerivative : HasDerivWithinAt (fun time : ℝ =>
      closedSemigroup domain form nonnegative closable domainDense time.toNNReal values)
      derivative (Set.Ici 0) 0) : inner ℝ derivative values ≤ 0 := by
  have scalarDerivative := hasDerivative.inner ℝ hasDerivative
  simp only [Real.toNNReal_zero, closedSemigroup_zero, ContinuousLinearMap.id_apply,
    real_inner_comm values derivative] at scalarDerivative
  have scalarNonpositive := scalarDerivative.nonpos_of_antitoneOn
    ((uniqueDiffOn_Ici (0 : ℝ)) 0 (Set.mem_Ici.mpr le_rfl)).accPt
    (by simpa only [real_inner_self_eq_norm_sq] using
      closedSemigroup_orbit_norm_antitone domain form nonnegative closable domainDense values)
  rw [← real_inner_comm derivative values]
  linarith

theorem closedSemigroup_generator_graph (values derivative : H) :
    HasDerivWithinAt (fun time : ℝ =>
      closedSemigroup domain form nonnegative closable domainDense time.toNNReal values)
      derivative (Set.Ici 0) 0 ↔
    ∃ domainValues : generatorDomain domain form nonnegative closable,
      (domainValues : H) = values ∧
      -(closedGenerator domain form nonnegative closable domainDense domainValues) = derivative := by
  constructor
  · intro hasDerivative
    obtain ⟨domainValues, equation⟩ := closedGenerator_resolvent_surjective
      domain form nonnegative closable domainDense (values - derivative)
    have differenceDerivative := hasDerivative.sub
      (closedSemigroup_hasDerivWithinAt_zero domain form nonnegative closable domainDense domainValues)
    change HasDerivWithinAt (fun time : ℝ =>
      closedSemigroup domain form nonnegative closable domainDense time.toNNReal values -
        closedSemigroup domain form nonnegative closable domainDense time.toNNReal (domainValues : H))
      (derivative - -(closedGenerator domain form nonnegative closable domainDense domainValues))
      (Set.Ici 0) 0 at differenceDerivative
    simp only [← map_sub, sub_neg_eq_add] at differenceDerivative
    have derivativeIdentity : derivative +
        closedGenerator domain form nonnegative closable domainDense domainValues =
      values - (domainValues : H) := by
      apply eq_sub_iff_add_eq.mpr
      simpa only [add_assoc, add_comm, add_left_comm] using (eq_sub_iff_add_eq.mp equation)
    rw [derivativeIdentity] at differenceDerivative
    have nonpositive := closedSemigroup_rightDerivative_nonpositive domain form nonnegative closable
      domainDense (values - (domainValues : H)) (values - (domainValues : H)) differenceDerivative
    have differenceZero : values - (domainValues : H) = 0 :=
      (inner_self_eq_zero (𝕜 := ℝ)).mp (le_antisymm nonpositive real_inner_self_nonneg)
    refine ⟨domainValues, (sub_eq_zero.mp differenceZero).symm, ?_⟩
    rw [differenceZero] at derivativeIdentity
    exact (eq_neg_iff_add_eq_zero.mpr derivativeIdentity).symm
  · rintro ⟨domainValues, rfl, rfl⟩
    exact closedSemigroup_hasDerivWithinAt_zero domain form nonnegative closable domainDense domainValues

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_orbit_norm_antitone
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_rightDerivative_nonpositive
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_generator_graph
