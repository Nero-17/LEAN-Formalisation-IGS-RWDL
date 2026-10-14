import RequestProject.Section31.EIGSZeroAnchoredMarkov
import Mathlib.Analysis.InnerProductSpace.Dual

/-! Resistance on the actual skeleton is the squared norm of the Riesz
representative of a difference of evaluations in the complete energy space.
The sharp energy inequality and its attained equality identify this quantity
as resistance. The triangle inequality is for this squared norm itself:
positive-part truncation proves the required sign of the cross inner product.
Candidate source: compilation is not claimed. -/

namespace EIGS
open IGS.Sec31
noncomputable section
variable {K : ℕ}

variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (anchor : XiVertexUnion system)

def xiZeroAnchoredDifferenceEvaluation (first second : XiVertexUnion system) :
    xiZeroAnchoredEnergyDomain system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor →L[ℝ] ℝ :=
  ((xiAnchoredEnergyEvaluation system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair anchor first) -
    (xiAnchoredEnergyEvaluation system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair anchor second)).comp
    (xiZeroAnchoredEnergyDomain system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor).subtypeL

def xiSkeletonResistanceRiesz (first second : XiVertexUnion system) :
    xiZeroAnchoredEnergyDomain system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor :=
  (InnerProductSpace.toDual ℝ _).symm
    (xiZeroAnchoredDifferenceEvaluation system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair anchor first second)

theorem xiSkeletonResistanceRiesz_represents (first second : XiVertexUnion system)
    (values : xiZeroAnchoredEnergyDomain system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor) :
    inner ℝ (xiSkeletonResistanceRiesz system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair anchor first second) values =
      values.val.value.val first - values.val.value.val second :=
  InnerProductSpace.toDual_symm_apply

def xiSkeletonResistance (first second : XiVertexUnion system) : ℝ :=
  ‖xiSkeletonResistanceRiesz system rulesConnected resistanceRate ratePositive resistanceVector
    vectorPositive eigenpair anchor first second‖ ^ 2

theorem xiSkeletonResistance_sharp_energy_bound (first second : XiVertexUnion system)
    (values : xiZeroAnchoredEnergyDomain system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor) :
    (values.val.value.val first - values.val.value.val second) ^ 2 ≤
      xiSkeletonResistance system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        eigenpair anchor first second *
      (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        values.val.value.val).toReal := by
  rw [← xiSkeletonResistanceRiesz_represents system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive eigenpair anchor first second values,
    ← xiZeroAnchoredEnergyDomain_norm_sq]
  have bound := abs_real_inner_le_norm
    (xiSkeletonResistanceRiesz system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair anchor first second) values
  have squared := (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg values))).2 bound
  simpa only [sq_abs, mul_pow, xiSkeletonResistance] using squared

theorem xiSkeletonResistanceRiesz_attains (first second : XiVertexUnion system) :
    (xiSkeletonResistanceRiesz system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair anchor first second).val.value.val first -
    (xiSkeletonResistanceRiesz system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair anchor first second).val.value.val second =
    xiSkeletonResistance system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair anchor first second := by
  rw [← xiSkeletonResistanceRiesz_represents system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive eigenpair anchor first second, real_inner_self_eq_norm_sq]
  rfl

theorem xiSkeletonResistanceRiesz_sink_minimum (first second vertex : XiVertexUnion system) :
    0 ≤
      (xiSkeletonResistanceRiesz system rulesConnected resistanceRate ratePositive resistanceVector
        vectorPositive eigenpair anchor first second).val.value.val vertex -
      (xiSkeletonResistanceRiesz system rulesConnected resistanceRate ratePositive resistanceVector
        vectorPositive eigenpair anchor first second).val.value.val second := by
  let representative := xiSkeletonResistanceRiesz system rulesConnected resistanceRate ratePositive resistanceVector
    vectorPositive eigenpair anchor first second
  let positivePart := xiZeroAnchoredPositivePart system rulesConnected resistanceRate ratePositive resistanceVector
    vectorPositive eigenpair anchor representative second
  have sourceValue : representative.val.value.val first - representative.val.value.val second =
      ‖representative‖ ^ 2 :=
    xiSkeletonResistanceRiesz_attains system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair anchor first second
  have sourceNonnegative : 0 ≤ representative.val.value.val first - representative.val.value.val second := by
    rw [sourceValue]
    exact sq_nonneg _
  have truncatedValue : positivePart.val.value.val first - positivePart.val.value.val second =
      ‖representative‖ ^ 2 := by
    simp only [positivePart, xiZeroAnchoredPositivePart_apply, sub_self, max_self,
      max_eq_left sourceNonnegative]
    linarith [sourceValue]
  have innerIdentity : inner ℝ representative positivePart = ‖representative‖ ^ 2 := by
    rw [xiSkeletonResistanceRiesz_represents]
    exact truncatedValue
  have normBound := xiZeroAnchoredPositivePart_norm_sq_le system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive eigenpair anchor representative second
  change ‖positivePart‖ ^ 2 ≤ ‖representative‖ ^ 2 at normBound
  have differenceIdentity := norm_sub_sq_real representative positivePart
  rw [innerIdentity] at differenceIdentity
  have differenceZero : ‖representative - positivePart‖ = 0 := by
    nlinarith [norm_nonneg (representative - positivePart)]
  have equality : representative = positivePart := sub_eq_zero.mp (norm_eq_zero.mp differenceZero)
  have equalityOfDifferences := congrArg (fun values : xiZeroAnchoredEnergyDomain system rulesConnected
    resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor =>
      values.val.value.val vertex - values.val.value.val second) equality
  simp only [positivePart, xiZeroAnchoredPositivePart_apply, sub_self, max_self] at equalityOfDifferences
  have normalized : representative.val.value.val vertex - representative.val.value.val second =
      max (representative.val.value.val vertex - representative.val.value.val second) 0 := by
    linarith [equalityOfDifferences]
  change 0 ≤ representative.val.value.val vertex - representative.val.value.val second
  rw [normalized]
  exact le_max_right _ _

theorem xiSkeletonResistanceRiesz_add (first middle last : XiVertexUnion system) :
    xiSkeletonResistanceRiesz system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair anchor first middle +
    xiSkeletonResistanceRiesz system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair anchor middle last =
    xiSkeletonResistanceRiesz system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair anchor first last := by
  apply ext_inner_right ℝ
  intro values
  rw [inner_add_left, xiSkeletonResistanceRiesz_represents, xiSkeletonResistanceRiesz_represents,
    xiSkeletonResistanceRiesz_represents]
  ring

theorem xiSkeletonResistance_triangle (first middle last : XiVertexUnion system) :
    xiSkeletonResistance system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair anchor first last ≤
    xiSkeletonResistance system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair anchor first middle +
    xiSkeletonResistance system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair anchor middle last := by
  have crossNonpositive :
      inner ℝ
        (xiSkeletonResistanceRiesz system rulesConnected resistanceRate ratePositive resistanceVector
          vectorPositive eigenpair anchor first middle)
        (xiSkeletonResistanceRiesz system rulesConnected resistanceRate ratePositive resistanceVector
          vectorPositive eigenpair anchor middle last) ≤ 0 := by
    rw [real_inner_comm, xiSkeletonResistanceRiesz_represents]
    have minimum := xiSkeletonResistanceRiesz_sink_minimum system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor first middle last
    linarith
  unfold xiSkeletonResistance
  rw [← xiSkeletonResistanceRiesz_add system rulesConnected resistanceRate ratePositive resistanceVector
    vectorPositive eigenpair anchor first middle last, norm_add_sq_real]
  linarith

end
end EIGS

#print axioms EIGS.xiSkeletonResistance_sharp_energy_bound
#print axioms EIGS.xiSkeletonResistanceRiesz_attains
#print axioms EIGS.xiSkeletonResistanceRiesz_sink_minimum
#print axioms EIGS.xiSkeletonResistance_triangle
