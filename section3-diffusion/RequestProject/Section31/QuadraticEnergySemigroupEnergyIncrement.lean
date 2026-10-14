import RequestProject.Section31.QuadraticEnergyYosidaFormBound
import RequestProject.Section31.BoundedSemigroupEnergyIncrement
import RequestProject.Section31.QuadraticEnergyYosidaDerivativeBound

/-! The original closed energy controls the actual constructed semigroup's
ambient increment, for every closed-domain input. The Yosida strong limit
and the resolvent minimum supply the bound internally. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology
open scoped NNReal

variable {Hilbert : Type*} [NormedAddCommGroup Hilbert]
    [InnerProductSpace ℝ Hilbert] [CompleteSpace Hilbert]

theorem closedSemigroup_energy_increment_sq_le
    (domain : Submodule ℝ Hilbert) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set Hilbert)) (time : ℝ≥0)
    (target : closedDomain domain form nonnegative) :
    ‖closedSemigroup domain form nonnegative closable domainDense time target.val - target.val‖ ^ 2 ≤
      2 * (time : ℝ) * closedForm domain form nonnegative closable target := by
  have convergence := ((closedSemigroup_approximation_limit domain form nonnegative closable domainDense
    time target.val).sub (tendsto_const_nhds (x := target.val))).norm.pow 2
  apply le_of_tendsto convergence
  apply Eventually.of_forall
  intro index
  have incrementBound := BoundedSemigroupEnergyIncrement.positive_exp_apply_sub_self_sq_le
    (yosidaGenerator domain form nonnegative closable domainDense (canonicalYosidaStep index)
      (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index))
    (yosidaGenerator_selfAdjoint domain form nonnegative closable domainDense (canonicalYosidaStep index)
      (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index))
    (yosidaGenerator_pairing_nonnegative domain form nonnegative closable domainDense (canonicalYosidaStep index)
      (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index))
    target.val (time : ℝ) time.coe_nonneg
  have pairingBound := yosida_pairing_le_closed_energy domain form nonnegative closable domainDense
    (canonicalYosidaStep index) (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index) target
  have bound := incrementBound.trans (mul_le_mul_of_nonneg_left pairingBound
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) time.coe_nonneg))
  simpa only [closedSemigroupApproximation, yosidaSemigroup_eq_exp] using bound

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_energy_increment_sq_le
