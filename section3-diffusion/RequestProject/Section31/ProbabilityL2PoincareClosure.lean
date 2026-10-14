import RequestProject.Section31.QuadraticEnergyPoincareClosure
import Mathlib.MeasureTheory.Function.L2Space

/-! The bounded mean-zero projection realizes variance on probability L².
Recovery therefore transfers a core variance bound to the closed domain,
and zero closed energy gives almost-everywhere constancy. A model consumer
must still prove the original variance bound for its actual energy. -/

namespace IGS.Sec31

open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section

variable {Space : Type*} [MeasurableSpace Space]
    (law : Measure Space) [IsProbabilityMeasure law]

def probabilityL2MeanZeroProjection : Lp ℝ 2 law →L[ℝ] Lp ℝ 2 law :=
  ContinuousLinearMap.id ℝ (Lp ℝ 2 law) -
    (innerSL ℝ (Lp.const 2 law (1 : ℝ))).smulRight (Lp.const 2 law (1 : ℝ))

theorem L2_inner_one_eq_integral (values : Lp ℝ 2 law) :
    inner ℝ (Lp.const 2 law (1 : ℝ)) values = ∫ point, values point ∂law := by
  simpa only [indicatorConstLp_univ, setIntegral_univ] using
    L2.inner_indicatorConstLp_one MeasurableSet.univ (measure_ne_top law Set.univ) values

theorem probabilityL2MeanZeroProjection_ae (values : Lp ℝ 2 law) :
    (probabilityL2MeanZeroProjection law values : Space → ℝ) =ᵐ[law]
      fun point => values point - ∫ other, values other ∂law := by
  simp only [probabilityL2MeanZeroProjection, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  rw [L2_inner_one_eq_integral law values]
  filter_upwards [Lp.coeFn_sub values ((∫ other, values other ∂law) • Lp.const 2 law (1 : ℝ)),
    Lp.coeFn_smul (∫ other, values other ∂law) (Lp.const 2 law (1 : ℝ)),
    Lp.coeFn_const 2 law (1 : ℝ)] with point subtraction scaling constant
  rw [subtraction]
  simp only [Pi.sub_apply]
  rw [scaling]
  simp only [Pi.smul_apply, smul_eq_mul, constant, Function.const_apply, mul_one]

theorem probabilityL2MeanZeroProjection_norm_sq (values : Lp ℝ 2 law) :
    ‖probabilityL2MeanZeroProjection law values‖ ^ 2 =
      ∫ point, (values point - ∫ other, values other ∂law) ^ 2 ∂law := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  apply integral_congr_ae
  exact (probabilityL2MeanZeroProjection_ae law values).fun_comp (fun value : ℝ => value ^ 2)

namespace QuadraticEnergySpace

theorem closedForm_variance_bound
    (domain : Submodule ℝ (Lp ℝ 2 law)) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values)
    (closable : SequentiallyClosable domain form) (constant : ℝ)
    (originalBound : ∀ values : domain,
      (∫ point, (values.val point - ∫ other, values.val other ∂law) ^ 2 ∂law) ≤
        constant * form values)
    (target : closedDomain domain form nonnegative) :
    (∫ point, (target.val point - ∫ other, target.val other ∂law) ^ 2 ∂law) ≤
      constant * closedForm domain form nonnegative closable target := by
  rw [← probabilityL2MeanZeroProjection_norm_sq law target.val]
  apply closedForm_projection_bound domain form nonnegative closable
    (probabilityL2MeanZeroProjection law) constant
  intro values
  rw [probabilityL2MeanZeroProjection_norm_sq]
  exact originalBound values

theorem closedForm_ae_eq_mean_of_variance_bound_and_energy_zero
    (domain : Submodule ℝ (Lp ℝ 2 law)) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values)
    (closable : SequentiallyClosable domain form) (constant : ℝ)
    (originalBound : ∀ values : domain,
      (∫ point, (values.val point - ∫ other, values.val other ∂law) ^ 2 ∂law) ≤
        constant * form values)
    (target : closedDomain domain form nonnegative)
    (zeroEnergy : closedForm domain form nonnegative closable target = 0) :
    ∀ᵐ point ∂law, target.val point = ∫ other, target.val other ∂law := by
  have zeroProjection := closedForm_projection_eq_zero_of_energy_zero domain form
    nonnegative closable (probabilityL2MeanZeroProjection law) constant
    (fun values => by rw [probabilityL2MeanZeroProjection_norm_sq]; exact originalBound values)
    target zeroEnergy
  have representation := probabilityL2MeanZeroProjection_ae law target.val
  rw [zeroProjection] at representation
  filter_upwards [representation, Lp.coeFn_zero (E := ℝ) (p := (2 : ℝ≥0∞)) law] with point identity zero
  rw [zero] at identity
  exact sub_eq_zero.mp identity.symm

end QuadraticEnergySpace
end
end IGS.Sec31

#print axioms IGS.Sec31.L2_inner_one_eq_integral
#print axioms IGS.Sec31.probabilityL2MeanZeroProjection_ae
#print axioms IGS.Sec31.probabilityL2MeanZeroProjection_norm_sq
#print axioms IGS.Sec31.QuadraticEnergySpace.closedForm_variance_bound
#print axioms IGS.Sec31.QuadraticEnergySpace.closedForm_ae_eq_mean_of_variance_bound_and_energy_zero
