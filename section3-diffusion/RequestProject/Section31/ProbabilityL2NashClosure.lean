import RequestProject.Section31.QuadraticEnergyClosureRecovery
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! The absolute integral is continuous on probability L². Consequently a
two-scale Nash bound on an original quadratic-form domain passes, with the
same constants, to its constructed closure. No continuous representative of
an arbitrary L² class is required. -/

namespace IGS.Sec31

open MeasureTheory Filter Topology
noncomputable section

variable {Space : Type*} [MeasurableSpace Space]
    (law : Measure Space) [IsProbabilityMeasure law]

theorem probability_L2_integral_abs_le_norm (values : Lp ℝ 2 law) :
    (∫ point, |values point| ∂law) ≤ ‖values‖ := by
  have bound := ENNReal.toReal_mono (Lp.eLpNorm_ne_top values)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      values.aestronglyMeasurable)
  rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm
    values.aestronglyMeasurable, ← Lp.norm_def] at bound
  simpa only [Real.norm_eq_abs] using bound

theorem probability_L2_integral_abs_lipschitz :
    LipschitzWith 1 (fun values : Lp ℝ 2 law => ∫ point, |values point| ∂law) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  have firstIntegrable : Integrable first law := MemLp.integrable (by norm_num) first.memLp
  have secondIntegrable : Integrable second law := MemLp.integrable (by norm_num) second.memLp
  have differenceIdentity :
      (∫ point, |first point - second point| ∂law) =
        ∫ point, |(first - second) point| ∂law :=
    integral_congr_ae ((Lp.coeFn_sub first second).fun_comp abs).symm
  have integralBound :
      |(∫ point, |first point| ∂law) - ∫ point, |second point| ∂law| ≤ ‖first - second‖ := by
    rw [← integral_sub firstIntegrable.norm secondIntegrable.norm]
    calc
      _ ≤ ∫ point, | |first point| - |second point| | ∂law := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun point => |first point| - |second point|)
      _ ≤ ∫ point, |first point - second point| ∂law :=
        integral_mono (firstIntegrable.norm.sub secondIntegrable.norm).norm
          (firstIntegrable.sub secondIntegrable).norm (fun point => by
            simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le (first point) (second point))
      _ ≤ ‖first - second‖ := by
        rw [differenceIdentity]
        exact probability_L2_integral_abs_le_norm law (first - second)
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using integralBound

theorem probability_L2_integral_abs_tendsto
    {Index : Type*} {filter : Filter Index} {sequence : Index → Lp ℝ 2 law}
    {target : Lp ℝ 2 law} (convergence : Tendsto sequence filter (nhds target)) :
    Tendsto (fun index => ∫ point, |sequence index point| ∂law) filter
      (nhds (∫ point, |target point| ∂law)) :=
  (probability_L2_integral_abs_lipschitz law).continuous.continuousAt.tendsto.comp convergence

namespace QuadraticEnergySpace

theorem closedForm_two_scale_bound
    (domain : Submodule ℝ (Lp ℝ 2 law)) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values)
    (closable : SequentiallyClosable domain form)
    (energyCoefficient massCoefficient : ℕ → ℝ)
    (originalBound : ∀ (values : domain) level,
      ‖(values : Lp ℝ 2 law)‖ ^ 2 ≤ energyCoefficient level * form values +
        massCoefficient level * (∫ point, |values.val point| ∂law) ^ 2)
    (target : closedDomain domain form nonnegative) (level : ℕ) :
    ‖(target : Lp ℝ 2 law)‖ ^ 2 ≤
      energyCoefficient level * closedForm domain form nonnegative closable target +
        massCoefficient level * (∫ point, |target.val point| ∂law) ^ 2 := by
  obtain ⟨sequence, stateConvergence, energyConvergence⟩ :=
    exists_original_state_energy_approximation domain form nonnegative closable target
  have integralConvergence := probability_L2_integral_abs_tendsto law stateConvergence
  apply le_of_tendsto_of_tendsto (stateConvergence.norm.pow 2)
    ((tendsto_const_nhds.mul energyConvergence).add
      (tendsto_const_nhds.mul (integralConvergence.pow 2)))
  exact Filter.Eventually.of_forall (fun index => originalBound (sequence index) level)

end QuadraticEnergySpace

end
end IGS.Sec31

#print axioms IGS.Sec31.probability_L2_integral_abs_le_norm
#print axioms IGS.Sec31.probability_L2_integral_abs_lipschitz
#print axioms IGS.Sec31.probability_L2_integral_abs_tendsto
#print axioms IGS.Sec31.QuadraticEnergySpace.closedForm_two_scale_bound
