import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Elementary L¹/L² smoothing duality. Indicator tests turn an actual
integral pairing bound into an almost-everywhere bound. Self-adjointness then
transfers an L¹-to-L² estimate to L²-to-L∞ without assuming a kernel density. -/

namespace IGS.Sec31

open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section

variable {Space : Type*} [MeasurableSpace Space] (law : Measure Space) [IsFiniteMeasure law]

theorem L2_ae_le_of_pairing_bound (target : Lp ℝ 2 law) (bound : ℝ)
    (pairingBound : ∀ test : Lp ℝ 2 law,
      inner ℝ test target ≤ bound * (∫ point, |test point| ∂law)) :
    ∀ᵐ point ∂law, target point ≤ bound := by
  have targetIntegrable : Integrable target law :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp target)
  apply ae_le_of_forall_setIntegral_le targetIntegrable (integrable_const bound)
  intro region regionMeasurable regionFinite
  have testIntegral :
      (∫ point, |indicatorConstLp 2 regionMeasurable regionFinite.ne (1 : ℝ) point| ∂law) = law.real region := by
    calc
      _ = ∫ point, region.indicator (fun _ => (1 : ℝ)) point ∂law := by
        apply integral_congr_ae
        filter_upwards [indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := regionMeasurable)
          (hμs := regionFinite.ne) (c := (1 : ℝ))] with point identity
        rw [identity]
        by_cases membership : point ∈ region <;> simp [Set.indicator, membership]
      _ = law.real region := by
        rw [integral_indicator regionMeasurable, setIntegral_const]
        simp
  have estimate := pairingBound (indicatorConstLp 2 regionMeasurable regionFinite.ne (1 : ℝ))
  rw [L2.inner_indicatorConstLp_one regionMeasurable regionFinite.ne, testIntegral] at estimate
  simpa only [setIntegral_const, smul_eq_mul, mul_comm] using estimate

theorem L2_ae_abs_le_of_pairing_bound (target : Lp ℝ 2 law) (bound : ℝ)
    (pairingBound : ∀ test : Lp ℝ 2 law,
      |inner ℝ test target| ≤ bound * (∫ point, |test point| ∂law)) :
    ∀ᵐ point ∂law, |target point| ≤ bound := by
  have upper := L2_ae_le_of_pairing_bound law target bound
    (fun test => (le_abs_self _).trans (pairingBound test))
  have lower := L2_ae_le_of_pairing_bound law (-target) bound (fun test => by
    rw [inner_neg_right]
    exact (neg_le_abs _).trans (pairingBound test))
  filter_upwards [upper, lower, Lp.coeFn_neg target] with point upper lower negation
  rw [negation] at lower
  exact abs_le.mpr ⟨neg_le.mp lower, upper⟩

theorem selfAdjoint_L2_smoothing_ae_bound
    (operator : Lp ℝ 2 law →L[ℝ] Lp ℝ 2 law) (selfAdjoint : IsSelfAdjoint operator)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (smoothing : ∀ values : Lp ℝ 2 law,
      ‖operator values‖ ^ 2 ≤ bound * (∫ point, |values point| ∂law) ^ 2)
    (values : Lp ℝ 2 law) :
    ∀ᵐ point ∂law, |operator values point| ≤ Real.sqrt bound * ‖values‖ := by
  apply L2_ae_abs_le_of_pairing_bound law (operator values) (Real.sqrt bound * ‖values‖)
  intro test
  have integralNonnegative : 0 ≤ ∫ point, |test point| ∂law := integral_nonneg (fun _ => abs_nonneg _)
  have normBound : ‖operator test‖ ≤ Real.sqrt bound * (∫ point, |test point| ∂law) := by
    have productNonnegative : 0 ≤ Real.sqrt bound * (∫ point, |test point| ∂law) := by positivity
    apply (sq_le_sq₀ (norm_nonneg _) productNonnegative).1
    rw [mul_pow, Real.sq_sqrt boundNonnegative]
    exact smoothing test
  calc
    |inner ℝ test (operator values)| = |inner ℝ (operator test) values| := by
      exact congrArg abs (selfAdjoint.isSymmetric test values).symm
    _ ≤ ‖operator test‖ * ‖values‖ := abs_real_inner_le_norm (operator test) values
    _ ≤ (Real.sqrt bound * (∫ point, |test point| ∂law)) * ‖values‖ :=
      mul_le_mul_of_nonneg_right normBound (norm_nonneg _)
    _ = (Real.sqrt bound * ‖values‖) * (∫ point, |test point| ∂law) := by ring

end
end IGS.Sec31

#print axioms IGS.Sec31.L2_ae_le_of_pairing_bound
#print axioms IGS.Sec31.L2_ae_abs_le_of_pairing_bound
#print axioms IGS.Sec31.selfAdjoint_L2_smoothing_ae_bound
