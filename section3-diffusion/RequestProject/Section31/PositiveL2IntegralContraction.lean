import RequestProject.Section31.QuadraticEnergySemigroupMarkov
import RequestProject.Section31.QuadraticEnergySemigroupIntegralPreservation
import Mathlib.MeasureTheory.Function.LpOrder

/-! Positivity and preservation of the actual integral imply L¹ contraction
on L² of a finite measure. The closed-form instance supplies positivity from
normal contractions and integral preservation from an actual zero-energy one. -/

namespace IGS.Sec31

open MeasureTheory Filter Topology
open scoped NNReal
noncomputable section

variable {Space : Type*} [MeasurableSpace Space] (law : Measure Space)
    [IsFiniteMeasure law]

theorem positive_integral_preserving_L2_abs_integral_contraction
    (operator : Lp ℝ 2 law →L[ℝ] Lp ℝ 2 law)
    (positive : ∀ values : Lp ℝ 2 law,
      (∀ᵐ point ∂law, 0 ≤ values point) → ∀ᵐ point ∂law, 0 ≤ operator values point)
    (integralPreserving : ∀ values : Lp ℝ 2 law,
      (∫ point, operator values point ∂law) = ∫ point, values point ∂law)
    (values : Lp ℝ 2 law) :
    (∫ point, |operator values point| ∂law) ≤ ∫ point, |values point| ∂law := by
  have operatorNonnegative : ∀ values : Lp ℝ 2 law, 0 ≤ values → 0 ≤ operator values := by
    intro values valuesNonnegative
    exact (Lp.coeFn_nonneg _).mp (positive values ((Lp.coeFn_nonneg _).mpr valuesNonnegative))
  have operatorMonotone : Monotone operator := by
    intro first second ordered
    have difference := operatorNonnegative (second - first) (sub_nonneg.mpr ordered)
    rw [map_sub] at difference
    exact sub_nonneg.mp difference
  have absoluteBound : |operator values| ≤ operator |values| := by
    apply abs_le.mpr
    constructor
    · have bound := operatorMonotone (neg_abs_le values)
      simpa only [map_neg] using bound
    · exact operatorMonotone (le_abs_self values)
  have absoluteBoundAE : ∀ᵐ point ∂law, |operator values point| ≤ operator |values| point := by
    filter_upwards [(Lp.coeFn_le _ _).mpr absoluteBound, Lp.coeFn_abs (operator values)] with point bound identity
    simpa only [identity] using bound
  have imageIntegrable : Integrable (operator values) law := MemLp.integrable (by norm_num) (operator values).memLp
  have absoluteImageIntegrable : Integrable (operator |values|) law := MemLp.integrable (by norm_num) (operator |values|).memLp
  calc
    _ ≤ ∫ point, operator |values| point ∂law := integral_mono_ae imageIntegrable.norm absoluteImageIntegrable absoluteBoundAE
    _ = ∫ point, |values| point ∂law := integralPreserving |values|
    _ = ∫ point, |values point| ∂law := integral_congr_ae (Lp.coeFn_abs values)

namespace QuadraticEnergySpace

theorem closedSemigroup_abs_integral_contraction
    (domain : Submodule ℝ (Lp ℝ 2 law)) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set (Lp ℝ 2 law)))
    (normalContractions : ∀ (contraction : ℝ → ℝ)
      (lipschitz : LipschitzWith 1 contraction) (zero : contraction 0 = 0)
      (target : closedDomain domain form nonnegative),
      ∃ membership : lipschitz.compLp zero target.val ∈ closedDomain domain form nonnegative,
        closedForm domain form nonnegative closable ⟨lipschitz.compLp zero target.val, membership⟩ ≤
          closedForm domain form nonnegative closable target)
    (one : domain) (oneEnergy : form one = 0)
    (oneAE : ∀ᵐ point ∂law, (one : Lp ℝ 2 law) point = 1)
    (time : ℝ≥0) (values : Lp ℝ 2 law) :
    (∫ point, |closedSemigroup domain form nonnegative closable domainDense time values point| ∂law) ≤
      ∫ point, |values point| ∂law :=
  positive_integral_preserving_L2_abs_integral_contraction law
    (closedSemigroup domain form nonnegative closable domainDense time)
    (lp_closedSemigroup_preserves_nonnegative law domain form nonnegative closable domainDense normalContractions time)
    (closedSemigroup_integral_preservation law domain form nonnegative closable domainDense one oneEnergy oneAE time)
    values

end QuadraticEnergySpace
end
end IGS.Sec31

#print axioms IGS.Sec31.positive_integral_preserving_L2_abs_integral_contraction
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_abs_integral_contraction
