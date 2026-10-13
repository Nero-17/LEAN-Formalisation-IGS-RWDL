import RequestProject.Section31.QuadraticEnergySemigroupSymmetry
import RequestProject.Section31.QuadraticEnergySemigroupKernel
import Mathlib.MeasureTheory.Function.L2Space

/-! A zero-energy native constant one makes the actual semigroup preserve
integrals. Symmetry and constant preservation are proved inputs from the
constructed operators, rather than an invariant-measure assumption. -/

namespace IGS.Sec31.QuadraticEnergySpace

open MeasureTheory Filter Topology
open scoped NNReal

variable {X : Type*} [MeasurableSpace X] (measure : Measure X)

theorem lp_integrable_of_one (one : Lp ℝ 2 measure)
    (oneAE : ∀ᵐ point ∂measure, one point = 1) (forcing : Lp ℝ 2 measure) :
    Integrable (fun point => forcing point) measure := by
  apply (L2.integrable_inner (𝕜 := ℝ) forcing one).congr
  filter_upwards [oneAE] with point onePoint
  rw [onePoint]
  simp

theorem lp_inner_one_eq_integral (one : Lp ℝ 2 measure)
    (oneAE : ∀ᵐ point ∂measure, one point = 1) (forcing : Lp ℝ 2 measure) :
    inner ℝ forcing one = ∫ point, forcing point ∂measure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [oneAE] with point onePoint
  rw [onePoint]
  simp

theorem closedSemigroup_integral_preservation
    (domain : Submodule ℝ (Lp ℝ 2 measure)) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set (Lp ℝ 2 measure)))
    (one : domain) (oneEnergy : form one = 0)
    (oneAE : ∀ᵐ point ∂measure, (one : Lp ℝ 2 measure) point = 1)
    (time : ℝ≥0) (forcing : Lp ℝ 2 measure) :
    (∫ point, closedSemigroup domain form nonnegative closable domainDense time forcing point ∂measure) =
      ∫ point, forcing point ∂measure := by
  have pairing : inner ℝ (closedSemigroup domain form nonnegative closable domainDense time forcing)
      (one : Lp ℝ 2 measure) = inner ℝ forcing
        (closedSemigroup domain form nonnegative closable domainDense time (one : Lp ℝ 2 measure)) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (closedSemigroup_selfAdjoint domain form nonnegative closable domainDense time)) forcing one
  rw [closedSemigroup_fixed_of_original_energy_zero domain form nonnegative closable domainDense one oneEnergy time] at pairing
  simpa only [lp_inner_one_eq_integral measure (one : Lp ℝ 2 measure) oneAE] using pairing

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.lp_integrable_of_one
#print axioms IGS.Sec31.QuadraticEnergySpace.lp_inner_one_eq_integral
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_integral_preservation
