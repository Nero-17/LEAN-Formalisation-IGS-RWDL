import RequestProject.Section31.CountableMarkovKernel
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Measure invariance follows from the actual kernel's continuous-test
representation and the proved preservation of integrals. It is not inserted
as an additional property of the constructed kernel. -/

namespace IGS.Sec31.CountableMarkov

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory BoundedContinuousFunction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
    (measure : Measure X) [IsFiniteMeasure measure]
    (operator : C(X, ℝ) →L[ℝ] Lp ℝ 2 measure)

theorem kernel_invariant_of_continuous_representation
    (kernel : Kernel X X) [IsMarkovKernel kernel]
    (representation : ∀ values : C(X, ℝ), ∀ᵐ point ∂measure,
      (∫ location, values location ∂kernel point) = operator values point)
    (integralPreservation : ∀ values : C(X, ℝ),
      (∫ point, operator values point ∂measure) = ∫ point, values point ∂measure) :
    kernel.Invariant measure := by
  change kernel ∘ₘ measure = measure
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro boundedValues
  have integrable : Integrable boundedValues
      ((kernel ∘ₖ Kernel.const Unit measure) ()) := by
    rw [← Measure.comp_eq_comp_const_apply]
    exact boundedValues.integrable (kernel ∘ₘ measure)
  calc
    (∫ location, boundedValues location ∂(kernel ∘ₘ measure)) =
        ∫ point, ∫ location, boundedValues location ∂kernel point ∂measure := by
      simpa only [← Measure.comp_eq_comp_const_apply, Kernel.const_apply] using
        (Kernel.integral_comp (η := kernel) (κ := Kernel.const Unit measure) (a := ()) integrable)
    _ = ∫ point, operator boundedValues.toContinuousMap point ∂measure :=
      integral_congr_ae (representation boundedValues.toContinuousMap)
    _ = ∫ location, boundedValues location ∂measure :=
      integralPreservation boundedValues.toContinuousMap

theorem fixedTimeKernel_invariant
    (tests : Submodule ℚ C(X, ℝ)) [Countable tests]
    (dense : Dense (tests : Set C(X, ℝ))) (oneMem : (1 : C(X, ℝ)) ∈ tests)
    (supBound : ∀ values : C(X, ℝ),
      ∀ᵐ point ∂measure, |operator values point| ≤ ‖values‖)
    (goodAE : ∀ᵐ point ∂measure, GoodPoint measure operator tests point)
    (integralPreservation : ∀ values : C(X, ℝ),
      (∫ point, operator values point ∂measure) = ∫ point, values point ∂measure)
    (defaultPoint : X) :
    (fixedTimeKernel measure operator tests dense oneMem defaultPoint).Invariant measure := by
  exact kernel_invariant_of_continuous_representation measure operator _
    (ae_fixedTimeKernel_integral measure operator tests dense oneMem supBound goodAE defaultPoint)
    integralPreservation

end IGS.Sec31.CountableMarkov

#print axioms IGS.Sec31.CountableMarkov.kernel_invariant_of_continuous_representation
#print axioms IGS.Sec31.CountableMarkov.fixedTimeKernel_invariant
