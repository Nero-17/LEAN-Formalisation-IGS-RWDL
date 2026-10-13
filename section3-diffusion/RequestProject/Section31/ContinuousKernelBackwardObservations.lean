import RequestProject.Section31.ContinuousMarkovKernel
import RequestProject.Section31.BanachBackwardObservations
import Mathlib.Analysis.Normed.Operator.Mul

/-! The backward recursion of a continuous semigroup is the genuine finite
nesting of integrals against its Riesz Markov kernels. No finite-dimensional
law or conditional-expectation identity is assumed. -/

namespace IGS.Sec31.ContinuousMarkov

open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [SecondCountableTopology Space] [MeasurableSpace Space] [BorelSpace Space]

def kernelBackwardProduct (kernels : ℝ≥0 → Kernel Space Space) :
    List (ℝ≥0 × C(Space, ℝ)) → C(Space, ℝ) → Space → ℝ
  | [], terminal => terminal
  | observation :: remaining, terminal => fun point => observation.2 point *
      ∫ location, kernelBackwardProduct kernels remaining terminal location ∂kernels observation.1 point

theorem kernelBackwardProduct_eq_semigroupBackwardProduct
    (semigroup : ℝ≥0 → C(Space, ℝ) →L[ℝ] C(Space, ℝ))
    (positive : ∀ time (function : C(Space, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup time function point)
    (preservesOne : ∀ time, semigroup time 1 = 1)
    (observations : List (ℝ≥0 × C(Space, ℝ))) (terminal : C(Space, ℝ)) :
    kernelBackwardProduct (semigroupKernel semigroup positive preservesOne) observations terminal =
      BanachBackwardObservations.backwardProduct semigroup
        (fun function => ContinuousLinearMap.mul ℝ C(Space, ℝ) function) observations terminal := by
  induction observations with
  | nil => rfl
  | cons observation remaining induction =>
      funext point
      change observation.2 point * (∫ location,
        kernelBackwardProduct (semigroupKernel semigroup positive preservesOne) remaining terminal location
          ∂semigroupKernel semigroup positive preservesOne observation.1 point) = _
      rw [induction, semigroupKernel_integral]
      rfl

theorem kernelBackwardProduct_indexed_eq_semigroupBackwardProduct
    (semigroup : ℝ≥0 → C(Space, ℝ) →L[ℝ] C(Space, ℝ))
    (positive : ∀ time (function : C(Space, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup time function point)
    (preservesOne : ∀ time, semigroup time 1 = 1)
    (gaps : ℕ → ℝ≥0) (tests : ℕ → C(Space, ℝ)) (count : ℕ)
    (terminal : C(Space, ℝ)) :
    kernelBackwardProduct (semigroupKernel semigroup positive preservesOne)
      ((List.range count).map (fun index => (gaps index, tests index))) terminal =
      BanachBackwardObservations.backwardProduct (fun index => semigroup (gaps index))
        (fun index => ContinuousLinearMap.mul ℝ C(Space, ℝ) (tests index))
        ((List.range count).map (fun index => (index, index))) terminal := by
  have representation (observations : List (ℕ × ℕ)) :
      kernelBackwardProduct (semigroupKernel semigroup positive preservesOne)
        (observations.map (fun observation => (gaps observation.1, tests observation.2))) terminal =
      BanachBackwardObservations.backwardProduct (fun index => semigroup (gaps index))
        (fun index => ContinuousLinearMap.mul ℝ C(Space, ℝ) (tests index)) observations terminal := by
    induction observations with
    | nil => rfl
    | cons observation remaining induction =>
        funext point
        change tests observation.2 point * (∫ location,
          kernelBackwardProduct (semigroupKernel semigroup positive preservesOne)
            (remaining.map (fun entry => (gaps entry.1, tests entry.2))) terminal location
              ∂semigroupKernel semigroup positive preservesOne (gaps observation.1) point) = _
        rw [induction, semigroupKernel_integral]
        rfl
  simpa only [List.map_map, Function.comp_def] using
    representation ((List.range count).map (fun index => (index, index)))

end
end IGS.Sec31.ContinuousMarkov

#print axioms IGS.Sec31.ContinuousMarkov.kernelBackwardProduct_eq_semigroupBackwardProduct
#print axioms IGS.Sec31.ContinuousMarkov.kernelBackwardProduct_indexed_eq_semigroupBackwardProduct
