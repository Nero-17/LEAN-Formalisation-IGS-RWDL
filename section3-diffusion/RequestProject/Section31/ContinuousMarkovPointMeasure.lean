import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Every point of a compact space has a probability measure representing a
positive unital continuous-function operator. The probability-valued map is
continuous. Native applications must supply positivity and preservation of
constants from their actual semigroup; these are explicit generic inputs. -/

namespace IGS.Sec31.ContinuousMarkov

open MeasureTheory
open scoped CompactlySupported

variable {Space : Type*} [TopologicalSpace Space] [CompactSpace Space]
  [T2Space Space] [MeasurableSpace Space] [BorelSpace Space]
  (operator : C(Space, ℝ) →L[ℝ] C(Space, ℝ))
  (positive : ∀ function : C(Space, ℝ), (∀ point, 0 ≤ function point) →
    ∀ point, 0 ≤ operator function point)
  (preservesOne : operator 1 = 1)

noncomputable def pointPositiveFunctional (point : Space) : C_c(Space, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun function := operator function.toContinuousMap point
      map_add' := by
        intro first second
        exact congrArg (fun function : C(Space, ℝ) => function point)
          (map_add operator first.toContinuousMap second.toContinuousMap)
      map_smul' := by
        intro scalar function
        exact congrArg (fun function : C(Space, ℝ) => function point)
          (map_smul operator scalar function.toContinuousMap) }
    (by
      intro function functionNonnegative
      exact positive function.toContinuousMap (fun point => functionNonnegative point) point)

noncomputable def pointMeasure (point : Space) : Measure Space :=
  RealRMK.rieszMeasure (pointPositiveFunctional operator positive point)

instance pointMeasure_finite (point : Space) :
    IsFiniteMeasure (pointMeasure operator positive point) := by
  unfold pointMeasure
  infer_instance

theorem pointMeasure_integral (point : Space) (function : C(Space, ℝ)) :
    ∫ location, function location ∂(pointMeasure operator positive point) = operator function point :=
  RealRMK.integral_rieszMeasure (pointPositiveFunctional operator positive point)
    ⟨function, HasCompactSupport.of_compactSpace function⟩

include preservesOne in
theorem pointMeasure_isProbability (point : Space) :
    IsProbabilityMeasure (pointMeasure operator positive point) := by
  constructor
  apply (ENNReal.toReal_eq_one_iff _).mp
  have identity := pointMeasure_integral operator positive point (1 : C(Space, ℝ))
  rw [preservesOne] at identity
  simpa only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one,
    measureReal_def] using identity

noncomputable def pointProbabilityMeasure (point : Space) : ProbabilityMeasure Space :=
  ⟨pointMeasure operator positive point, pointMeasure_isProbability operator positive preservesOne point⟩

theorem pointProbabilityMeasure_integral (point : Space) (function : C(Space, ℝ)) :
    ∫ location, function location ∂(pointProbabilityMeasure operator positive preservesOne point) =
      operator function point :=
  pointMeasure_integral operator positive point function

theorem pointProbabilityMeasure_continuous :
    Continuous (pointProbabilityMeasure operator positive preservesOne) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro function
  simp_rw [pointProbabilityMeasure_integral]
  exact (operator function).continuous

end IGS.Sec31.ContinuousMarkov

#print axioms IGS.Sec31.ContinuousMarkov.pointMeasure_integral
#print axioms IGS.Sec31.ContinuousMarkov.pointMeasure_isProbability
#print axioms IGS.Sec31.ContinuousMarkov.pointProbabilityMeasure_continuous
