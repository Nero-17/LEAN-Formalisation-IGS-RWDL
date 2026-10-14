import RequestProject.Section31.ContinuousTimePathBorel
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Continuous test representation identifies the actual one-time path
marginal with its density measure. The only law input is the one-time FDD
against the same continuous operator. Neither a marginal measure identity
nor equality of independently selected semigroups is assumed. -/

namespace IGS.Sec31.DiscreteMarkov
noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction
variable {State : Type*} [MetricSpace State] [CompactSpace State]
    [MeasurableSpace State] [BorelSpace State]
local instance transitionDensityPathMeasurableSpace : MeasurableSpace C(ℝ≥0, State) := borel _
local instance transitionDensityPathBorelSpace : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

 theorem continuousPath_oneTimeLaw_eq_withDensity_of_representation
    (measure : Measure State) [IsFiniteMeasure measure]
    (law : ProbabilityMeasure C(ℝ≥0, State))
    (operator : C(State, ℝ) →L[ℝ] C(State, ℝ)) (start : State) (time : ℝ≥0)
    (oneTimeObservation : ∀ test : C(State, ℝ),
      (∫ path, test (path time) ∂(law : Measure C(ℝ≥0, State))) = operator test start)
    (density : State → ℝ) (densityContinuous : Continuous density)
    (densityNonnegative : ∀ point, 0 ≤ density point)
    (representation : ∀ test : C(State, ℝ),
      operator test start = ∫ point, density point * test point ∂measure) :
    (law : Measure C(ℝ≥0, State)).map (fun path => path time) =
      measure.withDensity (fun point => ENNReal.ofReal (density point)) := by
  let continuousDensity : C(State, ℝ) := ⟨density, densityContinuous⟩
  have densityIntegrable : Integrable density measure :=
    Integrable.of_bound densityContinuous.measurable.aestronglyMeasurable ‖continuousDensity‖
      (Eventually.of_forall fun point => continuousDensity.norm_coe_le_norm point)
  letI transitionDensityFiniteWeightedMeasure :
      IsFiniteMeasure (measure.withDensity (fun point => ENNReal.ofReal (density point))) :=
    isFiniteMeasure_withDensity_ofReal densityIntegrable.2
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro test
  rw [integral_map (continuous_eval_const time).measurable.aemeasurable
      test.continuous.measurable.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul densityContinuous.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _]
  have toRealDensity (point : State) : (ENNReal.ofReal (density point)).toReal = density point :=
    ENNReal.toReal_ofReal (densityNonnegative point)
  simpa only [toRealDensity, smul_eq_mul] using
    (oneTimeObservation test.toContinuousMap).trans (representation test.toContinuousMap)

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_oneTimeLaw_eq_withDensity_of_representation
