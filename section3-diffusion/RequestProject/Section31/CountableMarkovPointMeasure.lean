import RequestProject.Section31.CountableMarkovPointFunctional
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! The actual RMK probability measure of each fixed-time good point's
constructed positive functional. No measurable kernel or all-time law is
asserted. -/

namespace IGS.Sec31.CountableMarkov
open MeasureTheory Filter Topology
open scoped CompactlySupported

set_option maxHeartbeats 2000000

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [BorelSpace X]
    (measure : Measure X) [IsFiniteMeasure measure]
    (operator : C(X, ℝ) →L[ℝ] Lp ℝ 2 measure)
    (tests : Submodule ℚ C(X, ℝ))
    (dense : Dense (tests : Set C(X, ℝ))) (oneMem : (1 : C(X, ℝ)) ∈ tests)

theorem measurableSet_goodPoint [Countable tests] :
    MeasurableSet {point | GoodPoint measure operator tests point} := by
  have outputMeasurable (values : C(X, ℝ)) : Measurable (operator values : X → ℝ) :=
    (Lp.stronglyMeasurable (operator values)).measurable
  have additions : MeasurableSet {point | ∀ first second : tests,
      operator ((first + second : tests) : C(X, ℝ)) point =
        operator (first : C(X, ℝ)) point + operator (second : C(X, ℝ)) point} := by
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro first
    apply MeasurableSet.iInter
    intro second
    exact measurableSet_eq_fun
      (outputMeasurable ((first + second : tests) : C(X, ℝ)))
      ((outputMeasurable (first : C(X, ℝ))).add (outputMeasurable (second : C(X, ℝ))))
  have scalars : MeasurableSet {point | ∀ (scalar : ℚ) (values : tests),
      operator ((scalar • values : tests) : C(X, ℝ)) point =
        scalar • operator (values : C(X, ℝ)) point} := by
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro scalar
    apply MeasurableSet.iInter
    intro values
    exact measurableSet_eq_fun
      (outputMeasurable ((scalar • values : tests) : C(X, ℝ)))
      ((outputMeasurable (values : C(X, ℝ))).const_smul scalar)
  have bounds : MeasurableSet {point | ∀ values : tests,
      |operator (values : C(X, ℝ)) point| ≤ ‖(values : C(X, ℝ))‖} := by
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro values
    exact measurableSet_le
      (outputMeasurable (values : C(X, ℝ))).abs measurable_const
  have positivity : MeasurableSet {point | ∀ values : tests,
      (∀ location, 0 ≤ (values : C(X, ℝ)) location) →
        0 ≤ operator (values : C(X, ℝ)) point} := by
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro values
    by_cases valuesNonnegative : ∀ location, 0 ≤ (values : C(X, ℝ)) location
    · have equality :
          {point | (∀ location, 0 ≤ (values : C(X, ℝ)) location) →
            0 ≤ operator (values : C(X, ℝ)) point} =
          {point | 0 ≤ operator (values : C(X, ℝ)) point} := by
        ext point
        exact ⟨fun implication => implication valuesNonnegative, fun output _ => output⟩
      rw [equality]
      exact measurableSet_le (f := fun _ : X => (0 : ℝ))
        measurable_const (outputMeasurable (values : C(X, ℝ)))
    · simp only [valuesNonnegative, false_implies, Set.setOf_true]
      exact MeasurableSet.univ
  have normalization : MeasurableSet {point | operator 1 point = 1} :=
    measurableSet_eq_fun (outputMeasurable 1) measurable_const
  have equality : {point | GoodPoint measure operator tests point} =
      {point | ∀ first second : tests,
        operator ((first + second : tests) : C(X, ℝ)) point =
          operator (first : C(X, ℝ)) point + operator (second : C(X, ℝ)) point} ∩
      ({point | ∀ (scalar : ℚ) (values : tests),
        operator ((scalar • values : tests) : C(X, ℝ)) point =
          scalar • operator (values : C(X, ℝ)) point} ∩
      ({point | ∀ values : tests,
        |operator (values : C(X, ℝ)) point| ≤ ‖(values : C(X, ℝ))‖} ∩
      ({point | ∀ values : tests, (∀ location, 0 ≤ (values : C(X, ℝ)) location) →
        0 ≤ operator (values : C(X, ℝ)) point} ∩ {point | operator 1 point = 1}))) := by
    ext point
    constructor
    · intro good
      exact ⟨good.add, good.smul, good.bound, good.positive, good.one⟩
    · rintro ⟨addition, scalar, bound, positive, one⟩
      exact ⟨addition, scalar, bound, positive, one⟩
  rw [equality]
  exact additions.inter (scalars.inter (bounds.inter (positivity.inter normalization)))

/-- On the exceptional set use the real evaluation functional at one fixed
default point. This preserves normalization and positivity everywhere. -/
noncomputable def extendedPointFunctional (defaultPoint point : X) : C(X, ℝ) →L[ℝ] ℝ := by
  classical
  exact if good : GoodPoint measure operator tests point then
    pointRealFunctional measure operator tests point good
  else ContinuousMap.evalCLM ℝ defaultPoint

include dense in
theorem extendedPointFunctional_bound (defaultPoint point : X) (values : C(X, ℝ)) :
    ‖extendedPointFunctional measure operator tests defaultPoint point values‖ ≤ ‖values‖ := by
  classical
  by_cases good : GoodPoint measure operator tests point
  · simpa only [extendedPointFunctional, dif_pos good] using
      pointRealFunctional_bound measure operator tests dense point good values
  · simpa only [extendedPointFunctional, dif_neg good, ContinuousMap.evalCLM_apply] using
      values.norm_coe_le_norm defaultPoint

include dense oneMem in
theorem extendedPointFunctional_one (defaultPoint point : X) :
    extendedPointFunctional measure operator tests defaultPoint point 1 = 1 := by
  classical
  by_cases good : GoodPoint measure operator tests point
  · simpa only [extendedPointFunctional, dif_pos good] using
      pointRealFunctional_one measure operator tests dense oneMem point good
  · simp only [extendedPointFunctional, dif_neg good, ContinuousMap.evalCLM_apply, ContinuousMap.one_apply]

include dense oneMem in
theorem extendedPointFunctional_positive (defaultPoint point : X) (values : C(X, ℝ))
    (valuesNonnegative : ∀ location, 0 ≤ values location) :
    0 ≤ extendedPointFunctional measure operator tests defaultPoint point values := by
  classical
  by_cases good : GoodPoint measure operator tests point
  · simpa only [extendedPointFunctional, dif_pos good] using
      pointRealFunctional_positive measure operator tests dense oneMem point good values valuesNonnegative
  · simpa only [extendedPointFunctional, dif_neg good, ContinuousMap.evalCLM_apply] using
      valuesNonnegative defaultPoint

include dense in
theorem extendedPointFunctional_measurable [Countable tests]
    (defaultPoint : X) (values : C(X, ℝ)) :
    Measurable (fun point => extendedPointFunctional measure operator tests defaultPoint point values) := by
  classical
  obtain ⟨approximation, approximationMem, approximationLimit⟩ :=
    mem_closure_iff_seq_limit.mp (dense values)
  let scalarApproximation := fun (index : ℕ) (point : X) =>
    if GoodPoint measure operator tests point then operator (approximation index) point
    else (approximation index) defaultPoint
  have measurableApproximation : ∀ index, Measurable (scalarApproximation index) := by
    intro index
    exact Measurable.ite (measurableSet_goodPoint measure operator tests)
      (Lp.stronglyMeasurable (operator (approximation index))).measurable measurable_const
  apply measurable_of_tendsto_metrizable measurableApproximation
  apply tendsto_pi_nhds.mpr
  intro point
  by_cases good : GoodPoint measure operator tests point
  · have agreement : (fun index => scalarApproximation index point) =
        (fun index => pointRealFunctional measure operator tests point good (approximation index)) := by
      funext index
      simp only [scalarApproximation, if_pos good]
      exact (pointRealFunctional_agrees measure operator tests dense point good
        ⟨approximation index, approximationMem index⟩).symm
    rw [agreement]
    simpa only [extendedPointFunctional, dif_pos good] using
      ((pointRealFunctional measure operator tests point good).continuous.tendsto values).comp approximationLimit
  · simpa only [scalarApproximation, if_neg good, extendedPointFunctional, dif_neg good,
      ContinuousMap.evalCLM_apply] using
      ((ContinuousMap.evalCLM ℝ defaultPoint).continuous.tendsto values).comp approximationLimit

include dense in
theorem extendedPointFunctional_ae_eq
    (supBound : ∀ values : C(X, ℝ),
      ∀ᵐ point ∂measure, |operator values point| ≤ ‖values‖)
    (goodAE : ∀ᵐ point ∂measure, GoodPoint measure operator tests point)
    (defaultPoint : X) (values : C(X, ℝ)) :
    (fun point => extendedPointFunctional measure operator tests defaultPoint point values)
      =ᵐ[measure] operator values := by
  classical
  filter_upwards [goodAE, ae_pointRealFunctional_agrees measure operator tests dense supBound values]
    with point good agreement
  simpa only [extendedPointFunctional, dif_pos good] using agreement good

/-- Restrict the already constructed positive real functional to actual
compactly supported continuous functions. -/
noncomputable def pointPositiveFunctional (point : X)
    (good : GoodPoint measure operator tests point) : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun values := pointRealFunctional measure operator tests point good values.toContinuousMap
      map_add' := by
        intro first second
        exact map_add (pointRealFunctional measure operator tests point good)
          first.toContinuousMap second.toContinuousMap
      map_smul' := by
        intro scalar values
        exact map_smul (pointRealFunctional measure operator tests point good)
          scalar values.toContinuousMap }
    (by
      intro values valuesNonnegative
      exact pointRealFunctional_positive measure operator tests dense oneMem point good
        values.toContinuousMap (fun location => valuesNonnegative location))

/-- The measure is defined by RMK from the actual good-point functional. -/
noncomputable def pointMeasure (point : X)
    (good : GoodPoint measure operator tests point) : Measure X :=
  RealRMK.rieszMeasure (pointPositiveFunctional measure operator tests dense oneMem point good)

instance pointMeasure_finite (point : X) (good : GoodPoint measure operator tests point) :
    IsFiniteMeasure (pointMeasure measure operator tests dense oneMem point good) := by
  unfold pointMeasure
  infer_instance

theorem pointMeasure_integral (point : X) (good : GoodPoint measure operator tests point)
    (values : C(X, ℝ)) :
    ∫ location, values location ∂(pointMeasure measure operator tests dense oneMem point good) =
      pointRealFunctional measure operator tests point good values := by
  exact RealRMK.integral_rieszMeasure
    (pointPositiveFunctional measure operator tests dense oneMem point good)
    ⟨values, HasCompactSupport.of_compactSpace values⟩

theorem pointMeasure_isProbability (point : X) (good : GoodPoint measure operator tests point) :
    IsProbabilityMeasure (pointMeasure measure operator tests dense oneMem point good) := by
  constructor
  apply (ENNReal.toReal_eq_one_iff _).mp
  have identity := pointMeasure_integral measure operator tests dense oneMem point good (1 : C(X, ℝ))
  rw [pointRealFunctional_one measure operator tests dense oneMem point good] at identity
  simpa only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one,
    measureReal_def] using identity

noncomputable def pointProbabilityMeasure (point : X)
    (good : GoodPoint measure operator tests point) : ProbabilityMeasure X :=
  ⟨pointMeasure measure operator tests dense oneMem point good,
    pointMeasure_isProbability measure operator tests dense oneMem point good⟩

theorem pointMeasure_integral_test (point : X) (good : GoodPoint measure operator tests point)
    (values : tests) :
    ∫ location, (values : C(X, ℝ)) location
        ∂(pointMeasure measure operator tests dense oneMem point good) =
      operator (values : C(X, ℝ)) point := by
  rw [pointMeasure_integral measure operator tests dense oneMem point good,
    pointRealFunctional_agrees measure operator tests dense point good]

/-- For each continuous input separately, the represented integral is AE
equal to the actual L2 output at every good point in that AE set. -/
theorem ae_pointMeasure_integral
    (supBound : ∀ values : C(X, ℝ),
      ∀ᵐ point ∂measure, |operator values point| ≤ ‖values‖)
    (values : C(X, ℝ)) :
    ∀ᵐ point ∂measure, ∀ good : GoodPoint measure operator tests point,
      ∫ location, values location ∂(pointMeasure measure operator tests dense oneMem point good) =
        operator values point := by
  filter_upwards [ae_pointRealFunctional_agrees measure operator tests dense supBound values]
    with point agreement
  intro good
  rw [pointMeasure_integral measure operator tests dense oneMem point good]
  exact agreement good

end IGS.Sec31.CountableMarkov

#print axioms IGS.Sec31.CountableMarkov.pointMeasure_integral
#print axioms IGS.Sec31.CountableMarkov.pointMeasure_isProbability
#print axioms IGS.Sec31.CountableMarkov.pointMeasure_integral_test
#print axioms IGS.Sec31.CountableMarkov.ae_pointMeasure_integral
#print axioms IGS.Sec31.CountableMarkov.measurableSet_goodPoint
#print axioms IGS.Sec31.CountableMarkov.extendedPointFunctional_bound
#print axioms IGS.Sec31.CountableMarkov.extendedPointFunctional_one
#print axioms IGS.Sec31.CountableMarkov.extendedPointFunctional_positive
#print axioms IGS.Sec31.CountableMarkov.extendedPointFunctional_measurable
#print axioms IGS.Sec31.CountableMarkov.extendedPointFunctional_ae_eq
