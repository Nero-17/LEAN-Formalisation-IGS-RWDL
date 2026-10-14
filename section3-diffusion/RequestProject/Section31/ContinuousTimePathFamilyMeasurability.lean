import RequestProject.Section31.ContinuousTimePathBorel
import RequestProject.Section31.FiniteSupportPathProductUniqueness
import RequestProject.Section31.FiniteObservationTimeReindexing
import RequestProject.Section31.ContinuousKernelBackwardObservations
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Constructions.Cylinders

/-! Measurability of continuous path laws follows from their finite
observations. Countable dense evaluations reduce the assertion to a
Dynkin-class argument on measurable cylinders. For laws whose ordered
products are given by one continuous semigroup, sorting and insertion of
zero give continuous arbitrary product expectations; compact product-test
density gives weak continuity of each finite-dimensional law. Portmanteau
and another Dynkin-class argument then give the required Giry measurability.
Neither finite-dimensional nor full path-law measurability is assumed in
the final semigroup criterion. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal BigOperators BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 5000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

local instance : MeasurableSpace C(ℝ≥0, State) := borel _
local instance : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

theorem measurable_measureFamily_of_finite_coordinates
    {Parameter : Type*} [MeasurableSpace Parameter]
    (laws : Parameter → ProbabilityMeasure (ℕ → State))
    (finiteMeasurable : ∀ indices : Finset ℕ,
      Measurable (fun point => (laws point : Measure (ℕ → State)).map indices.restrict)) :
    Measurable (fun point => (laws point : Measure (ℕ → State))) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (generateFrom_measurableCylinders (α := fun _ : ℕ => State)).symm
    isPiSystem_measurableCylinders
  intro event eventMembership
  obtain ⟨indices, base, baseMeasurable, rfl⟩ :=
    (mem_measurableCylinders event).mp eventMembership
  have cylinderIdentity (point : Parameter) :
      (laws point : Measure (ℕ → State)) (cylinder indices base) =
        ((laws point : Measure (ℕ → State)).map indices.restrict) base := by
    rw [Measure.map_apply (measurable_pi_lambda _ fun index => measurable_pi_apply index.val)
      baseMeasurable]
    rfl
  simpa only [cylinderIdentity] using
    (Measure.measurable_coe baseMeasurable).comp (finiteMeasurable indices)

theorem continuousPathFamily_measure_measurable_of_finite_evaluations
    {Parameter : Type*} [MeasurableSpace Parameter]
    (laws : Parameter → ProbabilityMeasure C(ℝ≥0, State))
    (finiteMeasurable : ∀ (dimension : ℕ) (times : Fin dimension → ℝ≥0),
      Measurable (fun point => (laws point : Measure C(ℝ≥0, State)).map
        (fun path => fun index => path (times index)))) :
    Measurable (fun point => (laws point : Measure C(ℝ≥0, State))) := by
  let denseTimes := TopologicalSpace.denseSeq ℝ≥0
  let denseEvaluation : C(ℝ≥0, State) → ℕ → State := fun path index => path (denseTimes index)
  have denseEmbedding : MeasurableEmbedding denseEvaluation :=
    continuousMap_denseEvaluation_measurableEmbedding denseTimes
      (TopologicalSpace.denseRange_denseSeq ℝ≥0)
  let denseLaws : Parameter → ProbabilityMeasure (ℕ → State) :=
    fun point => (laws point).map denseEmbedding.measurable.aemeasurable
  have denseFiniteMeasurable (indices : Finset ℕ) :
      Measurable (fun point => (denseLaws point : Measure (ℕ → State)).map indices.restrict) := by
    let enumeration : indices ≃ Fin (Fintype.card indices) := Fintype.equivFin indices
    let times : Fin (Fintype.card indices) → ℝ≥0 :=
      fun index => denseTimes (enumeration.symm index).val
    let reorder : (Fin (Fintype.card indices) → State) → indices → State :=
      fun values index => values (enumeration index)
    have reorderedMeasurable :=
      (Measure.measurable_map reorder (measurable_pi_lambda _ fun index =>
        measurable_pi_apply (enumeration index))).comp
          (finiteMeasurable (Fintype.card indices) times)
    convert reorderedMeasurable using 1
    funext point
    change ((laws point : Measure C(ℝ≥0, State)).map denseEvaluation).map indices.restrict =
      ((laws point : Measure C(ℝ≥0, State)).map
        (fun path => fun index : Fin (Fintype.card indices) => path (times index))).map reorder
    have restrictionMeasurable : Measurable
        (indices.restrict : (ℕ → State) → indices → State) :=
      measurable_pi_lambda _ fun (index : indices) => measurable_pi_apply index.val
    rw [Measure.map_map
      restrictionMeasurable denseEmbedding.measurable,
      Measure.map_map (show Measurable reorder from
        measurable_pi_lambda _ fun index => measurable_pi_apply (enumeration index))
        (measurable_pi_lambda _ fun index => (continuous_eval_const (times index)).measurable)]
    congr 1
    funext path index
    change path (denseTimes index.val) = path (denseTimes (enumeration.symm (enumeration index)).val)
    rw [Equiv.symm_apply_apply]
  have denseMeasurable := measurable_measureFamily_of_finite_coordinates denseLaws denseFiniteMeasurable
  apply Measure.measurable_of_measurable_coe
  intro event eventMeasurable
  have imageMeasurable : MeasurableSet (denseEvaluation '' event) :=
    denseEmbedding.measurableSet_image.mpr eventMeasurable
  have eventIdentity (point : Parameter) :
      (denseLaws point : Measure (ℕ → State)) (denseEvaluation '' event) =
        (laws point : Measure C(ℝ≥0, State)) event := by
    change ((laws point : Measure C(ℝ≥0, State)).map denseEvaluation) (denseEvaluation '' event) = _
    rw [Measure.map_apply denseEmbedding.measurable imageMeasurable,
      denseEmbedding.injective.preimage_image]
  simpa only [Function.comp_def, eventIdentity] using
    (Measure.measurable_coe imageMeasurable).comp denseMeasurable

theorem probabilityMeasureFamily_measure_measurable_of_continuous
    {Parameter Outcome : Type*} [TopologicalSpace Parameter] [MeasurableSpace Parameter]
    [OpensMeasurableSpace Parameter] [MetricSpace Outcome] [MeasurableSpace Outcome] [BorelSpace Outcome]
    (laws : Parameter → ProbabilityMeasure Outcome) (lawsContinuous : Continuous laws) :
    Measurable (fun point => (laws point : Measure Outcome)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    BorelSpace.measurable_eq isPiSystem_isOpen
  intro event eventOpen
  have eventLowerSemicontinuous : LowerSemicontinuous (fun point => (laws point : Measure Outcome) event) := by
    apply lowerSemicontinuous_iff_le_liminf.mpr
    intro point
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto lawsContinuous.continuousAt eventOpen
  exact eventLowerSemicontinuous.measurable

theorem continuousPathFamily_finite_product_expectation_continuous
    (laws : State → ProbabilityMeasure C(ℝ≥0, State))
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (positive : ∀ time (function : C(State, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup time function point)
    (preservesOne : ∀ time, semigroup time 1 = 1)
    (orderedObservations : ∀ (start : State) (times : ℕ → ℝ≥0), Monotone times → times 0 = 0 →
      ∀ (tests : ℕ → C(State, ℝ)) (count : ℕ) (terminal : C(State, ℝ)),
        (∫ path, (∏ index : Fin count, tests index.val (path (times index.val))) *
          terminal (path (times count)) ∂(laws start : Measure C(ℝ≥0, State))) =
          ContinuousMarkov.kernelBackwardProduct
            (ContinuousMarkov.semigroupKernel semigroup positive preservesOne)
            ((List.range count).map (fun index => (times (index + 1) - times index, tests index))) terminal start)
    (dimension : ℕ) (times : Fin dimension → ℝ≥0) (tests : Fin dimension → C(State, ℝ)) :
    Continuous (fun start => ∫ path, ∏ index, tests index (path (times index))
      ∂(laws start : Measure C(ℝ≥0, State))) := by
  obtain ⟨count, orderedTimes, timesMonotone, startsAtZero, orderedTests, terminal, representation⟩ :=
    FiniteObservationTimeReindexing.exists_monotone_zero_start_product_representation dimension times tests
  let expectation : C(State, ℝ) := BanachBackwardObservations.backwardProduct semigroup
    (fun function => ContinuousLinearMap.mul ℝ C(State, ℝ) function)
    ((List.range count).map (fun index => (orderedTimes (index + 1) - orderedTimes index, orderedTests index))) terminal
  have expectationIdentity (start : State) :
      (∫ path, ∏ index, tests index (path (times index)) ∂(laws start : Measure C(ℝ≥0, State))) =
        expectation start := by
    calc
      _ = ∫ path, (∏ index : Fin count, orderedTests index.val (path (orderedTimes index.val))) *
          terminal (path (orderedTimes count)) ∂(laws start : Measure C(ℝ≥0, State)) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun path => representation path
      _ = _ := (orderedObservations start orderedTimes timesMonotone startsAtZero orderedTests count terminal).trans
        (congrFun (ContinuousMarkov.kernelBackwardProduct_eq_semigroupBackwardProduct semigroup positive
          preservesOne _ terminal) start)
  exact expectation.continuous.congr (fun start => (expectationIdentity start).symm)

theorem continuousPathFamily_finite_evaluation_continuous
    (laws : State → ProbabilityMeasure C(ℝ≥0, State))
    (productContinuous : ∀ (dimension : ℕ) (times : Fin dimension → ℝ≥0)
      (tests : Fin dimension → C(State, ℝ)),
      Continuous (fun start => ∫ path, ∏ index, tests index (path (times index))
        ∂(laws start : Measure C(ℝ≥0, State))))
    (dimension : ℕ) (times : Fin dimension → ℝ≥0) :
    Continuous (fun start => (laws start).map
      (measurable_pi_lambda _ fun index => (continuous_eval_const (times index)).measurable).aemeasurable) := by
  apply continuous_iff_continuousAt.mpr
  intro start
  apply FiniteProductWeak.weak_tendsto_of_product_integrals
  intro tests
  have productMeasurable : Measurable (fun values : Fin dimension → State =>
      ∏ index, tests index (values index)) :=
    (continuous_finset_prod Finset.univ fun index _ =>
      (tests index).continuous.comp (continuous_apply index)).measurable
  change Tendsto (fun point => ∫ values : Fin dimension → State,
    ∏ index, tests index (values index) ∂(laws point : Measure C(ℝ≥0, State)).map
      (fun path => fun index => path (times index))) (𝓝 start)
        (𝓝 (∫ values : Fin dimension → State, ∏ index, tests index (values index)
          ∂(laws start : Measure C(ℝ≥0, State)).map (fun path => fun index => path (times index))))
  simp_rw [integral_map
    (measurable_pi_lambda _ fun index => (continuous_eval_const (times index)).measurable).aemeasurable
    productMeasurable.aestronglyMeasurable]
  exact (productContinuous dimension times (fun index => (tests index).toContinuousMap)).continuousAt

theorem continuousPathFamily_measure_measurable_of_ordered_observations
    (laws : State → ProbabilityMeasure C(ℝ≥0, State))
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (positive : ∀ time (function : C(State, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup time function point)
    (preservesOne : ∀ time, semigroup time 1 = 1)
    (orderedObservations : ∀ (start : State) (times : ℕ → ℝ≥0), Monotone times → times 0 = 0 →
      ∀ (tests : ℕ → C(State, ℝ)) (count : ℕ) (terminal : C(State, ℝ)),
        (∫ path, (∏ index : Fin count, tests index.val (path (times index.val))) *
          terminal (path (times count)) ∂(laws start : Measure C(ℝ≥0, State))) =
          ContinuousMarkov.kernelBackwardProduct
            (ContinuousMarkov.semigroupKernel semigroup positive preservesOne)
            ((List.range count).map (fun index => (times (index + 1) - times index, tests index))) terminal start) :
    Measurable (fun start => (laws start : Measure C(ℝ≥0, State))) := by
  apply continuousPathFamily_measure_measurable_of_finite_evaluations laws
  intro dimension times
  exact probabilityMeasureFamily_measure_measurable_of_continuous _
    (continuousPathFamily_finite_evaluation_continuous laws
      (continuousPathFamily_finite_product_expectation_continuous laws semigroup positive
        preservesOne orderedObservations) dimension times)

def continuousPathFamilyKernel
    (laws : State → ProbabilityMeasure C(ℝ≥0, State))
    (lawsMeasurable : Measurable (fun start => (laws start : Measure C(ℝ≥0, State)))) :
    Kernel State C(ℝ≥0, State) where
  toFun start := laws start
  measurable' := lawsMeasurable

instance continuousPathFamilyKernel_isMarkov
    (laws : State → ProbabilityMeasure C(ℝ≥0, State))
    (lawsMeasurable : Measurable (fun start => (laws start : Measure C(ℝ≥0, State)))) :
    IsMarkovKernel (continuousPathFamilyKernel laws lawsMeasurable) where
  isProbabilityMeasure start := (laws start).prop

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.measurable_measureFamily_of_finite_coordinates
#print axioms IGS.Sec31.DiscreteMarkov.continuousPathFamily_measure_measurable_of_finite_evaluations
#print axioms IGS.Sec31.DiscreteMarkov.probabilityMeasureFamily_measure_measurable_of_continuous
#print axioms IGS.Sec31.DiscreteMarkov.continuousPathFamily_finite_product_expectation_continuous
#print axioms IGS.Sec31.DiscreteMarkov.continuousPathFamily_finite_evaluation_continuous
#print axioms IGS.Sec31.DiscreteMarkov.continuousPathFamily_measure_measurable_of_ordered_observations
#print axioms IGS.Sec31.DiscreteMarkov.continuousPathFamilyKernel_isMarkov
