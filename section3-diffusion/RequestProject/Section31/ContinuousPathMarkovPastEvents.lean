import RequestProject.Section31.ContinuousPathDeterministicMarkov
import RequestProject.Section31.FiniteProductFiniteMeasureUniqueness
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Continuous finite-product identities extend to finite Borel past events
by uniqueness of finite weighted measures. A Dynkin-class argument then
extends them to every event of the canonical natural filtration. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal BigOperators BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 7000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

local instance continuousMarkovPastEventsMeasurableSpace : MeasurableSpace C(ℝ≥0, State) := borel _
local instance continuousMarkovPastEventsBorelSpace : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

theorem weighted_finite_evaluation_setIntegral_eq
    {Sample Coordinates : Type*} [MeasurableSpace Sample] [Fintype Coordinates]
    (measure : Measure Sample) (values : Sample → Coordinates → State) (valuesMeasurable : Measurable values)
    (firstWeight secondWeight : Sample → ℝ)
    (firstMeasurable : Measurable firstWeight) (secondMeasurable : Measurable secondWeight)
    (firstNonnegative : ∀ sample, 0 ≤ firstWeight sample)
    (secondNonnegative : ∀ sample, 0 ≤ secondWeight sample)
    (firstIntegrable : Integrable firstWeight measure) (secondIntegrable : Integrable secondWeight measure)
    (sameProducts : ∀ tests : Coordinates → State →ᵇ ℝ,
      (∫ sample, (∏ coordinate, tests coordinate (values sample coordinate)) * firstWeight sample ∂measure) =
        ∫ sample, (∏ coordinate, tests coordinate (values sample coordinate)) * secondWeight sample ∂measure)
    (event : Set (Coordinates → State)) (eventMeasurable : MeasurableSet event) :
    (∫ sample in values ⁻¹' event, firstWeight sample ∂measure) =
      ∫ sample in values ⁻¹' event, secondWeight sample ∂measure := by
  letI : IsFiniteMeasure (measure.withDensity (fun sample => ENNReal.ofReal (firstWeight sample))) :=
    isFiniteMeasure_withDensity_ofReal firstIntegrable.2
  letI : IsFiniteMeasure (measure.withDensity (fun sample => ENNReal.ofReal (secondWeight sample))) :=
    isFiniteMeasure_withDensity_ofReal secondIntegrable.2
  have firstToReal (sample : Sample) : (ENNReal.ofReal (firstWeight sample)).toReal = firstWeight sample :=
    ENNReal.toReal_ofReal (firstNonnegative sample)
  have secondToReal (sample : Sample) : (ENNReal.ofReal (secondWeight sample)).toReal = secondWeight sample :=
    ENNReal.toReal_ofReal (secondNonnegative sample)
  have weightedEquality :
      (measure.withDensity (fun sample => ENNReal.ofReal (firstWeight sample))).map values =
        (measure.withDensity (fun sample => ENNReal.ofReal (secondWeight sample))).map values := by
    apply FiniteProductWeak.finiteMeasure_eq_of_product_integrals
    intro tests
    have productMeasurable : Measurable (fun point : Coordinates → State =>
        ∏ coordinate, tests coordinate (point coordinate)) :=
      (continuous_finset_prod Finset.univ fun coordinate _ =>
        (tests coordinate).continuous.comp (continuous_apply coordinate)).measurable
    rw [integral_map valuesMeasurable.aemeasurable productMeasurable.aestronglyMeasurable,
      integral_map valuesMeasurable.aemeasurable productMeasurable.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul firstMeasurable.ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _,
      integral_withDensity_eq_integral_toReal_smul secondMeasurable.ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _]
    simpa only [firstToReal, secondToReal, smul_eq_mul, mul_comm] using sameProducts tests
  have weightedEventEquality := congrArg (fun probability : Measure (Coordinates → State) => probability event)
    weightedEquality
  dsimp only at weightedEventEquality
  rw [Measure.map_apply valuesMeasurable eventMeasurable,
    Measure.map_apply valuesMeasurable eventMeasurable,
    withDensity_apply _ (valuesMeasurable eventMeasurable),
    withDensity_apply _ (valuesMeasurable eventMeasurable)] at weightedEventEquality
  apply (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg firstNonnegative) (integral_nonneg secondNonnegative)).mp
  rw [ofReal_integral_eq_lintegral_ofReal firstIntegrable.integrableOn (Eventually.of_forall firstNonnegative),
    ofReal_integral_eq_lintegral_ofReal secondIntegrable.integrableOn (Eventually.of_forall secondNonnegative)]
  exact weightedEventEquality

def canonicalPastProjection (time : ℝ≥0) (path : C(ℝ≥0, State)) (past : Set.Iic time) : State := path past.val

theorem canonicalContinuousPathFiltration_eq_pastProjection_comap (time : ℝ≥0) :
    canonicalContinuousPathFiltration (State := State) time =
      MeasurableSpace.comap (canonicalPastProjection (State := State) time)
        (inferInstance : MeasurableSpace (Set.Iic time → State)) := by
  change (⨆ past ≤ time, MeasurableSpace.comap (fun path : C(ℝ≥0, State) => path past)
      (inferInstance : MeasurableSpace State)) = _
  apply le_antisymm
  · apply iSup₂_le
    intro past pastBound
    have projectionMeasurable :
        @Measurable C(ℝ≥0, State) (Set.Iic time → State)
          (MeasurableSpace.comap (canonicalPastProjection (State := State) time) inferInstance)
          inferInstance (canonicalPastProjection (State := State) time) := Measurable.of_comap_le le_rfl
    exact ((measurable_pi_apply (⟨past, pastBound⟩ : Set.Iic time)).comp projectionMeasurable).comap_le
  · have projectionMeasurable :
        @Measurable C(ℝ≥0, State) (Set.Iic time → State)
          (⨆ past ≤ time, MeasurableSpace.comap (fun path : C(ℝ≥0, State) => path past)
            (inferInstance : MeasurableSpace State))
          inferInstance (canonicalPastProjection (State := State) time) := by
      letI continuousPastProjectionGeneratorMeasurableSpace : MeasurableSpace C(ℝ≥0, State) :=
        ⨆ past ≤ time, MeasurableSpace.comap (fun path : C(ℝ≥0, State) => path past)
          (inferInstance : MeasurableSpace State)
      change Measurable (fun path : C(ℝ≥0, State) => fun past : Set.Iic time => path past.val)
      apply measurable_pi_lambda
      intro past
      exact Measurable.of_comap_le (le_iSup_of_le past.val (le_iSup_of_le past.property le_rfl))
    exact projectionMeasurable.comap_le

theorem canonicalPast_setIntegral_eq_of_finite_cylinders
    (measure : Measure C(ℝ≥0, State)) (time : ℝ≥0)
    (firstWeight secondWeight : C(ℝ≥0, State) → ℝ)
    (firstIntegrable : Integrable firstWeight measure) (secondIntegrable : Integrable secondWeight measure)
    (totalEquality : (∫ path, firstWeight path ∂measure) = ∫ path, secondWeight path ∂measure)
    (finiteEvents : ∀ (indices : Finset (Set.Iic time)) (base : Set (indices → State)), MeasurableSet base →
      (∫ path in (fun path : C(ℝ≥0, State) => fun index : indices => path index.val.val) ⁻¹' base,
        firstWeight path ∂measure) =
      ∫ path in (fun path : C(ℝ≥0, State) => fun index : indices => path index.val.val) ⁻¹' base,
        secondWeight path ∂measure)
    (event : Set C(ℝ≥0, State))
    (eventMeasurable : MeasurableSet[canonicalContinuousPathFiltration (State := State) time] event) :
    (∫ path in event, firstWeight path ∂measure) = ∫ path in event, secondWeight path ∂measure := by
  let generators : Set (Set C(ℝ≥0, State)) :=
    Set.preimage (canonicalPastProjection (State := State) time) ''
      measurableCylinders (fun _ : Set.Iic time => State)
  have generates : canonicalContinuousPathFiltration (State := State) time =
      MeasurableSpace.generateFrom generators := by
    rw [canonicalContinuousPathFiltration_eq_pastProjection_comap,
      ← generateFrom_measurableCylinders (α := fun _ : Set.Iic time => State),
      MeasurableSpace.comap_generateFrom]
  have generatorsPiSystem : IsPiSystem generators := by
    rintro first ⟨firstBase, firstMembership, rfl⟩ second ⟨secondBase, secondMembership, rfl⟩ intersectionNonempty
    refine ⟨firstBase ∩ secondBase, isPiSystem_measurableCylinders firstBase firstMembership
      secondBase secondMembership ?_, rfl⟩
    obtain ⟨path, firstPath, secondPath⟩ := intersectionNonempty
    exact ⟨canonicalPastProjection time path, firstPath, secondPath⟩
  induction event, eventMeasurable using MeasurableSpace.induction_on_inter generates generatorsPiSystem with
  | empty => simp
  | basic event membership =>
      obtain ⟨base, baseMembership, rfl⟩ := membership
      obtain ⟨indices, baseEvent, baseEventMeasurable, rfl⟩ :=
        (mem_measurableCylinders base).mp baseMembership
      exact finiteEvents indices baseEvent baseEventMeasurable
  | compl event measurableEvent induction =>
      have globalMeasurable := (canonicalContinuousPathFiltration (State := State)).le time event measurableEvent
      rw [setIntegral_compl globalMeasurable firstIntegrable,
        setIntegral_compl globalMeasurable secondIntegrable, totalEquality, induction]
  | iUnion events disjointEvents measurableEvents induction =>
      have globalMeasurable (index : ℕ) :=
        (canonicalContinuousPathFiltration (State := State)).le time (events index) (measurableEvents index)
      rw [integral_iUnion globalMeasurable disjointEvents firstIntegrable.integrableOn,
        integral_iUnion globalMeasurable disjointEvents secondIntegrable.integrableOn]
      exact tsum_congr induction

theorem canonical_eval_continuousTest_integrable
    (law : ProbabilityMeasure C(ℝ≥0, State)) (time : ℝ≥0) (function : C(State, ℝ)) :
    Integrable (fun path : C(ℝ≥0, State) => function (path time)) (law : Measure C(ℝ≥0, State)) :=
  Integrable.of_bound (function.continuous.comp (continuous_eval_const time)).measurable.aestronglyMeasurable
    ‖function‖ (Eventually.of_forall fun path => function.norm_coe_le_norm (path time))

theorem continuousPath_natural_setIntegral_markov_nonnegative
    (law : ProbabilityMeasure C(ℝ≥0, State))
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ)) (start : State)
    (positive : ∀ delay (function : C(State, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup delay function point)
    (observations : ContinuousPathOrderedBanachObservations law semigroup start)
    (time delay : ℝ≥0) (terminal : C(State, ℝ)) (terminalNonnegative : ∀ point, 0 ≤ terminal point)
    (event : Set C(ℝ≥0, State))
    (eventMeasurable : MeasurableSet[canonicalContinuousPathFiltration (State := State) time] event) :
    (∫ path in event, terminal (path (time + delay)) ∂(law : Measure C(ℝ≥0, State))) =
      ∫ path in event, semigroup delay terminal (path time) ∂(law : Measure C(ℝ≥0, State)) := by
  let firstWeight (path : C(ℝ≥0, State)) : ℝ := terminal (path (time + delay))
  let secondWeight (path : C(ℝ≥0, State)) : ℝ := semigroup delay terminal (path time)
  have firstIntegrable : Integrable firstWeight (law : Measure C(ℝ≥0, State)) :=
    canonical_eval_continuousTest_integrable law (time + delay) terminal
  have secondIntegrable : Integrable secondWeight (law : Measure C(ℝ≥0, State)) :=
    canonical_eval_continuousTest_integrable law time (semigroup delay terminal)
  have totalEquality : (∫ path, firstWeight path ∂(law : Measure C(ℝ≥0, State))) =
      ∫ path, secondWeight path ∂(law : Measure C(ℝ≥0, State)) := by
    simpa only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, firstWeight, secondWeight] using
      continuousPath_finite_past_future_factorization law semigroup start observations time delay 0
        (fun index => Fin.elim0 index) (fun index => Fin.elim0 index) (fun index => Fin.elim0 index) terminal
  refine canonicalPast_setIntegral_eq_of_finite_cylinders (law : Measure C(ℝ≥0, State)) time
    firstWeight secondWeight firstIntegrable secondIntegrable totalEquality ?_ event eventMeasurable
  intro indices base baseMeasurable
  refine weighted_finite_evaluation_setIntegral_eq (law : Measure C(ℝ≥0, State))
    (fun path : C(ℝ≥0, State) => fun index : indices => path index.val.val)
    (measurable_pi_lambda _ fun index => (continuous_eval_const index.val.val).measurable)
    firstWeight secondWeight
    (terminal.continuous.comp (continuous_eval_const (time + delay))).measurable
    ((semigroup delay terminal).continuous.comp (continuous_eval_const time)).measurable
    (fun path => terminalNonnegative (path (time + delay)))
    (fun path => positive delay terminal terminalNonnegative (path time))
    firstIntegrable secondIntegrable ?_ base baseMeasurable
  intro tests
  let enumeration : indices ≃ Fin (Fintype.card indices) := Fintype.equivFin indices
  let finiteTimes (index : Fin (Fintype.card indices)) : ℝ≥0 := (enumeration.symm index).val.val
  let finiteTests (index : Fin (Fintype.card indices)) : C(State, ℝ) :=
    (tests (enumeration.symm index)).toContinuousMap
  have productIdentity (path : C(ℝ≥0, State)) :
      (∏ index : Fin (Fintype.card indices), finiteTests index (path (finiteTimes index))) =
        ∏ index : indices, tests index (path index.val.val) :=
    Equiv.prod_comp enumeration.symm (fun index : indices => tests index (path index.val.val))
  have factorization := continuousPath_finite_past_future_factorization law semigroup start observations
    time delay (Fintype.card indices) finiteTimes (fun index => (enumeration.symm index).val.property)
    finiteTests terminal
  simpa only [productIdentity, firstWeight, secondWeight] using factorization

theorem continuousPath_natural_setIntegral_markov
    (law : ProbabilityMeasure C(ℝ≥0, State))
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ)) (start : State)
    (positive : ∀ delay (function : C(State, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup delay function point)
    (observations : ContinuousPathOrderedBanachObservations law semigroup start)
    (time delay : ℝ≥0) (terminal : C(State, ℝ)) (event : Set C(ℝ≥0, State))
    (eventMeasurable : MeasurableSet[canonicalContinuousPathFiltration (State := State) time] event) :
    (∫ path in event, terminal (path (time + delay)) ∂(law : Measure C(ℝ≥0, State))) =
      ∫ path in event, semigroup delay terminal (path time) ∂(law : Measure C(ℝ≥0, State)) := by
  let positivePart : C(State, ℝ) := ⟨fun point => max (terminal point) 0, terminal.continuous.max continuous_const⟩
  let negativePart : C(State, ℝ) := ⟨fun point => max (-terminal point) 0, terminal.continuous.neg.max continuous_const⟩
  have positivePartNonnegative (point : State) : 0 ≤ positivePart point := le_max_right _ _
  have negativePartNonnegative (point : State) : 0 ≤ negativePart point := le_max_right _ _
  have terminalDecomposition : terminal = positivePart - negativePart := by
    ext point
    change terminal point = max (terminal point) 0 - max (-terminal point) 0
    by_cases nonnegative : 0 ≤ terminal point
    · rw [max_eq_left nonnegative, max_eq_right (neg_nonpos.mpr nonnegative), sub_zero]
    · have nonpositive := le_of_not_ge nonnegative
      rw [max_eq_right nonpositive, max_eq_left (neg_nonneg.mpr nonpositive), zero_sub, neg_neg]
  have positiveIdentity := continuousPath_natural_setIntegral_markov_nonnegative law semigroup start positive
    observations time delay positivePart positivePartNonnegative event eventMeasurable
  have negativeIdentity := continuousPath_natural_setIntegral_markov_nonnegative law semigroup start positive
    observations time delay negativePart negativePartNonnegative event eventMeasurable
  rw [terminalDecomposition]
  simp only [map_sub, ContinuousMap.sub_apply]
  rw [integral_sub (canonical_eval_continuousTest_integrable law (time + delay) positivePart).integrableOn
      (canonical_eval_continuousTest_integrable law (time + delay) negativePart).integrableOn,
    integral_sub (canonical_eval_continuousTest_integrable law time (semigroup delay positivePart)).integrableOn
      (canonical_eval_continuousTest_integrable law time (semigroup delay negativePart)).integrableOn,
    positiveIdentity, negativeIdentity]

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.weighted_finite_evaluation_setIntegral_eq
#print axioms IGS.Sec31.DiscreteMarkov.canonicalContinuousPathFiltration_eq_pastProjection_comap
#print axioms IGS.Sec31.DiscreteMarkov.canonicalPast_setIntegral_eq_of_finite_cylinders
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_natural_setIntegral_markov_nonnegative
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_natural_setIntegral_markov

