import RequestProject.Section31.ContinuousPathRandomShift
import RequestProject.Section31.ContinuousPathFutureBlockReindexing
import RequestProject.Section31.ContinuousPathDenseCylinderUniqueness
import RequestProject.Section31.ContinuousTimePathFamilyMeasurability

/-! Full future-path law at a finite stopping time, for the same global
continuous-path family whose ordered continuous observations are represented
by the given semigroup. Event restrictions may have arbitrary finite mass,
including zero. The input Markov identity is only deterministic and single
time. The output future-path identity is derived through finite products.
The source sigma-field may exceed Borel; the target is explicitly Borel. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal BigOperators BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 7000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable [ambient : MeasurableSpace C(ℝ≥0, State)] [OpensMeasurableSpace C(ℝ≥0, State)]

theorem continuousPath_finite_stoppingTime_futureLaw_markov
    (measure : Measure C(ℝ≥0, State)) [IsFiniteMeasure measure]
    (filtration : Filtration ℝ≥0 ambient)
    (naturalBelow : ∀ time, canonicalContinuousPathFiltration (State := State) time ≤ filtration time)
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (positive : ∀ time (function : C(State, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup time function point)
    (preservesOne : ∀ time, semigroup time 1 = 1)
    (deterministicMarkov : ∀ (time delay : ℝ≥0) (terminal : C(State, ℝ)) (event : Set C(ℝ≥0, State)),
      MeasurableSet[filtration time] event →
      (∫ path in event, terminal (path (time + delay)) ∂measure) =
        ∫ path in event, semigroup delay terminal (path time) ∂measure)
    (globalLaws : State → @ProbabilityMeasure C(ℝ≥0, State) (borel C(ℝ≥0, State)))
    (familyMeasurable : Measurable (fun point =>
      (globalLaws point : @Measure C(ℝ≥0, State) (borel C(ℝ≥0, State)))))
    (orderedObservations : ∀ (start : State) (times : ℕ → ℝ≥0), Monotone times → times 0 = 0 →
      ∀ (tests : ℕ → C(State, ℝ)) (count : ℕ) (terminal : C(State, ℝ)),
        (∫ path, (∏ index : Fin count, tests index.val (path (times index.val))) *
          terminal (path (times count))
          ∂(globalLaws start : @Measure C(ℝ≥0, State) (borel C(ℝ≥0, State)))) =
          ContinuousMarkov.kernelBackwardProduct
            (ContinuousMarkov.semigroupKernel semigroup positive preservesOne)
            ((List.range count).map (fun index => (times (index + 1) - times index, tests index))) terminal start)
    (stoppingTime : C(ℝ≥0, State) → ℝ≥0)
    (stopping : IsStoppingTime filtration (fun path => (stoppingTime path : WithTop ℝ≥0)))
    (event : Set C(ℝ≥0, State)) (eventMeasurable : MeasurableSet[stopping.measurableSpace] event) :
    @Measure.map C(ℝ≥0, State) C(ℝ≥0, State) ambient (borel C(ℝ≥0, State))
        (continuousPathRandomShift stoppingTime) (measure.restrict event) =
      (((continuousPathFamilyKernel globalLaws familyMeasurable).comap
          (fun path : C(ℝ≥0, State) => path (stoppingTime path))
          ((continuousPath_finite_stoppingTime_state_measurable filtration naturalBelow stoppingTime stopping).mono
            stopping.measurableSpace_le le_rfl)) ∘ₖ
        Kernel.const Unit (measure.restrict event)) () := by
  have stoppingTimeMeasurable : Measurable stoppingTime := by
    simpa using stopping.measurable'.untopA
  have shiftMeasurable := continuousPathRandomShift_measurable stoppingTime stoppingTimeMeasurable
  let stoppedKernel : @Kernel C(ℝ≥0, State) C(ℝ≥0, State) ambient (borel C(ℝ≥0, State)) :=
    (continuousPathFamilyKernel globalLaws familyMeasurable).comap
      (fun path => path (stoppingTime path))
      ((continuousPath_finite_stoppingTime_state_measurable filtration naturalBelow stoppingTime stopping).mono
        stopping.measurableSpace_le le_rfl)
  let eventKernel : Kernel Unit C(ℝ≥0, State) := Kernel.const Unit (measure.restrict event)
  letI stoppingFutureLawStoppedKernelMarkov : IsMarkovKernel stoppedKernel := by
    dsimp only [stoppedKernel]
    infer_instance
  change @Measure.map C(ℝ≥0, State) C(ℝ≥0, State) ambient (borel C(ℝ≥0, State))
      (continuousPathRandomShift stoppingTime) (measure.restrict event) = (stoppedKernel ∘ₖ eventKernel) ()
  apply continuousPath_finiteMeasure_eq_of_dense_product_cylinders
    (TopologicalSpace.denseSeq ℝ≥0) (TopologicalSpace.denseRange_denseSeq ℝ≥0)
  intro indices tests
  let cylinder : C(ℝ≥0, State) →ᵇ ℝ :=
    ∏ index : indices, (tests index).compContinuous
      ⟨fun path => path (TopologicalSpace.denseSeq ℝ≥0 index.val),
        continuous_eval_const (TopologicalSpace.denseSeq ℝ≥0 index.val)⟩
  have cylinderApply (path : C(ℝ≥0, State)) : cylinder path =
      ∏ index : indices, tests index (path (TopologicalSpace.denseSeq ℝ≥0 index.val)) := by
    simp only [cylinder, BoundedContinuousFunction.prod_apply, BoundedContinuousFunction.compContinuous_apply,
      ContinuousMap.coe_mk]
  have cylinderMeasurable : @Measurable C(ℝ≥0, State) ℝ
      (borel C(ℝ≥0, State)) (inferInstance : MeasurableSpace ℝ) cylinder := cylinder.continuous.borel_measurable
  have cylinderStronglyMeasurable : StronglyMeasurable[borel C(ℝ≥0, State)] (cylinder : C(ℝ≥0, State) → ℝ) := by
    letI futureCylinderStronglyMeasurableSpace : MeasurableSpace C(ℝ≥0, State) := borel _
    exact cylinderMeasurable.stronglyMeasurable
  let enumeration : indices ≃ Fin (Fintype.card indices) := Fintype.equivFin indices
  let finiteTimes : Fin (Fintype.card indices) → ℝ≥0 :=
    fun index => TopologicalSpace.denseSeq ℝ≥0 (enumeration.symm index).val
  let finiteTests : Fin (Fintype.card indices) → C(State, ℝ) :=
    fun index => (tests (enumeration.symm index)).toContinuousMap
  have enumerateProducts (path : C(ℝ≥0, State)) : cylinder path =
      ∏ index : Fin (Fintype.card indices), finiteTests index (path (finiteTimes index)) := by
    rw [cylinderApply]
    apply Fintype.prod_equiv enumeration
    intro index
    simp only [finiteTests, finiteTimes, Equiv.symm_apply_apply, BoundedContinuousFunction.coe_toContinuousMap]
  obtain ⟨count, times, timesMonotone, startsAtZero, orderedTests, terminal, representation⟩ :=
    FiniteObservationTimeReindexing.exists_monotone_zero_start_product_representation
      (Fintype.card indices) finiteTimes finiteTests
  let observations := (List.range count).map (fun index => (times (index + 1) - times index, orderedTests index))
  let backward : C(State, ℝ) := BanachBackwardObservations.backwardProduct semigroup
    (fun function => ContinuousLinearMap.mul ℝ C(State, ℝ) function) observations terminal
  have cylinderOrdered (path : C(ℝ≥0, State)) : cylinder path =
      (∏ index : Fin count, orderedTests index.val (path (times index.val))) * terminal (path (times count)) :=
    (enumerateProducts path).trans (representation path)
  have familyIntegral (point : State) :
      (∫ path, cylinder path ∂(globalLaws point : @Measure C(ℝ≥0, State) (borel C(ℝ≥0, State)))) = backward point := by
    calc
      _ = ∫ path, (∏ index : Fin count, orderedTests index.val (path (times index.val))) *
          terminal (path (times count))
          ∂(globalLaws point : @Measure C(ℝ≥0, State) (borel C(ℝ≥0, State))) :=
        integral_congr_ae (Eventually.of_forall cylinderOrdered)
      _ = _ := (orderedObservations point times timesMonotone startsAtZero orderedTests count terminal).trans
        (congrFun (ContinuousMarkov.kernelBackwardProduct_eq_semigroupBackwardProduct
          semigroup positive preservesOne observations terminal) point)
  have shiftedCylinder (path : C(ℝ≥0, State)) : cylinder (continuousPathRandomShift stoppingTime path) =
      continuousPathFutureObservationProduct observations terminal path (stoppingTime path) := by
    rw [cylinderOrdered]
    have indexed := continuousPathFutureObservationProduct_indexed path (stoppingTime path)
      times timesMonotone orderedTests terminal count 0
    simpa only [observations, Nat.zero_add, startsAtZero, add_zero, continuousPathRandomShift_apply] using indexed.symm
  have stoppingProduct := continuousPath_finite_stoppingTime_futureBlock_setIntegral_markov
    measure filtration naturalBelow semigroup deterministicMarkov
    (ContinuousMarkov.semigroupKernel semigroup positive preservesOne) (fun _ => inferInstance)
    (ContinuousMarkov.semigroupKernel_integral semigroup positive preservesOne)
    observations terminal stoppingTime stopping (fun _ => 1) measurable_const 1 (by norm_num)
    (fun _ => by norm_num) event eventMeasurable
  have cylinderIntegrable : Integrable cylinder ((stoppedKernel ∘ₖ eventKernel) ()) := by
    letI futureCylinderIntegrableMeasurableSpace : MeasurableSpace C(ℝ≥0, State) := borel _
    letI futureCylinderIntegrableBorelSpace : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩
    exact cylinder.integrable _
  have compositionIntegral := Kernel.integral_comp (κ := eventKernel) (η := stoppedKernel) (a := ()) cylinderIntegrable
  have cylinderIntegralIdentity :
      (∫ path, cylinder path ∂@Measure.map C(ℝ≥0, State) C(ℝ≥0, State) ambient (borel C(ℝ≥0, State))
        (continuousPathRandomShift stoppingTime) (measure.restrict event)) =
      ∫ path, cylinder path ∂(stoppedKernel ∘ₖ eventKernel) () := by
    calc
      _ = ∫ path in event, cylinder (continuousPathRandomShift stoppingTime path) ∂measure :=
        @integral_map_of_stronglyMeasurable C(ℝ≥0, State) ℝ inferInstance inferInstance ambient
          (measure.restrict event) C(ℝ≥0, State) (borel C(ℝ≥0, State))
          (continuousPathRandomShift stoppingTime) shiftMeasurable cylinder cylinderStronglyMeasurable
      _ = ∫ path in event, backward (path (stoppingTime path)) ∂measure := by
        simp_rw [shiftedCylinder]
        simpa only [one_mul] using stoppingProduct
      _ = ∫ path in event, ∫ future, cylinder future
          ∂(globalLaws (path (stoppingTime path)) : @Measure C(ℝ≥0, State) (borel C(ℝ≥0, State))) ∂measure :=
        integral_congr_ae (Eventually.of_forall fun path => (familyIntegral _).symm)
      _ = _ := by
        simpa only [stoppedKernel, eventKernel, continuousPathFamilyKernel,
          Kernel.comap_apply, Kernel.const_apply] using compositionIntegral.symm
  simpa only [cylinderApply] using cylinderIntegralIdentity

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_finite_stoppingTime_futureLaw_markov
