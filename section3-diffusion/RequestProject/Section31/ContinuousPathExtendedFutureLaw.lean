import RequestProject.Section31.ContinuousPathStoppingFutureLaw
import RequestProject.Section31.NNRealStoppingTimeLocalization

/-! Full future-path law on the finite-value event of an extended stopping
time. Everywhere finite truncations are used on increasing localized past
events. Continuity from below proves the finite-value-event measure identity.
The arbitrary untopA value outside that event has no probabilistic meaning
and no process value at infinity is asserted. Zero-mass events are included. -/

namespace IGS.Sec31.DiscreteMarkov
open MeasureTheory ProbabilityTheory Set Filter Topology
open IGS.Sec31.StoppingApproximation
open scoped Classical NNReal BigOperators
noncomputable section
set_option maxHeartbeats 7000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable [ambient : MeasurableSpace C(ℝ≥0, State)] [OpensMeasurableSpace C(ℝ≥0, State)]

theorem continuousPath_extended_stoppingTime_futureLaw_markov
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
    (stoppingTime : C(ℝ≥0, State) → WithTop ℝ≥0)
    (stopping : IsStoppingTime filtration stoppingTime)
    (event : Set C(ℝ≥0, State)) (eventMeasurable : MeasurableSet[stopping.measurableSpace] event) :
    @Measure.map C(ℝ≥0, State) C(ℝ≥0, State) ambient (borel C(ℝ≥0, State))
        (continuousPathRandomShift (fun path => (stoppingTime path).untopA))
        (measure.restrict (event ∩ {path | stoppingTime path ≠ ⊤})) =
      (((continuousPathFamilyKernel globalLaws familyMeasurable).comap
          (fun path : C(ℝ≥0, State) => path (stoppingTime path).untopA)
          (continuous_eval.measurable.comp (measurable_id.prodMk stopping.measurable'.untopA))) ∘ₖ
        Kernel.const Unit (measure.restrict (event ∩ {path | stoppingTime path ≠ ⊤}))) () := by
  have timeMeasurable : Measurable (fun path => (stoppingTime path).untopA) := stopping.measurable'.untopA
  have shiftMeasurable := continuousPathRandomShift_measurable _ timeMeasurable
  let stoppedKernel : @Kernel C(ℝ≥0, State) C(ℝ≥0, State) ambient (borel C(ℝ≥0, State)) :=
    (continuousPathFamilyKernel globalLaws familyMeasurable).comap
      (fun path => path (stoppingTime path).untopA)
      (continuous_eval.measurable.comp (measurable_id.prodMk timeMeasurable))
  let localizedEvents (cutoff : ℕ) : Set C(ℝ≥0, State) :=
    event ∩ {path | stoppingTime path ≤ ((cutoff : ℝ≥0) : WithTop ℝ≥0)}
  have eventGlobalMeasurable : MeasurableSet event := stopping.measurableSpace_le _ eventMeasurable
  have localizedMeasurable (cutoff : ℕ) : MeasurableSet (localizedEvents cutoff) :=
    eventGlobalMeasurable.inter (stopping.measurableSpace_le _ (stopping.measurableSet_le' (cutoff : ℝ≥0)))
  have localizedMonotone : Monotone localizedEvents := by
    intro first second ordered path membership
    change path ∈ event ∧ stoppingTime path ≤ ((first : ℝ≥0) : WithTop ℝ≥0) at membership
    change path ∈ event ∧ stoppingTime path ≤ ((second : ℝ≥0) : WithTop ℝ≥0)
    refine ⟨membership.1, membership.2.trans ?_⟩
    exact_mod_cast ordered
  have unionEquality : (⋃ cutoff : ℕ, localizedEvents cutoff) = event ∩ {path | stoppingTime path ≠ ⊤} := by
    dsimp only [localizedEvents]
    rw [← Set.inter_iUnion, iUnion_stoppingTime_le_nat]
  have localizedEquality (cutoff : ℕ) :
      @Measure.map C(ℝ≥0, State) C(ℝ≥0, State) ambient (borel C(ℝ≥0, State))
        (continuousPathRandomShift (fun path => (stoppingTime path).untopA))
        (measure.restrict (localizedEvents cutoff)) =
      (stoppedKernel ∘ₖ Kernel.const Unit (measure.restrict (localizedEvents cutoff))) () := by
    let truncatedTime := finiteTruncation stoppingTime (cutoff : ℝ≥0)
    have truncatedStopping := finiteTruncation_isStoppingTime filtration stoppingTime stopping (cutoff : ℝ≥0)
    have truncatedMeasurable : Measurable truncatedTime := by
      simpa using truncatedStopping.measurable'.untopA
    let truncatedKernel : @Kernel C(ℝ≥0, State) C(ℝ≥0, State) ambient (borel C(ℝ≥0, State)) :=
      (continuousPathFamilyKernel globalLaws familyMeasurable).comap
        (fun path => path (truncatedTime path))
        (continuous_eval.measurable.comp (measurable_id.prodMk truncatedMeasurable))
    have finiteIdentity := continuousPath_finite_stoppingTime_futureLaw_markov
      measure filtration naturalBelow semigroup positive preservesOne deterministicMarkov globalLaws familyMeasurable
      orderedObservations truncatedTime truncatedStopping (localizedEvents cutoff)
      (finiteTruncation_localized_event_measurable filtration stoppingTime stopping (cutoff : ℝ≥0) event eventMeasurable)
    have timesAgree (path : C(ℝ≥0, State)) (membership : path ∈ localizedEvents cutoff) :
        truncatedTime path = (stoppingTime path).untopA :=
      finiteTruncation_eq_of_le stoppingTime (cutoff : ℝ≥0) path membership.2
    calc
      _ = @Measure.map C(ℝ≥0, State) C(ℝ≥0, State) ambient (borel C(ℝ≥0, State))
          (continuousPathRandomShift truncatedTime) (measure.restrict (localizedEvents cutoff)) := by
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem (localizedMeasurable cutoff)] with path membership
        apply ContinuousMap.ext
        intro delay
        simp only [continuousPathRandomShift_apply, timesAgree path membership]
      _ = (truncatedKernel ∘ₖ Kernel.const Unit (measure.restrict (localizedEvents cutoff))) () := finiteIdentity
      _ = _ := by
        apply @Measure.ext C(ℝ≥0, State) (borel C(ℝ≥0, State))
        intro target targetMeasurable
        rw [Kernel.comp_apply' _ _ _ targetMeasurable, Kernel.comp_apply' _ _ _ targetMeasurable,
          Kernel.const_apply]
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (localizedMeasurable cutoff)] with path membership
        simp only [truncatedKernel, stoppedKernel, Kernel.comap_apply, timesAgree path membership]
  change @Measure.map C(ℝ≥0, State) C(ℝ≥0, State) ambient (borel C(ℝ≥0, State))
      (continuousPathRandomShift (fun path => (stoppingTime path).untopA))
      (measure.restrict (event ∩ {path | stoppingTime path ≠ ⊤})) =
    (stoppedKernel ∘ₖ Kernel.const Unit (measure.restrict (event ∩ {path | stoppingTime path ≠ ⊤}))) ()
  apply @Measure.ext C(ℝ≥0, State) (borel C(ℝ≥0, State))
  intro target targetMeasurable
  have preimageMeasurable := shiftMeasurable targetMeasurable
  rw [Measure.map_apply shiftMeasurable targetMeasurable, Measure.restrict_apply preimageMeasurable,
    Kernel.comp_apply' _ _ _ targetMeasurable, Kernel.const_apply, ← unionEquality, Set.inter_iUnion]
  have intersectionMonotone : Monotone (fun cutoff =>
      (continuousPathRandomShift (fun path => (stoppingTime path).untopA)) ⁻¹' target ∩ localizedEvents cutoff) :=
    monotone_const.inter localizedMonotone
  rw [intersectionMonotone.measure_iUnion,
    setLIntegral_iUnion_of_directed (fun path => stoppedKernel path target) localizedMonotone.directed_le]
  apply iSup_congr
  intro cutoff
  have evaluated := congrArg (fun finiteMeasure : @Measure C(ℝ≥0, State) (borel C(ℝ≥0, State)) => finiteMeasure target)
    (localizedEquality cutoff)
  dsimp only at evaluated
  rw [Measure.map_apply shiftMeasurable targetMeasurable, Measure.restrict_apply preimageMeasurable,
    Kernel.comp_apply' _ _ _ targetMeasurable, Kernel.const_apply] at evaluated
  exact evaluated

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_extended_stoppingTime_futureLaw_markov
