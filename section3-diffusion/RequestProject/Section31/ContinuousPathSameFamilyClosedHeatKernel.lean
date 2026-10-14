import RequestProject.Section31.ContinuousPathConservativeHuntCriteria
import RequestProject.Section31.ContinuousPathTransitionDensityIdentification

/-! Attach the full conservative Hunt criteria and a closed-semigroup heat
kernel to one already supplied continuous-path family. The one-time density
measure identity is derived internally from ordered FDD and representation. -/

namespace IGS.Sec31.DiscreteMarkov
noncomputable section
open MeasureTheory Filter Topology
open scoped Classical NNReal BigOperators
variable {State : Type*} [MetricSpace State] [CompactSpace State]
    [MeasurableSpace State] [BorelSpace State]
local instance sameFamilyHeatPathMeasurableSpace : MeasurableSpace C(ℝ≥0, State) := borel _
local instance sameFamilyHeatPathBorelSpace : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

 theorem continuousPath_oneTimeObservation_of_ordered_observations
    (globalLaws : State → ProbabilityMeasure C(ℝ≥0, State))
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (positive : ∀ time (function : C(State, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup time function point)
    (preservesOne : ∀ time, semigroup time 1 = 1)
    (orderedObservations : ∀ (start : State) (times : ℕ → ℝ≥0), Monotone times → times 0 = 0 →
      ∀ (tests : ℕ → C(State, ℝ)) (count : ℕ) (terminal : C(State, ℝ)),
        (∫ path, (∏ index : Fin count, tests index.val (path (times index.val))) * terminal (path (times count))
          ∂(globalLaws start : Measure C(ℝ≥0, State))) =
          ContinuousMarkov.kernelBackwardProduct
            (ContinuousMarkov.semigroupKernel semigroup positive preservesOne)
            ((List.range count).map (fun index => (times (index + 1) - times index, tests index))) terminal start)
    (start : State) (time : ℝ≥0) (test : C(State, ℝ)) :
    (∫ path, test (path time) ∂(globalLaws start : Measure C(ℝ≥0, State))) = semigroup time test start := by
  let times : ℕ → ℝ≥0 := fun index => if index = 0 then 0 else time
  have timesMonotone : Monotone times := by
    intro first second ordered
    by_cases firstZero : first = 0
    · subst first
      simp only [times, if_pos rfl]
      exact zero_le _
    · have secondNonzero : second ≠ 0 := by omega
      simp only [times, if_neg firstZero, if_neg secondNonzero]
      exact le_rfl
  have observed := orderedObservations start times timesMonotone (by simp [times])
    (fun _ => (1 : C(State, ℝ))) 1 test
  simpa [times, ContinuousMarkov.kernelBackwardProduct, ContinuousMarkov.semigroupKernel_integral] using observed

 def ContinuousPathSameFamilyClosedHeatKernelProperties
    (measure : Measure State)
    (embedding : C(State, ℝ) →L[ℝ] Lp ℝ 2 measure)
    (closedSemigroup : ℝ≥0 → Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (exponent : ℝ)
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (globalLaws : State → ProbabilityMeasure C(ℝ≥0, State))
    (familyMeasurable : Measurable (fun start => (globalLaws start : Measure C(ℝ≥0, State)))) : Prop :=
  ContinuousPathConservativeHuntFamilyData globalLaws familyMeasurable ∧
  ∃ timeThreshold : ℝ, 0 < timeThreshold ∧ ∃ upperConstant : ℝ, 0 < upperConstant ∧
    ∃ kernel : {time : ℝ≥0 // 0 < time} → State → State → ℝ,
      Continuous (fun point : {time : ℝ≥0 // 0 < time} × State × State => kernel point.1 point.2.1 point.2.2) ∧
      ∀ time : {time : ℝ≥0 // 0 < time},
        (∀ first second, kernel time first second = kernel time second first) ∧
        (∀ first second, 0 < kernel time first second) ∧
        (∀ first second, kernel time first second ≤ upperConstant /
          (min ((time.val : ℝ) / 2) timeThreshold) ^ exponent) ∧
        (∀ point, (∫ other, kernel time point other ∂measure) = 1) ∧
        (∀ (function : C(State, ℝ)) point,
          semigroup time.val function point = ∫ other, kernel time point other * function other ∂measure) ∧
        (∃ lifted : Lp ℝ 2 measure →L[ℝ] C(State, ℝ),
          (∀ forcing point, lifted forcing point = ∫ other, kernel time point other * forcing other ∂measure) ∧
          ∀ forcing, embedding (lifted forcing) = closedSemigroup time.val forcing) ∧
        ∀ start, (globalLaws start : Measure C(ℝ≥0, State)).map (fun path => path time.val) =
          measure.withDensity (fun other => ENNReal.ofReal (kernel time start other))

 theorem continuousPath_sameFamilyClosedHeatKernelProperties_of_kernel
    (measure : Measure State) [IsFiniteMeasure measure]
    (embedding : C(State, ℝ) →L[ℝ] Lp ℝ 2 measure)
    (closedSemigroup : ℝ≥0 → Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (exponent : ℝ)
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (positive : ∀ time (function : C(State, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup time function point)
    (preservesOne : ∀ time, semigroup time 1 = 1)
    (globalLaws : State → ProbabilityMeasure C(ℝ≥0, State))
    (familyMeasurable : Measurable (fun start => (globalLaws start : Measure C(ℝ≥0, State))))
    (probabilityFamilyMeasurable : Measurable globalLaws)
    (normal : ∀ start, (globalLaws start : Measure C(ℝ≥0, State)).map (fun path => path 0) = Measure.dirac start)
    (orderedObservations : ∀ (start : State) (times : ℕ → ℝ≥0), Monotone times → times 0 = 0 →
      ∀ (tests : ℕ → C(State, ℝ)) (count : ℕ) (terminal : C(State, ℝ)),
        (∫ path, (∏ index : Fin count, tests index.val (path (times index.val))) * terminal (path (times count))
          ∂(globalLaws start : Measure C(ℝ≥0, State))) =
          ContinuousMarkov.kernelBackwardProduct
            (ContinuousMarkov.semigroupKernel semigroup positive preservesOne)
            ((List.range count).map (fun index => (times (index + 1) - times index, tests index))) terminal start)
    (timeThreshold : ℝ) (timeThresholdPositive : 0 < timeThreshold)
    (upperConstant : ℝ) (upperConstantPositive : 0 < upperConstant)
    (kernel : {time : ℝ≥0 // 0 < time} → State → State → ℝ)
    (jointContinuous : Continuous
      (fun point : {time : ℝ≥0 // 0 < time} × State × State => kernel point.1 point.2.1 point.2.2))
    (density : ∀ time : {time : ℝ≥0 // 0 < time},
      (∀ first second, kernel time first second = kernel time second first) ∧
      (∀ first second, 0 < kernel time first second) ∧
      (∀ first second, kernel time first second ≤ upperConstant /
        (min ((time.val : ℝ) / 2) timeThreshold) ^ exponent) ∧
      (∀ point, (∫ other, kernel time point other ∂measure) = 1) ∧
      (∀ (function : C(State, ℝ)) point,
        semigroup time.val function point = ∫ other, kernel time point other * function other ∂measure) ∧
      ∃ lifted : Lp ℝ 2 measure →L[ℝ] C(State, ℝ),
        (∀ forcing point, lifted forcing point = ∫ other, kernel time point other * forcing other ∂measure) ∧
        ∀ forcing, embedding (lifted forcing) = closedSemigroup time.val forcing) :
    ContinuousPathSameFamilyClosedHeatKernelProperties measure embedding closedSemigroup exponent
      semigroup globalLaws familyMeasurable := by
  refine ⟨continuousPath_conservativeHuntFamilyData_of_ordered_observations globalLaws familyMeasurable
    probabilityFamilyMeasurable semigroup positive preservesOne normal orderedObservations,
    timeThreshold, timeThresholdPositive, upperConstant, upperConstantPositive, kernel, jointContinuous, ?_⟩
  intro time
  obtain ⟨symmetric, strictlyPositive, upper, massOne, representation, lifted, liftedRepresentation,
    liftedCompatibility⟩ := density time
  refine ⟨symmetric, strictlyPositive, upper, massOne, representation,
    ⟨lifted, liftedRepresentation, liftedCompatibility⟩, ?_⟩
  intro start
  apply continuousPath_oneTimeLaw_eq_withDensity_of_representation measure (globalLaws start)
    (semigroup time.val) start time.val
    (continuousPath_oneTimeObservation_of_ordered_observations globalLaws semigroup positive preservesOne
      orderedObservations start time.val) (kernel time start)
    (jointContinuous.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)))
    (fun point => (strictlyPositive start point).le)
  exact fun test => representation test start

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_oneTimeObservation_of_ordered_observations
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_sameFamilyClosedHeatKernelProperties_of_kernel
