import RequestProject.Section31.ContinuousPathUsualExtendedFutureLaw
import RequestProject.Section31.ContinuousPathQuasiLeftContinuity

/-! Explicit conservative Hunt-family criteria on the genuine continuous
path carrier. The full extended-stopping future law and bounded Borel future
conditional expectation are mandatory fields. Normality, measurable family,
usual conditions, adaptation, continuous paths, and quasi-left continuity
are separate fields, so none is hidden by the name of the package.

There is no cemetery point in the state carrier. Paths are defined for every
nonnegative finite time; their canonical lifetime is infinity. Probability
mass one of every state marginal is separately certified. This file does not
construct a Skorokhod D Polish space or assert any GHPS transport. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal BigOperators
noncomputable section

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

local instance conservativeHuntPathMeasurableSpace : MeasurableSpace C(ℝ≥0, State) := borel _
local instance conservativeHuntPathBorelSpace : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

def canonicalContinuousPathLifetime (_path : C(ℝ≥0, State)) : WithTop ℝ≥0 := ⊤

structure ContinuousPathConservativeHuntFamilyData
    (globalLaws : State → ProbabilityMeasure C(ℝ≥0, State))
    (familyMeasurable : Measurable (fun start => (globalLaws start : Measure C(ℝ≥0, State)))) : Prop where
  probabilityFamilyMeasurable : Measurable globalLaws
  familyKernelMarkov : IsMarkovKernel (continuousPathFamilyKernel globalLaws familyMeasurable)
  normal : ∀ start, (globalLaws start : Measure C(ℝ≥0, State)).map (fun path => path 0) = Measure.dirac start
  usualRightContinuous : ∀ start, (canonicalUsualContinuousPathFiltration (globalLaws start)).IsRightContinuous
  usualContainsGlobalNull : ∀ start time (event : Set C(ℝ≥0, State)),
    (globalLaws start : Measure C(ℝ≥0, State)) event = 0 →
      MeasurableSet[canonicalUsualContinuousPathFiltration (globalLaws start) time] event
  adapted : ∀ start, StronglyAdapted (canonicalUsualContinuousPathFiltration (globalLaws start))
    canonicalContinuousPathProcess
  strongMarkovFuture : ContinuousPathUsualExtendedFutureLawProperties globalLaws familyMeasurable
  continuousPaths : ∀ path : C(ℝ≥0, State), Continuous (fun time => path time)
  lifetimeInfinite : ∀ path : C(ℝ≥0, State), canonicalContinuousPathLifetime path = ⊤
  conservativeMarginals : ∀ start time,
    ((globalLaws start : Measure C(ℝ≥0, State)).map (fun path => path time)) Set.univ = 1
  quasiLeftContinuous : ∀ (path : C(ℝ≥0, State)) (times : ℕ → WithTop ℝ≥0),
    Monotone times → (⨆ index, times index) ≠ ⊤ →
      Tendsto (fun index => path (times index).untopA) atTop
        (𝓝 (path (⨆ index, times index).untopA))

theorem continuousPath_conservativeHuntFamilyData_of_ordered_observations
    (globalLaws : State → ProbabilityMeasure C(ℝ≥0, State))
    (familyMeasurable : Measurable (fun start => (globalLaws start : Measure C(ℝ≥0, State))))
    (probabilityFamilyMeasurable : Measurable globalLaws)
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (positive : ∀ time (function : C(State, ℝ)), (∀ point, 0 ≤ function point) →
      ∀ point, 0 ≤ semigroup time function point)
    (preservesOne : ∀ time, semigroup time 1 = 1)
    (normal : ∀ start, (globalLaws start : Measure C(ℝ≥0, State)).map (fun path => path 0) = Measure.dirac start)
    (orderedObservations : ∀ (start : State) (times : ℕ → ℝ≥0), Monotone times → times 0 = 0 →
      ∀ (tests : ℕ → C(State, ℝ)) (count : ℕ) (terminal : C(State, ℝ)),
        (∫ path, (∏ index : Fin count, tests index.val (path (times index.val))) *
          terminal (path (times count)) ∂(globalLaws start : Measure C(ℝ≥0, State))) =
          ContinuousMarkov.kernelBackwardProduct
            (ContinuousMarkov.semigroupKernel semigroup positive preservesOne)
            ((List.range count).map (fun index => (times (index + 1) - times index, tests index))) terminal start) :
    ContinuousPathConservativeHuntFamilyData globalLaws familyMeasurable := by
  refine ⟨probabilityFamilyMeasurable, inferInstance, normal, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro start
    change (UsualAugmentation.usualAugmentation (globalLaws start : Measure C(ℝ≥0, State))
      canonicalContinuousPathFiltration).IsRightContinuous
    infer_instance
  · intro start time event eventNull
    exact UsualAugmentation.usualAugmentation_measurableSet_of_null
      (globalLaws start : Measure C(ℝ≥0, State)) canonicalContinuousPathFiltration time event eventNull
  · intro start time
    exact (canonicalContinuousPathProcess_stronglyAdapted time).mono
      (canonicalNatural_le_usualPathFiltration (globalLaws start) time)
  · exact continuousPath_usualExtendedFutureLawProperties_of_ordered_observations
      globalLaws familyMeasurable semigroup positive preservesOne orderedObservations
  · exact fun path => path.continuous
  · exact fun _ => rfl
  · intro start time
    rw [Measure.map_apply (continuous_eval_const time).measurable MeasurableSet.univ,
      Set.preimage_univ, measure_univ]
  · exact fun path times increasing finite =>
      continuousPath_quasiLeftContinuous_at_finite_supremum path times increasing finite

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_conservativeHuntFamilyData_of_ordered_observations
