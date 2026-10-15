import RequestProject.Section31.EIGSSameNativeJointFullHeatEstimatesOfRules
import RequestProject.Section31.ContinuousKernelPowerSpectralDimension

/-! Upgrade the kernel of one supplied conservative Hunt family with the
pure-power heat estimates and all-point spectral dimension. The family, semigroup and kernel are retained. The
one-time marginal identity is exported for that literal kernel.
Candidate source, awaiting compilation; the actual bounded-degree consumer must supply the universal estimates internally. -/

namespace IGS.Sec31.DiscreteMarkov
open MeasureTheory Filter Topology
open scoped Classical NNReal
noncomputable section
variable {State : Type*} [MetricSpace State] [CompactSpace State]
    [MeasurableSpace State] [BorelSpace State]
local instance sameFamilyPowerGlobalPathMeasurable : MeasurableSpace C(ℝ≥0, State) := borel _
local instance sameFamilyPowerGlobalPathBorel : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

def SameFamilyPowerHeatKernelProperties
    (measure : Measure State)
    (embedding : C(State, ℝ) →L[ℝ] Lp ℝ 2 measure)
    (closedSemigroup : ℝ≥0 → Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (exponent : ℝ)
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (globalLaws : State → ProbabilityMeasure C(ℝ≥0, State))
    (familyMeasurable : Measurable (fun start => (globalLaws start : Measure C(ℝ≥0, State))))
    : Prop :=
  ContinuousPathConservativeHuntFamilyData globalLaws familyMeasurable ∧
  ∃ timeThreshold : ℝ, 0 < timeThreshold ∧ ∃ upperConstant : ℝ, 0 < upperConstant ∧
    ∃ kernel : {time : ℝ≥0 // 0 < time} → State → State → ℝ,
      PositiveClosedKernelData measure embedding closedSemigroup exponent semigroup timeThreshold upperConstant kernel ∧
      (∀ (time : {time : ℝ≥0 // 0 < time}) start,
        (globalLaws start : Measure C(ℝ≥0, State)).map (fun path => path time.val) =
          measure.withDensity (fun other => ENNReal.ofReal (kernel time start other))) ∧
      (∃ cutoffTime lowerConstant upperPowerConstant : ℝ,
        0 < cutoffTime ∧ 0 < lowerConstant ∧ 0 < upperPowerConstant ∧
        ∀ time : {time : ℝ≥0 // 0 < time}, (time.val : ℝ) ≤ cutoffTime → ∀ point : State,
          lowerConstant / (time.val : ℝ) ^ exponent ≤ kernel time point point ∧
          kernel time point point ≤ upperPowerConstant / (time.val : ℝ) ^ exponent)
      ∧ ∀ point : State, Tendsto (fun time : ℝ =>
          -2 * Real.log (positiveKernelRealDiagonal kernel time point) / Real.log time)
          (𝓝[>] (0 : ℝ)) (𝓝 (2 * exponent))
theorem sameFamilyPowerHeatKernelProperties_of_same_family
    (measure : Measure State)
    (embedding : C(State, ℝ) →L[ℝ] Lp ℝ 2 measure)
    (closedSemigroup : ℝ≥0 → Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (exponent : ℝ)
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (globalLaws : State → ProbabilityMeasure C(ℝ≥0, State))
    (familyMeasurable : Measurable (fun start => (globalLaws start : Measure C(ℝ≥0, State))))
    (sameFamily : ContinuousPathSameFamilyClosedHeatKernelProperties measure embedding closedSemigroup
      exponent semigroup globalLaws familyMeasurable)
    (fullEstimates : ∀ timeThreshold upperConstant : ℝ, 0 < timeThreshold → 0 < upperConstant →
      ∀ kernel : {time : ℝ≥0 // 0 < time} → State → State → ℝ,
        PositiveClosedKernelData measure embedding closedSemigroup exponent semigroup timeThreshold upperConstant kernel →
        (∃ cutoffTime lowerConstant upperPowerConstant : ℝ,
        0 < cutoffTime ∧ 0 < lowerConstant ∧ 0 < upperPowerConstant ∧
        ∀ time : {time : ℝ≥0 // 0 < time}, (time.val : ℝ) ≤ cutoffTime → ∀ point : State,
          lowerConstant / (time.val : ℝ) ^ exponent ≤ kernel time point point ∧
          kernel time point point ≤ upperPowerConstant / (time.val : ℝ) ^ exponent)) :
    SameFamilyPowerHeatKernelProperties measure embedding closedSemigroup exponent semigroup globalLaws
      familyMeasurable := by
  obtain ⟨huntData, timeThreshold, thresholdPositive, upperConstant, upperPositive,
    kernel, jointlyContinuous, timeSlices⟩ := sameFamily
  have kernelData : PositiveClosedKernelData measure embedding closedSemigroup exponent semigroup
      timeThreshold upperConstant kernel := by
    refine ⟨jointlyContinuous, ?_⟩
    intro time
    obtain ⟨symmetric, strictlyPositive, upperBound, massOne, representation, lifted, marginal⟩ := timeSlices time
    exact ⟨symmetric, strictlyPositive, upperBound, massOne, representation, lifted⟩
  obtain ⟨cutoffTime, lowerConstant, upperPowerConstant, cutoffPositive,
    lowerPositive, upperPowerPositive, bounds⟩ :=
      fullEstimates timeThreshold upperConstant thresholdPositive upperPositive kernel kernelData
  refine ⟨huntData, timeThreshold, thresholdPositive, upperConstant, upperPositive, kernel,
    kernelData, ?_, ⟨cutoffTime, lowerConstant, upperPowerConstant, cutoffPositive,
      lowerPositive, upperPowerPositive, bounds⟩, ?_⟩
  · intro time start
    exact (timeSlices time).2.2.2.2.2.2 start
  · exact positiveKernelRealDiagonal_spectral_dimension_of_power_bounds kernel exponent cutoffTime
      lowerConstant upperPowerConstant cutoffPositive lowerPositive upperPowerPositive bounds
end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.sameFamilyPowerHeatKernelProperties_of_same_family

