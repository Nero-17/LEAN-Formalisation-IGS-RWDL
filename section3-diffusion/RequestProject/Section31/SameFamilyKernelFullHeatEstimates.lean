import RequestProject.Section31.EIGSSameNativeJointFullHeatEstimatesOfRules

/-! Upgrade the kernel of one supplied conservative Hunt family with the
full heat estimates. The family, semigroup and kernel are retained. The
one-time marginal identity is exported for that literal kernel.
Candidate source, awaiting compilation. -/

namespace IGS.Sec31.DiscreteMarkov
open MeasureTheory Filter Topology
open scoped Classical NNReal
noncomputable section
variable {State : Type*} [MetricSpace State] [CompactSpace State]
    [MeasurableSpace State] [BorelSpace State]
local instance : MeasurableSpace C(ℝ≥0, State) := borel _
local instance : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

def SameFamilyFullHeatKernelProperties
    (measure : Measure State)
    (embedding : C(State, ℝ) →L[ℝ] Lp ℝ 2 measure)
    (closedSemigroup : ℝ≥0 → Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (exponent : ℝ)
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (globalLaws : State → ProbabilityMeasure C(ℝ≥0, State))
    (familyMeasurable : Measurable (fun start => (globalLaws start : Measure C(ℝ≥0, State))))
    {Vertex : ℕ → Type*} (vertices : ∀ birth, Vertex birth → State)
    (finiteExponent baseLogExponent : ℝ) : Prop :=
  ContinuousPathConservativeHuntFamilyData globalLaws familyMeasurable ∧
  ∃ timeThreshold : ℝ, 0 < timeThreshold ∧ ∃ upperConstant : ℝ, 0 < upperConstant ∧
    ∃ kernel : {time : ℝ≥0 // 0 < time} → State → State → ℝ,
      PositiveClosedKernelData measure embedding closedSemigroup exponent semigroup timeThreshold upperConstant kernel ∧
      (∀ (time : {time : ℝ≥0 // 0 < time}) start,
        (globalLaws start : Measure C(ℝ≥0, State)).map (fun path => path time.val) =
          measure.withDensity (fun other => ENNReal.ofReal (kernel time start other))) ∧
      PositiveKernelFullHeatEstimates measure vertices finiteExponent exponent baseLogExponent kernel

theorem sameFamilyFullHeatKernelProperties_of_same_family
    (measure : Measure State)
    (embedding : C(State, ℝ) →L[ℝ] Lp ℝ 2 measure)
    (closedSemigroup : ℝ≥0 → Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (exponent : ℝ)
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (globalLaws : State → ProbabilityMeasure C(ℝ≥0, State))
    (familyMeasurable : Measurable (fun start => (globalLaws start : Measure C(ℝ≥0, State))))
    {Vertex : ℕ → Type*} (vertices : ∀ birth, Vertex birth → State)
    (finiteExponent baseLogExponent : ℝ)
    (sameFamily : ContinuousPathSameFamilyClosedHeatKernelProperties measure embedding closedSemigroup
      exponent semigroup globalLaws familyMeasurable)
    (fullEstimates : ∀ timeThreshold upperConstant : ℝ, 0 < timeThreshold → 0 < upperConstant →
      ∀ kernel : {time : ℝ≥0 // 0 < time} → State → State → ℝ,
        PositiveClosedKernelData measure embedding closedSemigroup exponent semigroup timeThreshold upperConstant kernel →
        PositiveKernelFullHeatEstimates measure vertices finiteExponent exponent baseLogExponent kernel) :
    SameFamilyFullHeatKernelProperties measure embedding closedSemigroup exponent semigroup globalLaws
      familyMeasurable vertices finiteExponent baseLogExponent := by
  obtain ⟨huntData, timeThreshold, thresholdPositive, upperConstant, upperPositive,
    kernel, jointlyContinuous, timeSlices⟩ := sameFamily
  have kernelData : PositiveClosedKernelData measure embedding closedSemigroup exponent semigroup
      timeThreshold upperConstant kernel := by
    refine ⟨jointlyContinuous, ?_⟩
    intro time
    obtain ⟨symmetric, strictlyPositive, upperBound, massOne, representation, lifted, marginal⟩ := timeSlices time
    exact ⟨symmetric, strictlyPositive, upperBound, massOne, representation, lifted⟩
  refine ⟨huntData, timeThreshold, thresholdPositive, upperConstant, upperPositive, kernel,
    kernelData, ?_, fullEstimates timeThreshold upperConstant thresholdPositive upperPositive kernel kernelData⟩
  intro time start
  exact (timeSlices time).2.2.2.2.2.2 start

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.sameFamilyFullHeatKernelProperties_of_same_family
