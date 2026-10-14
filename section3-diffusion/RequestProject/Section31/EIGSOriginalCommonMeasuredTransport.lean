import RequestProject.Section31.CommonRealisationMeasuredTransport
import RequestProject.Section31.EIGSOriginalCountableRealisation

/-! The actual vertex and speed measures converge in any of the constructed
common realizations whose source points approach their projected target points.
The native weak limits are invoked internally. The same target is retained;
there is no new choice of a spatial or path-law witness. -/

namespace EIGS.MeasuredGHP
noncomputable section
open MeasureTheory Filter Topology Metric Set IGS.Sec31
open scoped Classical
variable {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    {Ambient : Type*} [MetricSpace Ambient] [CompactSpace Ambient]
    [MeasurableSpace Ambient] [BorelSpace Ambient]
    (target : XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair → Ambient)
    (targetContinuous : Continuous target)
    (sources : ∀ level, XiVtx system level → Ambient)
    (radii : ℕ → ℝ) (radiiNonnegative : ∀ level, 0 ≤ radii level)
    (radiiZero : Tendsto radii atTop (𝓝 0))
    (displacement : ∀ level vertex,
      dist (sources level vertex) (target (xiCompletionEmbedding system connected lengths
        lengthsPositive rate (zero_lt_one.trans rateGreaterThanOne) eigenpair level vertex)) ≤ radii level)

include radii radiiNonnegative radiiZero displacement

 theorem xiOriginalCommon_images_converge_of_native_weak
    (mass : XiMassParameters system)
    (finiteLaws : ∀ level, ProbabilityMeasure (XiVtx system level))
    (imageLaws : ℕ → ProbabilityMeasure (XiMetricCompletion system connected lengths
      lengthsPositive rate (zero_lt_one.trans rateGreaterThanOne) eigenpair))
    (images : ∀ level, (finiteLaws level).toMeasure.map
      (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level) = (imageLaws level).toMeasure)
    (nativeWeak : Tendsto imageLaws atTop
      (𝓝 (xiLimitProbabilityMeasure system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass))) :
    Tendsto (fun level => (finiteLaws level).map
      (show Measurable (sources level) from Measurable.of_discrete).aemeasurable) atTop
      (𝓝 ((xiLimitProbabilityMeasure system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass).map targetContinuous.measurable.aemeasurable)) ∧
    Tendsto (fun level => levyProkhorovDist
      ((finiteLaws level).map
        (show Measurable (sources level) from Measurable.of_discrete).aemeasurable).toMeasure
      ((xiLimitProbabilityMeasure system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass).map targetContinuous.measurable.aemeasurable).toMeasure)
      atTop (𝓝 0) := by
  have projectionLaw (level : ℕ) :
      (finiteLaws level).map
        (show Measurable (xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair level) from Measurable.of_discrete).aemeasurable =
        imageLaws level := by
    apply ProbabilityMeasure.toMeasure_injective
    exact images level
  have projectionConvergence : Tendsto (fun level => (finiteLaws level).map
      (show Measurable (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level) from Measurable.of_discrete).aemeasurable)
      atTop (𝓝 (xiLimitProbabilityMeasure system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass)) := by
    simpa only [projectionLaw] using nativeWeak
  have weak := commonRealisation_probability_images_tendsto finiteLaws
    (xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair)
    (fun _ => Measurable.of_discrete) target targetContinuous sources
    (fun _ => Measurable.of_discrete) radii radiiNonnegative radiiZero displacement
    (xiLimitProbabilityMeasure system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass) projectionConvergence
  exact ⟨weak, levyProkhorovDist_tendsto_zero_of_weak _ _ weak⟩

 theorem xiOriginalCommon_vertex_images_converge
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (mass : XiMassParameters system) :
    Tendsto (fun level => ((xiNativeVertexProbability system) level).map
      (show Measurable (sources level) from Measurable.of_discrete).aemeasurable) atTop
      (𝓝 ((xiLimitProbabilityMeasure system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass).map targetContinuous.measurable.aemeasurable)) ∧
    Tendsto (fun level => levyProkhorovDist
      (((xiNativeVertexProbability system) level).map
        (show Measurable (sources level) from Measurable.of_discrete).aemeasurable).toMeasure
      ((xiLimitProbabilityMeasure system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass).map targetContinuous.measurable.aemeasurable).toMeasure)
      atTop (𝓝 0) := by
  apply xiOriginalCommon_images_converge_of_native_weak system connected lengths lengthsPositive
    rate rateGreaterThanOne eigenpair target targetContinuous sources radii radiiNonnegative
    radiiZero displacement mass (xiNativeVertexProbability system) (xiVertexProbabilityMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair) (fun _ => rfl)
  exact xiVertexProbabilityMeasure_tendsto system connected plantingNonadjacent distancePositive
    lengths lengthsPositive rate rateGreaterThanOne eigenpair mass

 theorem xiOriginalCommon_speed_images_converge (mass : XiMassParameters system) :
    Tendsto (fun level => ((xiNativeSpeedProbability system mass) level).map
      (show Measurable (sources level) from Measurable.of_discrete).aemeasurable) atTop
      (𝓝 ((xiLimitProbabilityMeasure system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass).map targetContinuous.measurable.aemeasurable)) ∧
    Tendsto (fun level => levyProkhorovDist
      (((xiNativeSpeedProbability system mass) level).map
        (show Measurable (sources level) from Measurable.of_discrete).aemeasurable).toMeasure
      ((xiLimitProbabilityMeasure system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass).map targetContinuous.measurable.aemeasurable).toMeasure)
      atTop (𝓝 0) := by
  apply xiOriginalCommon_images_converge_of_native_weak system connected lengths lengthsPositive
    rate rateGreaterThanOne eigenpair target targetContinuous sources radii radiiNonnegative
    radiiZero displacement mass (xiNativeSpeedProbability system mass) (xiSpeedProbabilityMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass) (xiVertexSpeedMeasure_map system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)
  exact xiSpeedProbabilityMeasure_tendsto system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair mass

end
end EIGS.MeasuredGHP

#print axioms EIGS.MeasuredGHP.xiOriginalCommon_images_converge_of_native_weak
#print axioms EIGS.MeasuredGHP.xiOriginalCommon_vertex_images_converge
#print axioms EIGS.MeasuredGHP.xiOriginalCommon_speed_images_converge
