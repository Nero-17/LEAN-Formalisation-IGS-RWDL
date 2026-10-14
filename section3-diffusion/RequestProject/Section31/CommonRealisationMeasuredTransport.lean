import RequestProject.Section31.ProbabilityUniformCouplingTransport
import RequestProject.Section31.EIGSMeasuredGHP

/-! Measure and set convergence in one already constructed common ambient.
The projection laws and the uniform displacement are the mathematical inputs;
neither weak convergence of the source images nor common-space GHP convergence
is assumed. This leaf does not assert completeness or Polishness of a path space. -/

namespace IGS.Sec31
noncomputable section
open MeasureTheory Filter Topology Metric Set

 theorem commonRealisation_probability_images_tendsto
    {State Ambient : Type*}
    [MetricSpace State] [MeasurableSpace State] [BorelSpace State]
    [MetricSpace Ambient] [MeasurableSpace Ambient] [BorelSpace Ambient]
    {Vertex : ℕ → Type*} [∀ level, MeasurableSpace (Vertex level)]
    (laws : ∀ level, ProbabilityMeasure (Vertex level))
    (projection : ∀ level, Vertex level → State)
    (projectionMeasurable : ∀ level, Measurable (projection level))
    (target : State → Ambient) (targetContinuous : Continuous target)
    (sources : ∀ level, Vertex level → Ambient)
    (sourcesMeasurable : ∀ level, Measurable (sources level))
    (radii : ℕ → ℝ) (radiiNonnegative : ∀ level, 0 ≤ radii level)
    (radiiZero : Tendsto radii atTop (𝓝 0))
    (displacement : ∀ level vertex,
      dist (sources level vertex) (target (projection level vertex)) ≤ radii level)
    (limit : ProbabilityMeasure State)
    (projectionConvergence : Tendsto
      (fun level => (laws level).map (projectionMeasurable level).aemeasurable)
      atTop (𝓝 limit)) :
    Tendsto (fun level => (laws level).map (sourcesMeasurable level).aemeasurable)
      atTop (𝓝 (limit.map targetContinuous.measurable.aemeasurable)) := by
  have composedMeasurable (level : ℕ) : Measurable (target ∘ projection level) :=
    targetContinuous.measurable.comp (projectionMeasurable level)
  have composedLaw (level : ℕ) :
      (laws level).map (composedMeasurable level).aemeasurable =
        ((laws level).map (projectionMeasurable level).aemeasurable).map
          targetContinuous.measurable.aemeasurable := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map targetContinuous.measurable (projectionMeasurable level)]
  have composedConvergence : Tendsto
      (fun level => (laws level).map (composedMeasurable level).aemeasurable) atTop
      (𝓝 (limit.map targetContinuous.measurable.aemeasurable)) := by
    simpa only [composedLaw] using
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
        projectionConvergence targetContinuous
  exact probability_maps_same_limit_of_uniform_displacement laws sources
    (fun level => target ∘ projection level) sourcesMeasurable composedMeasurable
    radii radiiNonnegative radiiZero displacement _ composedConvergence

 theorem commonRealisation_levyProkhorov_images_tendsto_zero
    {State Ambient : Type*}
    [MetricSpace State] [MeasurableSpace State] [BorelSpace State]
    [MetricSpace Ambient] [TopologicalSpace.SeparableSpace Ambient]
    [MeasurableSpace Ambient] [BorelSpace Ambient]
    {Vertex : ℕ → Type*} [∀ level, MeasurableSpace (Vertex level)]
    (laws : ∀ level, ProbabilityMeasure (Vertex level))
    (projection : ∀ level, Vertex level → State)
    (projectionMeasurable : ∀ level, Measurable (projection level))
    (target : State → Ambient) (targetContinuous : Continuous target)
    (sources : ∀ level, Vertex level → Ambient)
    (sourcesMeasurable : ∀ level, Measurable (sources level))
    (radii : ℕ → ℝ) (radiiNonnegative : ∀ level, 0 ≤ radii level)
    (radiiZero : Tendsto radii atTop (𝓝 0))
    (displacement : ∀ level vertex,
      dist (sources level vertex) (target (projection level vertex)) ≤ radii level)
    (limit : ProbabilityMeasure State)
    (projectionConvergence : Tendsto
      (fun level => (laws level).map (projectionMeasurable level).aemeasurable)
      atTop (𝓝 limit)) :
    Tendsto (fun level => levyProkhorovDist
      ((laws level).map (sourcesMeasurable level).aemeasurable).toMeasure
      (limit.map targetContinuous.measurable.aemeasurable).toMeasure) atTop (𝓝 0) := by
  exact EIGS.MeasuredGHP.levyProkhorovDist_tendsto_zero_of_weak _ _
    (commonRealisation_probability_images_tendsto laws projection projectionMeasurable
      target targetContinuous sources sourcesMeasurable radii radiiNonnegative
      radiiZero displacement limit projectionConvergence)

 theorem commonRealisation_hausdorffDist_le
    {State Ambient Vertex : Type*} [PseudoMetricSpace State] [PseudoMetricSpace Ambient]
    (projection : Vertex → State) (target : State → Ambient) (targetIsometry : Isometry target)
    (source : Vertex → Ambient) (radius mesh : ℝ)
    (radiusNonnegative : 0 ≤ radius) (meshNonnegative : 0 ≤ mesh)
    (displacement : ∀ vertex, dist (source vertex) (target (projection vertex)) ≤ radius)
    (denseProjection : ∀ point : State, ∃ vertex, dist point (projection vertex) ≤ mesh) :
    hausdorffDist (range source) (range target) ≤ radius + mesh := by
  apply hausdorffDist_le_of_mem_dist (add_nonneg radiusNonnegative meshNonnegative)
  · rintro _ ⟨vertex, rfl⟩
    exact ⟨target (projection vertex), mem_range_self _,
      (displacement vertex).trans (le_add_of_nonneg_right meshNonnegative)⟩
  · rintro _ ⟨point, rfl⟩
    obtain ⟨vertex, near⟩ := denseProjection point
    refine ⟨source vertex, mem_range_self _, ?_⟩
    calc
      dist (target point) (source vertex) ≤
          dist (target point) (target (projection vertex)) +
            dist (target (projection vertex)) (source vertex) := dist_triangle _ _ _
      _ ≤ mesh + radius := add_le_add (by simpa only [targetIsometry.dist_eq] using near)
        (by simpa only [dist_comm] using displacement vertex)
      _ = radius + mesh := add_comm _ _

 theorem commonRealisation_hausdorffDist_tendsto_zero
    {State Ambient : Type*} [PseudoMetricSpace State] [PseudoMetricSpace Ambient]
    {Vertex : ℕ → Type*}
    (projection : ∀ level, Vertex level → State)
    (target : State → Ambient) (targetIsometry : Isometry target)
    (sources : ∀ level, Vertex level → Ambient)
    (radii mesh : ℕ → ℝ)
    (radiiNonnegative : ∀ level, 0 ≤ radii level)
    (meshNonnegative : ∀ level, 0 ≤ mesh level)
    (radiiZero : Tendsto radii atTop (𝓝 0)) (meshZero : Tendsto mesh atTop (𝓝 0))
    (displacement : ∀ level vertex,
      dist (sources level vertex) (target (projection level vertex)) ≤ radii level)
    (denseProjection : ∀ level point, ∃ vertex, dist point (projection level vertex) ≤ mesh level) :
    Tendsto (fun level => hausdorffDist (range (sources level)) (range target)) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => hausdorffDist_nonneg)
    (fun level => commonRealisation_hausdorffDist_le (projection level) target targetIsometry
      (sources level) (radii level) (mesh level) (radiiNonnegative level)
      (meshNonnegative level) (displacement level) (denseProjection level))
  simpa only [zero_add] using radiiZero.add meshZero

end
end IGS.Sec31

#print axioms IGS.Sec31.commonRealisation_probability_images_tendsto
#print axioms IGS.Sec31.commonRealisation_levyProkhorov_images_tendsto_zero
#print axioms IGS.Sec31.commonRealisation_hausdorffDist_le
#print axioms IGS.Sec31.commonRealisation_hausdorffDist_tendsto_zero
