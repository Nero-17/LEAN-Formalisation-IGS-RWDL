import RequestProject.Section31.FiniteSupportCadlagJ1Transport
import RequestProject.Section31.CadlagJ1SpatialTransport
import RequestProject.Section31.ProbabilityUniformCouplingTransport

/-! The actual finite-prefix law and its unchanged floor clock can be placed
in a common ambient by the original finite-space embeddings. Uniform
displacement from the projected embeddings transfers the proved weak limit.
The two samplers use exactly the same prefix and rates; no equality between
independently specified clocks is an assumption. -/

namespace IGS.Sec31.DiscreteMarkov
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped UniformConvergence NNReal

variable {State Ambient : Type*} [MetricSpace State] [CompactSpace State]
  [MeasurableSpace State] [BorelSpace State]
  [MetricSpace Ambient] [CompactSpace Ambient] [MeasurableSpace Ambient] [BorelSpace Ambient]
  {Vertex : ℕ → Type*} [∀ n, Fintype (Vertex n)] [∀ n, MeasurableSpace (Vertex n)]
  [∀ n, MeasurableSingletonClass (Vertex n)]

local instance commonFloorSourceBoundedSpace : BoundedSpace State := ⟨Metric.isBounded_of_compactSpace⟩
local instance commonFloorAmbientBoundedSpace : BoundedSpace Ambient := ⟨Metric.isBounded_of_compactSpace⟩
local instance commonFloorIntervalBoundedSpace (horizon : ℝ≥0) :
    BoundedSpace (Icc (0 : ℝ) (horizon : ℝ)) := ⟨Metric.isBounded_of_compactSpace⟩
local instance commonFloorSourceJ1MeasurableSpace (horizon : ℝ≥0) :
    MeasurableSpace (CadlagJ1Path (Icc (0 : ℝ) (horizon : ℝ)) State) := borel _
local instance commonFloorSourceJ1BorelSpace (horizon : ℝ≥0) :
    BorelSpace (CadlagJ1Path (Icc (0 : ℝ) (horizon : ℝ)) State) := ⟨rfl⟩
local instance commonFloorAmbientJ1MeasurableSpace (horizon : ℝ≥0) :
    MeasurableSpace (CadlagJ1Path (Icc (0 : ℝ) (horizon : ℝ)) Ambient) := borel _
local instance commonFloorAmbientJ1BorelSpace (horizon : ℝ≥0) :
    BorelSpace (CadlagJ1Path (Icc (0 : ℝ) (horizon : ℝ)) Ambient) := ⟨rfl⟩

def finiteHorizonHistoryCadlagJ1Map (horizon : ℝ≥0) (rates : ℕ → ℝ≥0)
    (embedding : ∀ n, Vertex n → State) (n : ℕ)
    (history : Finset.Iic ⌊(horizon : ℝ) * (rates n : ℝ)⌋₊ → Vertex n) :
    CadlagJ1Path (Icc (0 : ℝ) (horizon : ℝ)) State :=
  ⟨⟨finiteHorizonStepPaths horizon rates embedding n history⟩,
    finiteHorizonStepPaths_isCadlag horizon rates embedding n history⟩

theorem finiteHorizonHistoryCadlagJ1Map_measurable (horizon : ℝ≥0) (rates : ℕ → ℝ≥0)
    (embedding : ∀ n, Vertex n → State) (n : ℕ) :
    Measurable (finiteHorizonHistoryCadlagJ1Map horizon rates embedding n) := measurable_of_finite _

theorem finiteHorizonStepLaw_cadlag_eq_prefix_map (horizon : ℝ≥0) (rates : ℕ → ℝ≥0)
    (embedding : ∀ n, Vertex n → State)
    (kernels : ∀ n, Kernel (Vertex n) (Vertex n)) [∀ n, IsMarkovKernel (kernels n)]
    (initial : ∀ n, ProbabilityMeasure (Vertex n)) (n : ℕ) :
    (finiteHorizonStepLaw horizon rates embedding kernels initial n).map
        (finiteHorizonPathToCadlagJ1_continuous horizon rates embedding).measurable.aemeasurable =
      ProbabilityMeasure.map (⟨finiteHorizonPrefixLaw horizon rates kernels initial n, inferInstance⟩ :
        ProbabilityMeasure (Finset.Iic ⌊(horizon : ℝ) * (rates n : ℝ)⌋₊ → Vertex n))
          (finiteHorizonHistoryCadlagJ1Map_measurable horizon rates embedding n).aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  change ((finiteHorizonPrefixLaw horizon rates kernels initial n).map
    (finitePathEmbedding (finiteHorizonStepPaths horizon rates embedding) n)).map
      (finiteHorizonPathToCadlagJ1 horizon rates embedding) = _
  rw [Measure.map_map (finiteHorizonPathToCadlagJ1_continuous horizon rates embedding).measurable
    (measurable_of_countable (finitePathEmbedding (finiteHorizonStepPaths horizon rates embedding) n))]
  rfl

theorem finiteHorizon_common_ambient_weak_convergence
    (horizon : ℝ≥0) (rates : ℕ → ℝ≥0)
    (projection : ∀ n, Vertex n → State) (sources : ∀ n, Vertex n → Ambient)
    (target : State → Ambient) (targetContinuous : Continuous target)
    (kernels : ∀ n, Kernel (Vertex n) (Vertex n)) [∀ n, IsMarkovKernel (kernels n)]
    (initial : ∀ n, ProbabilityMeasure (Vertex n))
    (radii : ℕ → ℝ) (radiiNonnegative : ∀ n, 0 ≤ radii n) (radiiZero : Tendsto radii atTop (𝓝 0))
    (projectionClose : ∀ n vertex, dist (sources n vertex) (target (projection n vertex)) ≤ radii n)
    (limit : ProbabilityMeasure (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates projection)))
    (nativeConvergence : Tendsto (finiteHorizonStepLaw horizon rates projection kernels initial) atTop (𝓝 limit)) :
    Tendsto (fun n =>
      ProbabilityMeasure.map (⟨finiteHorizonPrefixLaw horizon rates kernels initial n, inferInstance⟩ :
        ProbabilityMeasure (Finset.Iic ⌊(horizon : ℝ) * (rates n : ℝ)⌋₊ → Vertex n))
          (finiteHorizonHistoryCadlagJ1Map_measurable horizon rates sources n).aemeasurable) atTop
      (𝓝 (cadlagJ1SpatialLaw target targetContinuous (limit.map
        (finiteHorizonPathToCadlagJ1_continuous horizon rates projection).measurable.aemeasurable))) := by
  let samples := fun n => (⟨finiteHorizonPrefixLaw horizon rates kernels initial n, inferInstance⟩ :
    ProbabilityMeasure (Finset.Iic ⌊(horizon : ℝ) * (rates n : ℝ)⌋₊ → Vertex n))
  let projected := fun n => cadlagJ1SpatialMap target targetContinuous ∘
    finiteHorizonHistoryCadlagJ1Map horizon rates projection n
  have projectedMeasurable (n : ℕ) : Measurable (projected n) :=
    (cadlagJ1SpatialMap_continuous target targetContinuous).measurable.comp
      (finiteHorizonHistoryCadlagJ1Map_measurable horizon rates projection n)
  have nativeJ1Convergence := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (finiteHorizonStepLaw horizon rates projection kernels initial) limit nativeConvergence
    (finiteHorizonPathToCadlagJ1_continuous horizon rates projection)
  have spatialConvergence := cadlagJ1SpatialLaw_weak_convergence target targetContinuous
    (fun n => (finiteHorizonStepLaw horizon rates projection kernels initial n).map
      (finiteHorizonPathToCadlagJ1_continuous horizon rates projection).measurable.aemeasurable)
    (limit.map (finiteHorizonPathToCadlagJ1_continuous horizon rates projection).measurable.aemeasurable)
    nativeJ1Convergence
  have projectedLawEquality (n : ℕ) :
      (samples n).map (projectedMeasurable n).aemeasurable = cadlagJ1SpatialLaw target targetContinuous
        ((finiteHorizonStepLaw horizon rates projection kernels initial n).map
          (finiteHorizonPathToCadlagJ1_continuous horizon rates projection).measurable.aemeasurable) := by
    rw [finiteHorizonStepLaw_cadlag_eq_prefix_map]
    apply ProbabilityMeasure.toMeasure_injective
    simp only [cadlagJ1SpatialLaw, ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map (cadlagJ1SpatialMap_continuous target targetContinuous).measurable
      (finiteHorizonHistoryCadlagJ1Map_measurable horizon rates projection n)]
    rfl
  have projectedConvergence : Tendsto (fun n => (samples n).map (projectedMeasurable n).aemeasurable) atTop
      (𝓝 (cadlagJ1SpatialLaw target targetContinuous (limit.map
        (finiteHorizonPathToCadlagJ1_continuous horizon rates projection).measurable.aemeasurable))) := by
    simpa only [projectedLawEquality] using spatialConvergence
  apply probability_maps_same_limit_of_uniform_displacement samples
    (finiteHorizonHistoryCadlagJ1Map horizon rates sources) projected
    (finiteHorizonHistoryCadlagJ1Map_measurable horizon rates sources) projectedMeasurable
    radii radiiNonnegative radiiZero ?_ _ projectedConvergence
  intro n history
  apply cadlagJ1_dist_le_of_pointwise _ _ (radii n) (radiiNonnegative n)
  intro time
  exact projectionClose n (history ⟨⌊time.val * (rates n : ℝ)⌋₊,
    Finset.mem_Iic.mpr (Nat.floor_mono
      (mul_le_mul_of_nonneg_right time.property.2 (rates n).property))⟩)

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizonStepLaw_cadlag_eq_prefix_map
#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizon_common_ambient_weak_convergence
