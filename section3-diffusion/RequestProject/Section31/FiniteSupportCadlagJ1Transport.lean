import RequestProject.Section31.FiniteFloorPathCadlag
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Continuous transport of the actual uniform support carrier to a genuine
cadlag subtype with the explicit J1 time-change pseudometric. Weak convergence
is transported by continuous probability pushforward. No J1 separation or
Polish-space theorem is used or asserted. -/

namespace IGS.Sec31.DiscreteMarkov

open Set Filter Topology MeasureTheory
open scoped UniformConvergence NNReal
noncomputable section

variable {Time State : Type*} [LinearOrder Time] [MetricSpace Time] [BoundedSpace Time]
variable [MetricSpace State] [CompactSpace State]
variable {History : ℕ → Type*} [∀ level, Finite (History level)]

local instance supportCadlagStateBoundedSpace : BoundedSpace State :=
  ⟨Metric.isBounded_of_compactSpace⟩

theorem finiteSupportPathSpace_isCadlag
    (paths : (level : ℕ) → History level → Time → State)
    (supportsCadlag : ∀ level history, IsCadlagPath (paths level history))
    (path : FiniteSupportPathSpace paths) : IsCadlagPath (UniformFun.toFun path.val) := by
  have supportIncluded : finitePathSupport paths ⊆
      {path : Time →ᵤ State | IsCadlagPath (UniformFun.toFun path)} := by
    intro support membership
    obtain ⟨level, history, rfl⟩ := Set.mem_iUnion.mp membership
    exact supportsCadlag level history
  exact closure_minimal supportIncluded isClosed_uniformCadlagPaths path.property

def finiteSupportPathSpaceToCadlagJ1
    (paths : (level : ℕ) → History level → Time → State)
    (supportsCadlag : ∀ level history, IsCadlagPath (paths level history))
    (path : FiniteSupportPathSpace paths) : CadlagJ1Path Time State :=
  ⟨uniformFunctionToJ1 path.val, finiteSupportPathSpace_isCadlag paths supportsCadlag path⟩

theorem finiteSupportPathSpaceToCadlagJ1_continuous
    (paths : (level : ℕ) → History level → Time → State)
    (supportsCadlag : ∀ level history, IsCadlagPath (paths level history)) :
    Continuous (finiteSupportPathSpaceToCadlagJ1 paths supportsCadlag) :=
  (uniformFunctionToJ1_continuous.comp continuous_subtype_val).subtype_mk
    (fun path => finiteSupportPathSpace_isCadlag paths supportsCadlag path)

local instance supportCadlagJ1MeasurableSpace : MeasurableSpace (CadlagJ1Path Time State) := borel _
local instance supportCadlagJ1BorelSpace : BorelSpace (CadlagJ1Path Time State) := ⟨rfl⟩

theorem finiteSupportPathSpaceToCadlagJ1_weak_convergence
    (paths : (level : ℕ) → History level → Time → State)
    (supportsCadlag : ∀ level history, IsCadlagPath (paths level history))
    (laws : ℕ → ProbabilityMeasure (FiniteSupportPathSpace paths))
    (limit : ProbabilityMeasure (FiniteSupportPathSpace paths))
    (lawsConverge : Tendsto laws atTop (𝓝 limit)) :
    Tendsto (fun index => (laws index).map
      (finiteSupportPathSpaceToCadlagJ1_continuous paths supportsCadlag).measurable.aemeasurable)
      atTop (𝓝 (limit.map
        (finiteSupportPathSpaceToCadlagJ1_continuous paths supportsCadlag).measurable.aemeasurable)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous laws limit lawsConverge
    (finiteSupportPathSpaceToCadlagJ1_continuous paths supportsCadlag)

section ActualFiniteFloorPaths
variable [MeasurableSpace State] [BorelSpace State]
variable {Vertex : ℕ → Type*} [∀ level, Fintype (Vertex level)]
variable [∀ level, MeasurableSpace (Vertex level)]
variable [∀ level, MeasurableSingletonClass (Vertex level)]

local instance floorCadlagIntervalBoundedSpace (horizon : ℝ≥0) :
    BoundedSpace (Icc (0 : ℝ) (horizon : ℝ)) := ⟨Metric.isBounded_of_compactSpace⟩

def finiteHorizonPathToCadlagJ1 (horizon : ℝ≥0) (rates : ℕ → ℝ≥0)
    (embedding : (level : ℕ) → Vertex level → State) :
    FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding) →
      CadlagJ1Path (Icc (0 : ℝ) (horizon : ℝ)) State :=
  finiteSupportPathSpaceToCadlagJ1 (finiteHorizonStepPaths horizon rates embedding)
    (finiteHorizonStepPaths_isCadlag horizon rates embedding)

theorem finiteHorizonPathToCadlagJ1_continuous (horizon : ℝ≥0) (rates : ℕ → ℝ≥0)
    (embedding : (level : ℕ) → Vertex level → State) :
    Continuous (finiteHorizonPathToCadlagJ1 horizon rates embedding) :=
  finiteSupportPathSpaceToCadlagJ1_continuous (finiteHorizonStepPaths horizon rates embedding)
    (finiteHorizonStepPaths_isCadlag horizon rates embedding)

theorem finiteHorizonPathToCadlagJ1_apply (horizon : ℝ≥0) (rates : ℕ → ℝ≥0)
    (embedding : (level : ℕ) → Vertex level → State)
    (path : FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding))
    (time : Icc (0 : ℝ) (horizon : ℝ)) :
    (finiteHorizonPathToCadlagJ1 horizon rates embedding path).val.toFun time =
      UniformFun.toFun path.val time := rfl

end ActualFiniteFloorPaths
end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPathSpace_isCadlag
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPathSpaceToCadlagJ1_weak_convergence
#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizonPathToCadlagJ1_continuous
