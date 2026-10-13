import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Metrizable.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Data.Set.Finite.Range

/-! The uniform closure of the actual finite path supports is a complete
separable metric space. No continuity of the individual paths is required.
The time type can in particular be a fixed compact interval. This does not
assert that the full uniform function space is separable or that the path
laws are tight. -/

namespace IGS.Sec31.DiscreteMarkov

open Set TopologicalSpace
open scoped UniformConvergence

variable {Time State : Type*} [MetricSpace State] [CompactSpace State]
variable {History : ℕ → Type*} [∀ level, Finite (History level)]

local instance compactStateBoundedSpace : BoundedSpace State :=
  ⟨Metric.isBounded_of_compactSpace⟩

variable (paths : (level : ℕ) → History level → Time → State)

def finitePathSupport : Set (Time →ᵤ State) :=
  ⋃ level, Set.range (fun history => UniformFun.ofFun (paths level history))

theorem finitePathSupport_countable : (finitePathSupport paths).Countable := by
  exact Set.countable_iUnion fun level =>
    (Set.finite_range (fun history => UniformFun.ofFun (paths level history))).countable

def FiniteSupportPathSpace : Type _ :=
  ↥(closure (finitePathSupport paths))

noncomputable instance finiteSupportPathSpaceMetricSpace :
    MetricSpace (FiniteSupportPathSpace paths) :=
  inferInstanceAs (MetricSpace ↥(closure (finitePathSupport paths)))

instance finiteSupportPathSpaceCompleteSpace :
    CompleteSpace (FiniteSupportPathSpace paths) :=
  isClosed_closure.completeSpace_coe

instance finiteSupportPathSpaceSeparableSpace :
    SeparableSpace (FiniteSupportPathSpace paths) :=
  ((finitePathSupport_countable paths).isSeparable.closure).separableSpace

instance finiteSupportPathSpaceSecondCountableTopology :
    SecondCountableTopology (FiniteSupportPathSpace paths) :=
  inferInstance

instance finiteSupportPathSpacePolishSpace :
    PolishSpace (FiniteSupportPathSpace paths) :=
  inferInstance

instance finiteSupportPathSpaceMeasurableSpace :
    MeasurableSpace (FiniteSupportPathSpace paths) :=
  borel (FiniteSupportPathSpace paths)

instance finiteSupportPathSpaceBorelSpace :
    BorelSpace (FiniteSupportPathSpace paths) :=
  ⟨rfl⟩

def finitePathEmbedding (level : ℕ) (history : History level) :
    FiniteSupportPathSpace paths :=
  ⟨UniformFun.ofFun (paths level history),
    subset_closure (Set.mem_iUnion.mpr ⟨level, Set.mem_range_self history⟩)⟩

theorem finitePathEmbedding_range_finite (level : ℕ) :
    (Set.range (finitePathEmbedding paths level)).Finite :=
  Set.finite_range _

theorem finitePathEmbedding_apply (level : ℕ) (history : History level) (time : Time) :
    UniformFun.toFun (finitePathEmbedding paths level history).val time =
      paths level history time :=
  rfl

theorem finiteSupportPathSpace_dist (first second : FiniteSupportPathSpace paths) :
    dist first second =
      ⨆ time, dist (UniformFun.toFun first.val time) (UniformFun.toFun second.val time) :=
  UniformFun.dist_def first.val second.val

theorem finiteSupportPathSpace_continuous_eval (time : Time) :
    Continuous (fun path : FiniteSupportPathSpace paths => UniformFun.toFun path.val time) :=
  (UniformFun.uniformContinuous_eval State time).continuous.comp continuous_subtype_val

theorem finiteSupportPathSpace_complete_separable :
    CompleteSpace (FiniteSupportPathSpace paths) ∧
      SeparableSpace (FiniteSupportPathSpace paths) :=
  ⟨inferInstance, inferInstance⟩

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finitePathSupport_countable
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPathSpace_complete_separable
#print axioms IGS.Sec31.DiscreteMarkov.finitePathEmbedding_range_finite
#print axioms IGS.Sec31.DiscreteMarkov.finitePathEmbedding_apply
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPathSpace_dist
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPathSpace_continuous_eval
