import RequestProject.Section31.FiniteSupportUniformPathSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Restriction between the uniform closures of finite path supports.
Compatibility is checked on the actual finite histories. It extends to the
closed path carriers by continuity, and hence transports weak limits. -/

namespace IGS.Sec31.DiscreteMarkov

open Set MeasureTheory Filter Topology
open scoped UniformConvergence

variable {LongTime ShortTime State : Type*} [MetricSpace State] [CompactSpace State]
variable {LongHistory ShortHistory : ℕ → Type*}
variable [∀ level, Finite (LongHistory level)] [∀ level, Finite (ShortHistory level)]

variable (longPaths : (level : ℕ) → LongHistory level → LongTime → State)
variable (shortPaths : (level : ℕ) → ShortHistory level → ShortTime → State)
variable (timeEmbedding : ShortTime → LongTime)
variable (restrictHistory : (level : ℕ) → LongHistory level → ShortHistory level)
variable (compatible : ∀ level history time,
  longPaths level history (timeEmbedding time) = shortPaths level (restrictHistory level history) time)

include restrictHistory compatible

theorem finitePathSupport_restriction_mapsTo :
    MapsTo (fun path : LongTime →ᵤ State =>
      UniformFun.ofFun (UniformFun.toFun path ∘ timeEmbedding))
      (finitePathSupport longPaths) (finitePathSupport shortPaths) := by
  intro path pathMem
  obtain ⟨level, history, rfl⟩ := Set.mem_iUnion.mp pathMem
  refine Set.mem_iUnion.mpr ⟨level, Set.mem_range.mpr ⟨restrictHistory level history, ?_⟩⟩
  congr 1
  funext time
  exact (compatible level history time).symm

def finiteSupportPathRestriction (path : FiniteSupportPathSpace longPaths) :
    FiniteSupportPathSpace shortPaths :=
  ⟨UniformFun.ofFun (UniformFun.toFun path.val ∘ timeEmbedding),
    (finitePathSupport_restriction_mapsTo longPaths shortPaths timeEmbedding restrictHistory compatible).closure
      UniformFun.precomp_uniformContinuous.continuous path.property⟩

theorem finiteSupportPathRestriction_apply
    (path : FiniteSupportPathSpace longPaths) (time : ShortTime) :
    UniformFun.toFun
      (finiteSupportPathRestriction longPaths shortPaths timeEmbedding restrictHistory compatible path).val time =
      UniformFun.toFun path.val (timeEmbedding time) := rfl

theorem finiteSupportPathRestriction_continuous :
    Continuous (finiteSupportPathRestriction longPaths shortPaths timeEmbedding restrictHistory compatible) :=
  (UniformFun.precomp_uniformContinuous.continuous.comp continuous_subtype_val).subtype_mk _

theorem finiteSupportPathRestriction_finitePathEmbedding (level : ℕ) (history : LongHistory level) :
    finiteSupportPathRestriction longPaths shortPaths timeEmbedding restrictHistory compatible
      (finitePathEmbedding longPaths level history) =
      finitePathEmbedding shortPaths level (restrictHistory level history) := by
  apply Subtype.ext
  change UniformFun.ofFun (longPaths level history ∘ timeEmbedding) =
    UniformFun.ofFun (shortPaths level (restrictHistory level history))
  congr 1
  funext time
  exact compatible level history time

theorem finiteSupportPathRestriction_weak_limit
    (longLaws : ℕ → ProbabilityMeasure (FiniteSupportPathSpace longPaths))
    (shortLaws : ℕ → ProbabilityMeasure (FiniteSupportPathSpace shortPaths))
    (longLimit : ProbabilityMeasure (FiniteSupportPathSpace longPaths))
    (shortLimit : ProbabilityMeasure (FiniteSupportPathSpace shortPaths))
    (longConvergence : Tendsto longLaws atTop (𝓝 longLimit))
    (shortConvergence : Tendsto shortLaws atTop (𝓝 shortLimit))
    (compatibleLaws : ∀ level, (longLaws level).map
      (finiteSupportPathRestriction_continuous longPaths shortPaths timeEmbedding
        restrictHistory compatible).measurable.aemeasurable = shortLaws level) :
    longLimit.map (finiteSupportPathRestriction_continuous longPaths shortPaths timeEmbedding
      restrictHistory compatible).measurable.aemeasurable = shortLimit := by
  have mappedConvergence := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    longLaws longLimit longConvergence
    (finiteSupportPathRestriction_continuous longPaths shortPaths timeEmbedding restrictHistory compatible)
  simp only [compatibleLaws] at mappedConvergence
  exact tendsto_nhds_unique mappedConvergence shortConvergence

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finitePathSupport_restriction_mapsTo
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPathRestriction_continuous
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPathRestriction_finitePathEmbedding
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPathRestriction_weak_limit
