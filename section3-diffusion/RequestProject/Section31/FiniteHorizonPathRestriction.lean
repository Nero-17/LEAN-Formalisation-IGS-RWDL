import RequestProject.Section31.FiniteSupportPathRestriction
import RequestProject.Section31.FiniteHorizonMarkovStepPathLaw

/-! The actual floor-clock laws are compatible under restriction of the
time horizon. Weak limits therefore inherit this compatibility. -/

namespace IGS.Sec31.DiscreteMarkov

open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped UniformConvergence NNReal

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable {Vertex : ℕ → Type*} [∀ level, Fintype (Vertex level)]
variable [∀ level, MeasurableSpace (Vertex level)]
variable [∀ level, MeasurableSingletonClass (Vertex level)]

variable (shortHorizon longHorizon : ℝ≥0) (horizonsOrdered : shortHorizon ≤ longHorizon)
variable (rates : ℕ → ℝ≥0) (embedding : (level : ℕ) → Vertex level → State)

def finiteHorizonTimeInclusion (time : Set.Icc (0 : ℝ) (shortHorizon : ℝ)) :
    Set.Icc (0 : ℝ) (longHorizon : ℝ) :=
  ⟨time.val, time.property.1, time.property.2.trans (by exact_mod_cast horizonsOrdered)⟩

def finiteHorizonHistoryRestriction (level : ℕ)
    (history : Finset.Iic ⌊(longHorizon : ℝ) * (rates level : ℝ)⌋₊ → Vertex level)
    (index : Finset.Iic ⌊(shortHorizon : ℝ) * (rates level : ℝ)⌋₊) : Vertex level :=
  history ⟨index.val, Finset.mem_Iic.mpr ((Finset.mem_Iic.mp index.property).trans
    (Nat.floor_mono (mul_le_mul_of_nonneg_right (by exact_mod_cast horizonsOrdered)
      (rates level).property)))⟩

noncomputable def finiteHorizonPathRestriction :
    FiniteSupportPathSpace (finiteHorizonStepPaths longHorizon rates embedding) →
      FiniteSupportPathSpace (finiteHorizonStepPaths shortHorizon rates embedding) :=
  finiteSupportPathRestriction
    (finiteHorizonStepPaths longHorizon rates embedding)
    (finiteHorizonStepPaths shortHorizon rates embedding)
    (finiteHorizonTimeInclusion shortHorizon longHorizon horizonsOrdered)
    (finiteHorizonHistoryRestriction shortHorizon longHorizon horizonsOrdered rates)
    (by intro level history time; rfl)

theorem finiteHorizonPathRestriction_continuous :
    Continuous (finiteHorizonPathRestriction shortHorizon longHorizon horizonsOrdered rates embedding) :=
  finiteSupportPathRestriction_continuous _ _ _ _ _

theorem finiteHorizonPathRestriction_stepMap (level : ℕ) (path : ℕ → Vertex level) :
    finiteHorizonPathRestriction shortHorizon longHorizon horizonsOrdered rates embedding
      (finiteHorizonStepMap longHorizon rates embedding level path) =
      finiteHorizonStepMap shortHorizon rates embedding level path := by
  apply Subtype.ext
  rfl

variable (kernels : (level : ℕ) → Kernel (Vertex level) (Vertex level))
variable [∀ level, IsMarkovKernel (kernels level)]
variable (initial : (level : ℕ) → ProbabilityMeasure (Vertex level))

theorem finiteHorizonPathRestriction_stepLaw (level : ℕ) :
    (finiteHorizonStepLaw longHorizon rates embedding kernels initial level).map
      (finiteHorizonPathRestriction_continuous shortHorizon longHorizon horizonsOrdered rates embedding).measurable.aemeasurable =
      finiteHorizonStepLaw shortHorizon rates embedding kernels initial level := by
  apply ProbabilityMeasure.toMeasure_injective
  change (finiteHorizonStepLaw longHorizon rates embedding kernels initial level :
    Measure (FiniteSupportPathSpace (finiteHorizonStepPaths longHorizon rates embedding))).map
    (finiteHorizonPathRestriction shortHorizon longHorizon horizonsOrdered rates embedding) = _
  rw [finiteHorizonStepLaw_eq_map, finiteHorizonStepLaw_eq_map]
  rw [Measure.map_map
    (finiteHorizonPathRestriction_continuous shortHorizon longHorizon horizonsOrdered rates embedding).measurable
    (finiteHorizonStepMap_measurable longHorizon rates embedding level)]
  congr 1

theorem finiteHorizonPathRestriction_weakLimits
    (longLimit : ProbabilityMeasure
      (FiniteSupportPathSpace (finiteHorizonStepPaths longHorizon rates embedding)))
    (shortLimit : ProbabilityMeasure
      (FiniteSupportPathSpace (finiteHorizonStepPaths shortHorizon rates embedding)))
    (longConvergence : Tendsto (finiteHorizonStepLaw longHorizon rates embedding kernels initial)
      atTop (𝓝 longLimit))
    (shortConvergence : Tendsto (finiteHorizonStepLaw shortHorizon rates embedding kernels initial)
      atTop (𝓝 shortLimit)) :
    longLimit.map
      (finiteHorizonPathRestriction_continuous shortHorizon longHorizon horizonsOrdered rates embedding).measurable.aemeasurable =
      shortLimit := by
  have mappedConvergence := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    _ longLimit longConvergence
    (finiteHorizonPathRestriction_continuous shortHorizon longHorizon horizonsOrdered rates embedding)
  simp only [finiteHorizonPathRestriction_stepLaw] at mappedConvergence
  exact tendsto_nhds_unique mappedConvergence shortConvergence

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizonPathRestriction_continuous
#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizonPathRestriction_stepMap
#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizonPathRestriction_stepLaw
#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizonPathRestriction_weakLimits
