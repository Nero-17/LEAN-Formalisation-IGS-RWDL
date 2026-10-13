import RequestProject.Section31.FiniteSupportUniformPathSpace
import RequestProject.Section31.DiscreteMarkovTrajectory
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Algebra.Order.Floor.Semiring

/-! Actual finite-horizon step paths of finite Markov chains, with the clock
floor(time * rate), as probability measures on their common uniform closure.
Every finite evaluation law agrees with the same Ionescu--Tulcea trajectory.
No tightness or path-convergence assertion is made. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Preorder Set
open scoped UniformConvergence NNReal

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable {Vertex : ℕ → Type*} [∀ level, Fintype (Vertex level)]
variable [∀ level, MeasurableSpace (Vertex level)]
variable [∀ level, MeasurableSingletonClass (Vertex level)]

variable (horizon : ℝ≥0) (rates : ℕ → ℝ≥0)
variable (embedding : (level : ℕ) → Vertex level → State)

noncomputable def finiteHorizonStepPaths (level : ℕ)
    (history : Finset.Iic ⌊(horizon : ℝ) * (rates level : ℝ)⌋₊ → Vertex level)
    (time : Set.Icc (0 : ℝ) (horizon : ℝ)) : State :=
  embedding level (history ⟨⌊time.val * (rates level : ℝ)⌋₊,
    Finset.mem_Iic.mpr (Nat.floor_mono
      (mul_le_mul_of_nonneg_right time.property.2 (rates level).property))⟩)

noncomputable def finiteHorizonStepMap (level : ℕ) (path : ℕ → Vertex level) :
    FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding) :=
  finitePathEmbedding (finiteHorizonStepPaths horizon rates embedding) level
    (frestrictLe ⌊(horizon : ℝ) * (rates level : ℝ)⌋₊ path)

theorem finiteHorizonStepMap_measurable (level : ℕ) :
    Measurable (finiteHorizonStepMap horizon rates embedding level) :=
  (measurable_of_countable
    (finitePathEmbedding (finiteHorizonStepPaths horizon rates embedding) level)).comp
      (measurable_frestrictLe _)

theorem finiteHorizonStepMap_apply (level : ℕ) (path : ℕ → Vertex level)
    (time : Set.Icc (0 : ℝ) (horizon : ℝ)) :
    UniformFun.toFun (finiteHorizonStepMap horizon rates embedding level path).val time =
      embedding level (path ⌊time.val * (rates level : ℝ)⌋₊) :=
  rfl

theorem finiteHorizonStepMap_range_finite (level : ℕ) :
    (Set.range (finiteHorizonStepMap horizon rates embedding level)).Finite := by
  refine (finitePathEmbedding_range_finite
    (finiteHorizonStepPaths horizon rates embedding) level).subset ?_
  rintro _ ⟨path, rfl⟩
  exact Set.mem_range_self _

variable (kernels : (level : ℕ) → Kernel (Vertex level) (Vertex level))
variable [∀ level, IsMarkovKernel (kernels level)]
variable (initial : (level : ℕ) → ProbabilityMeasure (Vertex level))

noncomputable def finiteHorizonPrefixLaw (level : ℕ) :
    Measure (Finset.Iic ⌊(horizon : ℝ) * (rates level : ℝ)⌋₊ → Vertex level) :=
  (pathLaw (kernels level) (initial level)).map
    (frestrictLe ⌊(horizon : ℝ) * (rates level : ℝ)⌋₊)

instance finiteHorizonPrefixLaw_isProbability (level : ℕ) :
    IsProbabilityMeasure (finiteHorizonPrefixLaw horizon rates kernels initial level) := by
  unfold finiteHorizonPrefixLaw
  exact Measure.isProbabilityMeasure_map (measurable_frestrictLe _).aemeasurable

noncomputable def finiteHorizonStepLaw (level : ℕ) :
    ProbabilityMeasure
      (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding)) :=
  ⟨(finiteHorizonPrefixLaw horizon rates kernels initial level).map
      (finitePathEmbedding (finiteHorizonStepPaths horizon rates embedding) level),
    Measure.isProbabilityMeasure_map
      (measurable_of_countable
        (finitePathEmbedding (finiteHorizonStepPaths horizon rates embedding) level)).aemeasurable⟩

theorem finiteHorizonStepLaw_eq_map (level : ℕ) :
    (finiteHorizonStepLaw horizon rates embedding kernels initial level : Measure _) =
      (pathLaw (kernels level) (initial level)).map
        (finiteHorizonStepMap horizon rates embedding level) := by
  change ((pathLaw (kernels level) (initial level)).map
    (frestrictLe ⌊(horizon : ℝ) * (rates level : ℝ)⌋₊)).map
      (finitePathEmbedding (finiteHorizonStepPaths horizon rates embedding) level) = _
  rw [Measure.map_map
    (μ := pathLaw (kernels level) (initial level))
    (g := finitePathEmbedding (finiteHorizonStepPaths horizon rates embedding) level)
    (f := fun path : ℕ → Vertex level => frestrictLe ⌊(horizon : ℝ) * (rates level : ℝ)⌋₊ path)
    (measurable_of_countable _) (measurable_frestrictLe _)]
  rfl

theorem finiteHorizonStepLaw_finite_evaluations (level dimension : ℕ)
    (times : Fin dimension → Set.Icc (0 : ℝ) (horizon : ℝ)) :
    (finiteHorizonStepLaw horizon rates embedding kernels initial level :
      Measure (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding))).map
        (fun path : FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding) =>
          fun index => UniformFun.toFun path.val (times index)) =
      (pathLaw (kernels level) (initial level)).map
        (fun path => fun index =>
          embedding level (path ⌊(times index).val * (rates level : ℝ)⌋₊)) := by
  rw [finiteHorizonStepLaw_eq_map]
  have evaluationMeasurable : Measurable
      (fun path : FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding) =>
        fun index => UniformFun.toFun path.val (times index)) := by
    exact measurable_pi_lambda _ fun index =>
      (finiteSupportPathSpace_continuous_eval
        (finiteHorizonStepPaths horizon rates embedding) (times index)).measurable
  rw [Measure.map_map evaluationMeasurable
    (finiteHorizonStepMap_measurable horizon rates embedding level)]
  rfl

theorem finiteHorizonStepLaw_coordinate (level : ℕ)
    (time : Set.Icc (0 : ℝ) (horizon : ℝ)) :
    (finiteHorizonStepLaw horizon rates embedding kernels initial level :
      Measure (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding))).map
        (fun path : FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding) =>
          UniformFun.toFun path.val time) =
      ((kernels level ^ ⌊time.val * (rates level : ℝ)⌋₊) ∘ₘ
        (initial level : Measure (Vertex level))).map (embedding level) := by
  rw [finiteHorizonStepLaw_eq_map,
    Measure.map_map
      (finiteSupportPathSpace_continuous_eval
        (finiteHorizonStepPaths horizon rates embedding) time).measurable
      (finiteHorizonStepMap_measurable horizon rates embedding level)]
  have factor :
      (fun path : ℕ → Vertex level =>
        embedding level (path ⌊time.val * (rates level : ℝ)⌋₊)) =
      (embedding level) ∘ (fun path : ℕ → Vertex level =>
        path ⌊time.val * (rates level : ℝ)⌋₊) := rfl
  change (pathLaw (kernels level) (initial level)).map
    (fun path => embedding level (path ⌊time.val * (rates level : ℝ)⌋₊)) = _
  rw [factor, ← Measure.map_map (g := embedding level)
    (f := fun path : ℕ → Vertex level => path ⌊time.val * (rates level : ℝ)⌋₊)
    (measurable_of_countable _) (measurable_pi_apply _), pathLaw_coordinate_iterates]

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizonStepMap_measurable
#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizonStepMap_apply
#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizonStepMap_range_finite
#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizonPrefixLaw_isProbability
#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizonStepLaw_eq_map
#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizonStepLaw_finite_evaluations
#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizonStepLaw_coordinate
