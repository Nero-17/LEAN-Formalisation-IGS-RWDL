import RequestProject.Section31.FiniteHorizonMarkovStepPathLaw
import RequestProject.Section31.FiniteSupportPathModulus
import Mathlib.Tactic

/-! Exact transfer of the floor-path modulus event to the common uniform
path-space law. The good modulus constraint is closed, hence measurable. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set
open scoped UniformConvergence NNReal

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable {Vertex : ℕ → Type*} [∀ level, Fintype (Vertex level)]
variable [∀ level, MeasurableSpace (Vertex level)]
variable [∀ level, MeasurableSingletonClass (Vertex level)]
variable (horizon : ℝ≥0) (rates : ℕ → ℝ≥0)
variable (embedding : (level : ℕ) → Vertex level → State)

theorem finiteHorizonStepMap_modulus_compl_preimage (level : ℕ) (window error : ℝ) :
    (finiteHorizonStepMap horizon rates embedding level) ⁻¹'
      (finiteSupportPathModulusSet (finiteHorizonStepPaths horizon rates embedding) window error)ᶜ =
    {path | ∃ first ∈ Set.Icc (0 : ℝ) (horizon : ℝ),
      ∃ second ∈ Set.Icc (0 : ℝ) (horizon : ℝ),
        |second - first| ≤ window ∧ error <
          dist (embedding level (path ⌊first * (rates level : ℝ)⌋₊))
            (embedding level (path ⌊second * (rates level : ℝ)⌋₊))} := by
  classical
  ext path
  change (¬ ∀ first second : Set.Icc (0 : ℝ) (horizon : ℝ), dist first second ≤ window →
    dist (embedding level (path ⌊first.val * (rates level : ℝ)⌋₊))
      (embedding level (path ⌊second.val * (rates level : ℝ)⌋₊)) ≤ error) ↔ _
  push_neg
  constructor
  · rintro ⟨first, second, close, far⟩
    refine ⟨first.val, first.property, second.val, second.property, ?_, far⟩
    simpa only [Subtype.dist_eq, Real.dist_eq, abs_sub_comm] using close
  · rintro ⟨first, firstBounds, second, secondBounds, close, far⟩
    refine ⟨⟨first, firstBounds⟩, ⟨second, secondBounds⟩, ?_, far⟩
    simpa only [Subtype.dist_eq, Real.dist_eq, abs_sub_comm] using close

variable (kernels : (level : ℕ) → Kernel (Vertex level) (Vertex level))
variable [∀ level, IsMarkovKernel (kernels level)]
variable (initial : (level : ℕ) → ProbabilityMeasure (Vertex level))

theorem finiteHorizonStepLaw_modulus_compl (level : ℕ) (window error : ℝ) :
    (finiteHorizonStepLaw horizon rates embedding kernels initial level : Measure _)
      (finiteSupportPathModulusSet (finiteHorizonStepPaths horizon rates embedding) window error)ᶜ =
    (pathLaw (kernels level) (initial level))
      {path | ∃ first ∈ Set.Icc (0 : ℝ) (horizon : ℝ),
        ∃ second ∈ Set.Icc (0 : ℝ) (horizon : ℝ),
          |second - first| ≤ window ∧ error <
            dist (embedding level (path ⌊first * (rates level : ℝ)⌋₊))
              (embedding level (path ⌊second * (rates level : ℝ)⌋₊))} := by
  rw [finiteHorizonStepLaw_eq_map]
  rw [Measure.map_apply (finiteHorizonStepMap_measurable horizon rates embedding level)
    (finiteSupportPathModulusSet_isClosed (finiteHorizonStepPaths horizon rates embedding)
      window error).measurableSet.compl]
  exact congrArg (pathLaw (kernels level) (initial level))
    (finiteHorizonStepMap_modulus_compl_preimage horizon rates embedding level window error)

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizonStepMap_modulus_compl_preimage
#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizonStepLaw_modulus_compl
