import RequestProject.Section31.FiniteSupportUniformPathSpace
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! Closed modulus constraints in the common separable uniform path space.
Vanishing modulus bounds imply continuity of limit paths; no continuity of
the individual finite step paths is imposed. -/

namespace IGS.Sec31.DiscreteMarkov

open Set Filter
open scoped UniformConvergence Topology

variable {Time State : Type*} [PseudoMetricSpace Time] [MetricSpace State] [CompactSpace State]
variable {History : ℕ → Type*} [∀ level, Finite (History level)]
variable (paths : (level : ℕ) → History level → Time → State)

def finiteSupportPathModulusSet (window error : ℝ) : Set (FiniteSupportPathSpace paths) :=
  {path | ∀ first second : Time, dist first second ≤ window →
    dist (UniformFun.toFun path.val first) (UniformFun.toFun path.val second) ≤ error}

theorem finiteSupportPathModulusSet_isClosed (window error : ℝ) :
    IsClosed (finiteSupportPathModulusSet paths window error) := by
  have representation : finiteSupportPathModulusSet paths window error =
      ⋂ first : Time, ⋂ second : Time, ⋂ (_ : dist first second ≤ window),
        {path : FiniteSupportPathSpace paths |
          dist (UniformFun.toFun path.val first) (UniformFun.toFun path.val second) ≤ error} := by
    ext path
    simp only [finiteSupportPathModulusSet, Set.mem_setOf_eq, Set.mem_iInter]
  rw [representation]
  exact isClosed_iInter fun first => isClosed_iInter fun second => isClosed_iInter fun _ =>
    isClosed_le ((finiteSupportPathSpace_continuous_eval paths first).dist
      (finiteSupportPathSpace_continuous_eval paths second)) continuous_const

theorem finiteSupportPath_uniformContinuous_of_vanishing_modulus
    (path : FiniteSupportPathSpace paths) (windows errors : ℕ → ℝ)
    (windowsPositive : ∀ index, 0 < windows index)
    (errorsVanish : Tendsto errors atTop (𝓝 0))
    (modulus : ∀ index, path ∈ finiteSupportPathModulusSet paths (windows index) (errors index)) :
    UniformContinuous (UniformFun.toFun path.val) := by
  apply Metric.uniformContinuous_iff.mpr
  intro tolerance tolerancePositive
  obtain ⟨index, errorSmall⟩ := (errorsVanish.eventually (gt_mem_nhds tolerancePositive)).exists
  refine ⟨windows index, windowsPositive index, ?_⟩
  intro first second close
  exact (modulus index first second close.le).trans_lt errorSmall

theorem finiteSupportPath_continuous_of_vanishing_modulus
    (path : FiniteSupportPathSpace paths) (windows errors : ℕ → ℝ)
    (windowsPositive : ∀ index, 0 < windows index)
    (errorsVanish : Tendsto errors atTop (𝓝 0))
    (modulus : ∀ index, path ∈ finiteSupportPathModulusSet paths (windows index) (errors index)) :
    Continuous (UniformFun.toFun path.val) :=
  (finiteSupportPath_uniformContinuous_of_vanishing_modulus paths path windows errors
    windowsPositive errorsVanish modulus).continuous

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPathModulusSet_isClosed
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPath_uniformContinuous_of_vanishing_modulus
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPath_continuous_of_vanishing_modulus
