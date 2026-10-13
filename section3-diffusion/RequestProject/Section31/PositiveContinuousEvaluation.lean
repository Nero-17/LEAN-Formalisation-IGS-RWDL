import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Tactic

/-! A positive linear functional which evaluates a uniformly dense core and
constants must evaluate every continuous function in its domain. The domain
may be the continuous part of an energy completion; no equality of domains is
assumed. -/

namespace IGS.Sec31

variable {Space : Type*} [TopologicalSpace Space]

theorem positive_linearMap_eq_evaluation_of_uniform_core
    (domain : Submodule ℝ C(Space, ℝ)) (functional : domain →ₗ[ℝ] ℝ) (point : Space)
    (positive : ∀ values : domain, (∀ x, 0 ≤ values.val x) → 0 ≤ functional values)
    (constants : ∀ value : ℝ, ∃ membership : ContinuousMap.const Space value ∈ domain,
      functional ⟨ContinuousMap.const Space value, membership⟩ = value)
    (approximation : ∀ target : domain, ∀ tolerance > 0, ∃ approximant : domain,
      functional approximant = approximant.val point ∧
        ∀ x, |approximant.val x - target.val x| < tolerance)
    (target : domain) : functional target = target.val point := by
  have comparison : ∀ tolerance > 0, |functional target - target.val point| ≤ 2 * tolerance := by
    intro tolerance tolerancePositive
    obtain ⟨approximant, approximantValue, approximantClose⟩ := approximation target tolerance tolerancePositive
    obtain ⟨constantMember, constantValue⟩ := constants tolerance
    let constant : domain := ⟨ContinuousMap.const Space tolerance, constantMember⟩
    have upperNonnegative : 0 ≤ functional (approximant + constant - target) := by
      apply positive
      intro x
      change 0 ≤ approximant.val x + tolerance - target.val x
      have := (abs_lt.mp (approximantClose x)).1
      linarith
    have lowerNonnegative : 0 ≤ functional (target + constant - approximant) := by
      apply positive
      intro x
      change 0 ≤ target.val x + tolerance - approximant.val x
      have := (abs_lt.mp (approximantClose x)).2
      linarith
    have constantEquality : functional constant = tolerance := constantValue
    simp only [map_add, map_sub, approximantValue, constantEquality] at upperNonnegative lowerNonnegative
    have pointClose := abs_lt.mp (approximantClose point)
    apply abs_le.mpr
    constructor <;> linarith
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  apply le_of_forall_pos_le_add
  intro tolerance tolerancePositive
  have := comparison (tolerance / 2) (by positivity)
  linarith

end IGS.Sec31

#print axioms IGS.Sec31.positive_linearMap_eq_evaluation_of_uniform_core
