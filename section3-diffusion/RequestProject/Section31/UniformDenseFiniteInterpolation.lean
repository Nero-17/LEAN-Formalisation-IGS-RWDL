import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-! Every uniformly dense linear subspace of continuous real functions on a
compact metric space interpolates arbitrary values on each finite subset.
Explicit products of distances give continuous finite-point interpolants.
The restriction image of the dense subspace is finite dimensional, hence
closed; uniform approximation makes this image dense, so it is all values.
Candidate source: compilation is not claimed. -/

namespace IGS.Sec31
open Set
noncomputable section
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

def finiteInterpolationHat (points : Finset Space) (anchor : points) : C(Space, ℝ) := by
  classical
  exact ⟨fun point => ∏ other : points,
    if other = anchor then 1 else dist point other.val / dist anchor.val other.val, by fun_prop⟩

theorem finiteInterpolationHat_eval (points : Finset Space) (anchor vertex : points) :
    finiteInterpolationHat points anchor vertex.val = if vertex = anchor then 1 else 0 := by
  classical
  by_cases same : vertex = anchor
  · subst vertex
    rw [if_pos rfl]
    change (∏ other : points, if other = anchor then (1 : ℝ) else dist anchor.val other.val / dist anchor.val other.val) = 1
    apply Finset.prod_eq_one
    intro other _
    by_cases identical : other = anchor
    · simp only [if_pos identical]
    · have distinct : anchor.val ≠ other.val := fun equality => identical (Subtype.ext equality.symm)
      simp only [if_neg identical, div_self (dist_ne_zero.mpr distinct)]
  · rw [if_neg same]
    change (∏ other : points, if other = anchor then (1 : ℝ) else dist vertex.val other.val / dist anchor.val other.val) = 0
    apply Finset.prod_eq_zero (Finset.mem_univ vertex)
    simp only [if_neg same, dist_self, zero_div]

def continuousFiniteInterpolation (points : Finset Space) (values : points → ℝ) : C(Space, ℝ) :=
  ⟨fun point => ∑ anchor : points, values anchor * finiteInterpolationHat points anchor point, by fun_prop⟩

theorem continuousFiniteInterpolation_eval (points : Finset Space) (values : points → ℝ) (vertex : points) :
    continuousFiniteInterpolation points values vertex.val = values vertex := by
  classical
  change (∑ anchor : points, values anchor * finiteInterpolationHat points anchor vertex.val) = values vertex
  simp [finiteInterpolationHat_eval, eq_comm]

theorem uniformDenseSubmodule_finite_evaluation_surjective
    (domain : Submodule ℝ C(Space, ℝ))
    (uniformDense : ∀ (target : C(Space, ℝ)) (tolerance : ℝ), 0 < tolerance →
      ∃ approximation : domain, ∀ point, |approximation.val point - target point| < tolerance)
    (points : Finset Space) :
    Function.Surjective (fun function : domain => fun vertex : points => function.val vertex.val) := by
  classical
  let evaluation : domain →ₗ[ℝ] (points → ℝ) :=
    { toFun := fun function vertex => function.val vertex.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have rangeClosed : IsClosed (evaluation.range : Set (points → ℝ)) :=
    evaluation.range.closed_of_finiteDimensional
  intro values
  have valuesInClosure : values ∈ closure (evaluation.range : Set (points → ℝ)) := by
    apply Metric.mem_closure_iff.2
    intro tolerance tolerancePositive
    obtain ⟨approximation, close⟩ := uniformDense (continuousFiniteInterpolation points values)
      (tolerance / 2) (by positivity)
    refine ⟨evaluation approximation, ⟨approximation, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    have normBound : ‖values - evaluation approximation‖ ≤ tolerance / 2 := by
      apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ tolerance / 2)).2
      intro vertex
      change |values vertex - approximation.val vertex.val| ≤ tolerance / 2
      have bounded := (close vertex.val).le
      rw [continuousFiniteInterpolation_eval, abs_sub_comm] at bounded
      exact bounded
    exact normBound.trans_lt (by linarith)
  rw [rangeClosed.closure_eq] at valuesInClosure
  exact valuesInClosure

end
end IGS.Sec31

#print axioms IGS.Sec31.continuousFiniteInterpolation_eval
#print axioms IGS.Sec31.uniformDenseSubmodule_finite_evaluation_surjective
