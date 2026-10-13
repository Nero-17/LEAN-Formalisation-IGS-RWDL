import RequestProject.Section2ConcreteBallBarrier
import RequestProject.Section2ExitComparison

/-! Actual multi-step incident stars and a recursively extended metric
potential. Every vertex predicate and distance is on the original Xi tower. -/

namespace EIGS

open scoped BigOperators Classical

variable {K : ℕ}

def xiIncidentStar (system : EIGSData K) (coarse : ℕ) (center : XiVtx system coarse) :
    (steps : ℕ) → XiVtx system (coarse + steps) → Prop
  | 0, vertex => vertex = center
  | steps + 1, Sum.inl vertex => xiIncidentStar system coarse center steps vertex
  | steps + 1, Sum.inr ⟨edge, _⟩ =>
      xiIncidentStar system coarse center steps (XiTail system (coarse + steps) edge) ∨
      xiIncidentStar system coarse center steps (XiHead system (coarse + steps) edge)

noncomputable def xiRefinedMetricPotential (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected) (coarse : ℕ)
    (potential : XiVtx system coarse → ℝ) :
    (steps : ℕ) → (Fin K → ℝ) → XiVtx system (coarse + steps) → ℝ
  | 0, _ => potential
  | steps + 1, lengths =>
      (XiNetwork system (coarse + steps)).substMetricPotential
        (system.ruleFamily rule_connected) lengths
        (xiRefinedMetricPotential system rule_connected coarse potential steps
          ((system.ruleFamily rule_connected).metricLengths lengths))

theorem xiRefinedMetricPotential_lipschitz (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected) (coarse steps : ℕ)
    (potential : XiVtx system coarse → ℝ) {lengths : Fin K → ℝ}
    (nonnegative : 0 ≤ lengths)
    (base_lipschitz : (XiNetwork system coarse).EdgeLipschitz
      ((system.ruleFamily rule_connected).metricLengths^[steps] lengths) potential) :
    (XiNetwork system (coarse + steps)).EdgeLipschitz lengths
      (xiRefinedMetricPotential system rule_connected coarse potential steps lengths) := by
  induction steps generalizing lengths with
  | zero => exact base_lipschitz
  | succ steps induction_hypothesis =>
    have previous_lipschitz := induction_hypothesis
      (Network.metricLengths_nonnegative (system.ruleFamily rule_connected)
        rule_connected nonnegative)
      (by simpa only [Function.iterate_succ_apply] using base_lipschitz)
    exact (XiNetwork system (coarse + steps)).substMetricPotential_lipschitz
      (system.ruleFamily rule_connected) rule_connected nonnegative _ previous_lipschitz

theorem xiRefinedMetricPotential_on_old (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected) (coarse steps : ℕ)
    (potential : XiVtx system coarse → ℝ) (lengths : Fin K → ℝ)
    (vertex : XiVtx system coarse) :
    xiRefinedMetricPotential system rule_connected coarse potential steps lengths
      (xiForward system coarse steps vertex) = potential vertex := by
  induction steps generalizing lengths with
  | zero => rfl
  | succ steps induction_hypothesis => exact induction_hypothesis _

theorem xiRefinedMetricPotential_ge_outside_star (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected) (coarse steps : ℕ)
    (center : XiVtx system coarse) {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths)
    {radius : ℝ} (radius_nonnegative : 0 ≤ radius)
    (vertex : XiVtx system (coarse + steps))
    (outside : ¬ xiIncidentStar system coarse center steps vertex) :
    radius ≤ xiRefinedMetricPotential system rule_connected coarse
      (fun old_vertex => if old_vertex = center then 0 else radius) steps lengths vertex := by
  induction steps generalizing lengths with
  | zero =>
    have different : vertex ≠ center := outside
    simp only [xiRefinedMetricPotential, different, ↓reduceIte, le_refl]
  | succ steps induction_hypothesis =>
    have previous_nonnegative := Network.metricLengths_nonnegative
      (system.ruleFamily rule_connected) rule_connected nonnegative
    cases vertex with
    | inl old_vertex => exact induction_hypothesis previous_nonnegative old_vertex outside
    | inr private_vertex =>
      obtain ⟨edge, interior⟩ := private_vertex
      have endpoint_outside :
          ¬ xiIncidentStar system coarse center steps (XiTail system (coarse + steps) edge) ∧
          ¬ xiIncidentStar system coarse center steps (XiHead system (coarse + steps) edge) :=
        not_or.mp outside
      have tail_bound := induction_hypothesis previous_nonnegative _ endpoint_outside.1
      have head_bound := induction_hypothesis previous_nonnegative _ endpoint_outside.2
      change radius ≤ min (_ + _) (_ + _)
      exact le_min
        (tail_bound.trans (le_add_of_nonneg_right
          ((system.ruleNetwork (XiCol system.toRuleData (coarse + steps) edge)).weightedDistance_nonnegative
            (rule_connected _) nonnegative _ _)))
        (head_bound.trans (le_add_of_nonneg_right
          ((system.ruleNetwork (XiCol system.toRuleData (coarse + steps) edge)).weightedDistance_nonnegative
            (rule_connected _) nonnegative _ _)))

theorem xiWeightedDistance_ge_radius_outside_multistep_star (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected) (coarse steps : ℕ)
    (center : XiVtx system coarse) {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths)
    {radius : ℝ} (radius_nonnegative : 0 ≤ radius)
    (rule_distance_bound : ∀ colour,
      radius ≤ ((system.ruleFamily rule_connected).metricLengths^[steps] lengths) colour)
    (vertex : XiVtx system (coarse + steps))
    (outside : ¬ xiIncidentStar system coarse center steps vertex) :
    radius ≤ (XiNetwork system (coarse + steps)).weightedDistance lengths
      (xiForward system coarse steps center) vertex := by
  let potential : XiVtx system coarse → ℝ :=
    fun old_vertex => if old_vertex = center then 0 else radius
  have base_lipschitz : (XiNetwork system coarse).EdgeLipschitz
      ((system.ruleFamily rule_connected).metricLengths^[steps] lengths) potential := by
    intro edge
    by_cases tail_center : XiTail system coarse edge = center <;>
      by_cases head_center : XiHead system coarse edge = center <;>
      simp only [XiNetwork, potential, tail_center, head_center, ↓reduceIte, sub_self,
        abs_zero, zero_sub, abs_neg, sub_zero, abs_of_nonneg radius_nonnegative] <;>
      first | exact rule_distance_bound _ | exact radius_nonnegative.trans (rule_distance_bound _)
  have extended_lipschitz := xiRefinedMetricPotential_lipschitz system rule_connected
    coarse steps potential nonnegative base_lipschitz
  have potential_bound := xiRefinedMetricPotential_ge_outside_star system rule_connected
    coarse steps center nonnegative radius_nonnegative vertex outside
  have difference_bound := (XiNetwork system (coarse + steps)).potential_difference_le_weightedDistance
    (xiSimpleGraph_connected system rule_connected (coarse + steps)) extended_lipschitz
      (xiForward system coarse steps center) vertex
  rw [xiRefinedMetricPotential_on_old] at difference_bound
  simp only [potential, ↓reduceIte, zero_sub, abs_neg] at difference_bound
  exact potential_bound.trans ((le_abs_self _).trans difference_bound)

theorem xiWeightedBall_subset_multistep_star (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected) (coarse steps : ℕ)
    (center : XiVtx system coarse) {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths)
    {radius : ℝ} (radius_nonnegative : 0 ≤ radius)
    (rule_distance_bound : ∀ colour,
      radius ≤ ((system.ruleFamily rule_connected).metricLengths^[steps] lengths) colour)
    (vertex : XiVtx system (coarse + steps))
    (in_ball : (XiNetwork system (coarse + steps)).weightedDistance lengths
      (xiForward system coarse steps center) vertex < radius) :
    xiIncidentStar system coarse center steps vertex := by
  by_contra outside
  exact (not_lt_of_ge (xiWeightedDistance_ge_radius_outside_multistep_star system
    rule_connected coarse steps center nonnegative radius_nonnegative rule_distance_bound
    vertex outside)) in_ball

end EIGS

#print axioms EIGS.xiRefinedMetricPotential_lipschitz
#print axioms EIGS.xiRefinedMetricPotential_on_old
#print axioms EIGS.xiRefinedMetricPotential_ge_outside_star
#print axioms EIGS.xiWeightedDistance_ge_radius_outside_multistep_star
#print axioms EIGS.xiWeightedBall_subset_multistep_star
