import RequestProject.Cluster.InfiniteTree

/-! # Deterministic bounds on the actual nested replacement trees -/

namespace Cluster

open Reduced

noncomputable section

private theorem parallel_monotone {first second larger_first larger_second : ℝ}
    (first_positive : 0 < first) (second_positive : 0 < second)
    (first_bound : first ≤ larger_first) (second_bound : second ≤ larger_second) :
    par first second ≤ par larger_first larger_second := by
  have larger_first_positive := lt_of_lt_of_le first_positive first_bound
  have first_step := par_monotoneOn_left second_positive
    first_positive.le larger_first_positive.le first_bound
  have second_step := par_monotoneOn_left larger_first_positive
    second_positive.le (lt_of_lt_of_le second_positive second_bound).le second_bound
  have second_step_commuted : par larger_first second ≤ par larger_first larger_second := by
    simpa only [par, mul_comm, add_comm] using second_step
  exact first_step.trans second_step_commuted

private theorem diamond_monotone
    {first second third fourth larger_first larger_second larger_third larger_fourth : ℝ}
    (first_positive : 0 < first) (second_positive : 0 < second)
    (third_positive : 0 < third) (fourth_positive : 0 < fourth)
    (first_bound : first ≤ larger_first) (second_bound : second ≤ larger_second)
    (third_bound : third ≤ larger_third) (fourth_bound : fourth ≤ larger_fourth) :
    diamondVal first second third fourth ≤
      diamondVal larger_first larger_second larger_third larger_fourth :=
  parallel_monotone (add_pos first_positive second_positive)
    (add_pos third_positive fourth_positive)
    (add_le_add first_bound second_bound) (add_le_add third_bound fourth_bound)

private theorem diamond_double (first second third fourth : ℝ) :
    diamondVal (2 * first) (2 * second) (2 * third) (2 * fourth) =
      2 * diamondVal first second third fourth := by
  simpa only [diamondMap] using
    diamondMap_scale (show (2 : ℝ) ≠ 0 by norm_num) (first, second, third, fourth)

/-- Every finite reduced network, without any probability qualification, has these bounds. -/
theorem Rres_bounds : ∀ (n : ℕ) (tree : RConf n),
    1 ≤ Rres n tree ∧ Rres n tree ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => intro tree; simp
  | succ n induction_hypothesis =>
      intro tree
      change (RConf n × RConf n) ⊕ ((RConf n × RConf n) × (RConf n × RConf n)) at tree
      cases tree with
      | inl branches =>
          have first_bounds := induction_hypothesis branches.1
          have second_bounds := induction_hypothesis branches.2
          have combined_bounds := series_bounds first_bounds.1 first_bounds.2
            second_bounds.1 second_bounds.2
          change 1 ≤ Rres n branches.1 + Rres n branches.2 ∧ _
          refine ⟨combined_bounds.1, ?_⟩
          simpa only [pow_succ, mul_comm] using combined_bounds.2
      | inr branches =>
          have first_bounds := induction_hypothesis branches.1.1
          have second_bounds := induction_hypothesis branches.1.2
          have third_bounds := induction_hypothesis branches.2.1
          have fourth_bounds := induction_hypothesis branches.2.2
          have combined_bounds := diamond_bounds first_bounds.1 first_bounds.2
            second_bounds.1 second_bounds.2 third_bounds.1 third_bounds.2
            fourth_bounds.1 fourth_bounds.2
          change 1 ≤ diamondVal _ _ _ _ ∧ _
          refine ⟨combined_bounds.1, combined_bounds.2.trans ?_⟩
          rw [pow_succ]
          have nonnegative_power : 0 ≤ (2 : ℝ) ^ n := by positivity
          linarith

/-- Forgetting one generation changes resistance by a factor between one and two. -/
theorem Rres_refinement_bounds : ∀ (n : ℕ) (tree : RConf (n + 1)),
    Rres n (rtrunc n tree) ≤ Rres (n + 1) tree ∧
      Rres (n + 1) tree ≤ 2 * Rres n (rtrunc n tree) := by
  intro n
  induction n with
  | zero =>
      intro tree
      change (RConf 0 × RConf 0) ⊕ ((RConf 0 × RConf 0) × (RConf 0 × RConf 0)) at tree
      cases tree <;> norm_num [Rres, rtrunc, diamondVal, par]
  | succ n induction_hypothesis =>
      intro tree
      change (RConf (n + 1) × RConf (n + 1)) ⊕
        ((RConf (n + 1) × RConf (n + 1)) ×
          (RConf (n + 1) × RConf (n + 1))) at tree
      cases tree with
      | inl branches =>
          have first_refinement := induction_hypothesis branches.1
          have second_refinement := induction_hypothesis branches.2
          change Rres n (rtrunc n branches.1) + Rres n (rtrunc n branches.2) ≤
              Rres (n + 1) branches.1 + Rres (n + 1) branches.2 ∧
            Rres (n + 1) branches.1 + Rres (n + 1) branches.2 ≤
              2 * (Rres n (rtrunc n branches.1) + Rres n (rtrunc n branches.2))
          constructor <;> linarith
      | inr branches =>
          have first_refinement := induction_hypothesis branches.1.1
          have second_refinement := induction_hypothesis branches.1.2
          have third_refinement := induction_hypothesis branches.2.1
          have fourth_refinement := induction_hypothesis branches.2.2
          have coarse_first_positive := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
            (Rres_bounds n (rtrunc n branches.1.1)).1
          have coarse_second_positive := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
            (Rres_bounds n (rtrunc n branches.1.2)).1
          have coarse_third_positive := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
            (Rres_bounds n (rtrunc n branches.2.1)).1
          have coarse_fourth_positive := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
            (Rres_bounds n (rtrunc n branches.2.2)).1
          change diamondVal _ _ _ _ ≤ diamondVal _ _ _ _ ∧ _
          constructor
          · exact diamond_monotone coarse_first_positive coarse_second_positive
              coarse_third_positive coarse_fourth_positive first_refinement.1
              second_refinement.1 third_refinement.1 fourth_refinement.1
          · calc
              diamondVal _ _ _ _ ≤ diamondVal
                  (2 * Rres n (rtrunc n branches.1.1))
                  (2 * Rres n (rtrunc n branches.1.2))
                  (2 * Rres n (rtrunc n branches.2.1))
                  (2 * Rres n (rtrunc n branches.2.2)) :=
                diamond_monotone
                  (lt_of_lt_of_le coarse_first_positive first_refinement.1)
                  (lt_of_lt_of_le coarse_second_positive second_refinement.1)
                  (lt_of_lt_of_le coarse_third_positive third_refinement.1)
                  (lt_of_lt_of_le coarse_fourth_positive fourth_refinement.1)
                  first_refinement.2 second_refinement.2 third_refinement.2 fourth_refinement.2
              _ = _ := diamond_double _ _ _ _

/-- The refinement inequalities hold at every sample point of the actual infinite tree. -/
theorem nested_network_refinement_bounds (tree : NestedTree) (n : ℕ) :
    (treeNetwork n (nestedTree n tree)).effRes.toReal ≤
        (treeNetwork (n + 1) (nestedTree (n + 1) tree)).effRes.toReal ∧
      (treeNetwork (n + 1) (nestedTree (n + 1) tree)).effRes.toReal ≤
        2 * (treeNetwork n (nestedTree n tree)).effRes.toReal := by
  simpa only [treeNetwork_toReal_effRes, nestedTree_bonded] using
    Rres_refinement_bounds n (nestedTree (n + 1) tree)

end
end Cluster
