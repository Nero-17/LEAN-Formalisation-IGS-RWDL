import RequestProject.Outlook.FourColourChildCodingLaw

/-! Explicit independent branching law for the adopted four-colour encoding.
Only the already verified one-cell conditional distribution is used to choose
an offspring outcome. The all-depth actual-law identity is proved separately. -/
namespace Outlook.FourColourBranchingLaw
open Cluster FourColourRuleAudit FourColourOrientationCandidate FourColourConditionalHierarchy
open FourColourCodingTree FourColourChildCodingLaw MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

def assemble (depth : ℕ) (outcome : Fin 9)
    (children : RuleTree depth × RuleTree depth × RuleTree depth × RuleTree depth) :
    RuleTree (depth+1) :=
  (outcome, ![children.1, children.2.1, children.2.2.1, children.2.2.2])

noncomputable def branchFromLaws (depth : ℕ) (parent : Fin 4) (outcome : Fin 9)
    (laws : Fin 4 → Measure (RuleTree depth)) : Measure (RuleTree (depth+1)) :=
  ((laws (colour parent outcome 0)).prod
    ((laws (colour parent outcome 1)).prod
      ((laws (colour parent outcome 2)).prod (laws (colour parent outcome 3))))).map
    (assemble depth outcome)

/-- Independent offspring choices at every cell, using the genuine one-cell
conditional Bernoulli law. Green outcomes merge exactly the verified fibres. -/
noncomputable def ruleTreeLaw : (depth : ℕ) → Fin 4 → Measure (RuleTree depth)
  | 0, _ => Measure.dirac ()
  | depth+1, parent =>
      ∑ configuration : Conf 1,
        (parentMeasure 1 parent {configuration}) •
          branchFromLaws depth parent (conditionedOutcome parent configuration) (ruleTreeLaw depth)

def childTupleEncoding (depth : ℕ) (parent : Fin 4) (coarseConfiguration : Conf 1)
    (configuration : Conf (depth+1)) :
    RuleTree depth × RuleTree depth × RuleTree depth × RuleTree depth :=
  (childEncoding depth parent coarseConfiguration 0 configuration.1,
    childEncoding depth parent coarseConfiguration 1 configuration.2.1,
    childEncoding depth parent coarseConfiguration 2 configuration.2.2.1,
    childEncoding depth parent coarseConfiguration 3 configuration.2.2.2)

theorem encode_on_coarse_fiber (depth : ℕ) (parent : Fin 4) (coarseConfiguration : Conf 1)
    (configuration : Conf (depth+1)) (membership : firstGeneration depth configuration=coarseConfiguration) :
    encode (depth+1) parent configuration =
      assemble depth (conditionedOutcome parent coarseConfiguration)
        (childTupleEncoding depth parent coarseConfiguration configuration) := by
  subst coarseConfiguration
  change (_, _) = (_, _)
  congr 1
  funext edge
  fin_cases edge <;> rfl

theorem actual_conditional_encode_branch (depth : ℕ) (parent : Fin 4)
    (coarseConfiguration : Conf 1) (condition : coarseConfiguration ∈ conditioningEvent parent) :
    (ProbabilityTheory.cond (confMeasure Reduced.pc (depth+1))
      {configuration | firstGeneration depth configuration=coarseConfiguration}).map
      (encode (depth+1) parent) =
      branchFromLaws depth parent (conditionedOutcome parent coarseConfiguration) (encodedLaw depth) := by
  have mapping : (encode (depth+1) parent) =ᵐ[
      ProbabilityTheory.cond (confMeasure Reduced.pc (depth+1))
        {configuration | firstGeneration depth configuration=coarseConfiguration}]
      assemble depth (conditionedOutcome parent coarseConfiguration) ∘
        childTupleEncoding depth parent coarseConfiguration :=
    ae_cond_of_forall_mem MeasurableSet.of_discrete
      (fun configuration membership => encode_on_coarse_fiber depth parent coarseConfiguration
        configuration membership)
  rw [Measure.map_congr mapping,
    ← Measure.map_map Measurable.of_discrete Measurable.of_discrete]
  unfold childTupleEncoding
  rw [actual_four_child_encoding_law depth parent coarseConfiguration condition]
  rfl

theorem parent_conditioned_coarse_fiber (depth : ℕ) (parent : Fin 4)
    (coarseConfiguration : Conf 1) (condition : coarseConfiguration ∈ conditioningEvent parent) :
    ProbabilityTheory.cond (parentMeasure (depth+1) parent)
        {configuration | firstGeneration depth configuration=coarseConfiguration} =
      ProbabilityTheory.cond (confMeasure Reduced.pc (depth+1))
        {configuration | firstGeneration depth configuration=coarseConfiguration} := by
  haveI := isProb_confMeasure Reduced.pc_pos.le Reduced.pc_lt_one.le (depth+1)
  rw [parentMeasure, cond_cond_eq_cond_inter MeasurableSet.of_discrete MeasurableSet.of_discrete]
  congr 1
  apply Set.inter_eq_right.mpr
  intro configuration membership
  rw [parentEvent_preimage]
  change firstGeneration depth configuration ∈ conditioningEvent parent
  rw [membership]
  exact condition

theorem coarse_fiber_mass (depth : ℕ) (parent : Fin 4) (coarseConfiguration : Conf 1) :
    parentMeasure (depth+1) parent (firstGeneration depth ⁻¹' {coarseConfiguration}) =
      parentMeasure 1 parent {coarseConfiguration} := by
  have mapping := congrArg (fun measure : Measure (Conf 1) => measure {coarseConfiguration})
    (firstGeneration_parentMeasure depth parent)
  dsimp only at mapping
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete] at mapping
  exact mapping

private theorem inadmissible_singleton (parent : Fin 4) (configuration : Conf 1)
    (condition : configuration ∉ conditioningEvent parent) :
    parentMeasure 1 parent {configuration} = 0 := by
  have intersection : parentEvent 1 parent ∩ {configuration} = ∅ := by
    ext candidate
    simp only [Set.mem_empty_iff_false, iff_false]
    intro membership
    have equal : candidate=configuration := membership.2
    subst candidate
    exact condition membership.1
  rw [parentMeasure, cond_apply MeasurableSet.of_discrete, intersection]
  simp

/-- The actual extracted-tree law has the explicit independent branching
recursion. The sum over sixteen Bernoulli patterns automatically merges the
four green outcomes, without conditioning on unretained black information. -/
theorem encodedLaw_recursion (depth : ℕ) (parent : Fin 4) :
    encodedLaw (depth+1) parent =
      ∑ configuration : Conf 1,
        (parentMeasure 1 parent {configuration}) •
          branchFromLaws depth parent (conditionedOutcome parent configuration) (encodedLaw depth) := by
  ext target targetMeasurable
  rw [encodedLaw, Measure.map_apply Measurable.of_discrete targetMeasurable]
  have decomposition := congrArg
    (fun measure : Measure (Conf (depth+1)) => measure (encode (depth+1) parent ⁻¹' target))
    (sum_meas_smul_cond_fiber (X := firstGeneration depth) Measurable.of_discrete
      (parentMeasure (depth+1) parent))
  dsimp only at decomposition
  simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.coe_smul,
    Pi.smul_apply, smul_eq_mul] at decomposition ⊢
  rw [← decomposition]
  apply Finset.sum_congr rfl
  intro configuration _
  rw [coarse_fiber_mass]
  by_cases condition : configuration ∈ conditioningEvent parent
  · have branch := congrArg (fun measure : Measure (RuleTree (depth+1)) => measure target)
      (actual_conditional_encode_branch depth parent configuration condition)
    dsimp only at branch
    rw [Measure.map_apply Measurable.of_discrete targetMeasurable] at branch
    change (parentMeasure 1 parent {configuration}) *
      (ProbabilityTheory.cond (parentMeasure (depth+1) parent)
        {candidate | firstGeneration depth candidate=configuration})
        (encode (depth+1) parent ⁻¹' target) = _
    rw [parent_conditioned_coarse_fiber depth parent configuration condition, branch]
  · rw [inadmissible_singleton parent configuration condition]
    simp

theorem actual_encodedLaw_eq_ruleTreeLaw (depth : ℕ) (parent : Fin 4) :
    encodedLaw depth parent = ruleTreeLaw depth parent := by
  induction depth generalizing parent with
  | zero =>
      change (parentMeasure 0 parent).map (fun _ => ()) = Measure.dirac ()
      simp
  | succ depth induction =>
      rw [encodedLaw_recursion]
      have laws : encodedLaw depth = ruleTreeLaw depth := funext induction
      rw [laws]
      rfl

end Outlook.FourColourBranchingLaw

#print axioms Outlook.FourColourBranchingLaw.encode_on_coarse_fiber
#print axioms Outlook.FourColourBranchingLaw.actual_conditional_encode_branch
#print axioms Outlook.FourColourBranchingLaw.parent_conditioned_coarse_fiber
#print axioms Outlook.FourColourBranchingLaw.coarse_fiber_mass
#print axioms Outlook.FourColourBranchingLaw.encodedLaw_recursion
#print axioms Outlook.FourColourBranchingLaw.actual_encodedLaw_eq_ruleTreeLaw
