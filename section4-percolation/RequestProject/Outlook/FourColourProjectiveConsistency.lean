import RequestProject.Outlook.FourColourLiteralRealization
import RequestProject.Cluster.InfiniteProcess

/-! Compatibility with the original coarse-graining coupling. The level laws
are never treated as independent across depth. This first interface proves
projective consistency before constructing any new infinite tree measure. -/
namespace Outlook.FourColourProjectiveConsistency
open Cluster MeasureTheory ProbabilityTheory FourColourRuleAudit FourColourOrientationCandidate
open FourColourConditionalHierarchy FourColourCodingTree FourColourBranchingLaw

def truncateRuleTree : (depth : ℕ) → RuleTree (depth+1) → RuleTree depth
  | 0, _ => ()
  | depth+1, tree => (tree.1, fun edge => truncateRuleTree depth (tree.2 edge))

theorem coarse_reverseConfiguration (depth : ℕ) (configuration : Conf (depth+1)) :
    coarse depth (reverseConfiguration (depth+1) configuration) =
      reverseConfiguration depth (coarse depth configuration) := by
  induction depth with
  | zero => exact conn_reverseConfiguration 1 configuration
  | succ depth induction =>
      rcases configuration with ⟨first,second,third,fourth⟩
      change (coarse depth (reverseConfiguration (depth+1) second),
        coarse depth (reverseConfiguration (depth+1) first),
        coarse depth (reverseConfiguration (depth+1) fourth),
        coarse depth (reverseConfiguration (depth+1) third)) = _
      rw [induction, induction, induction, induction]
      rfl

theorem firstGeneration_coarse (depth : ℕ) (configuration : Conf (depth+2)) :
    firstGeneration depth (coarse (depth+1) configuration) =
      firstGeneration (depth+1) configuration := by
  simp only [firstGeneration, coarse_succ, conn_coarse]

theorem childConfiguration_coarse (depth : ℕ) (configuration : Conf (depth+2)) (edge : Fin 4) :
    childConfiguration depth (coarse (depth+1) configuration) edge =
      coarse depth (childConfiguration (depth+1) configuration edge) := by
  fin_cases edge <;> rfl

theorem orientedChild_coarse (depth : ℕ) (parent : Fin 4) (configuration : Conf (depth+2)) (edge : Fin 4) :
    orientedChild depth parent (coarse (depth+1) configuration) edge =
      coarse depth (orientedChild (depth+1) parent configuration edge) := by
  by_cases reversed : reverseGreen parent (conditionedOutcome parent (firstGeneration (depth+1) configuration)) edge=true
  · simp only [orientedChild, firstGeneration_coarse, childConfiguration_coarse, reversed,
      if_true, coarse_reverseConfiguration]
  · simp only [orientedChild, firstGeneration_coarse, childConfiguration_coarse, reversed]
    simp

/-- The actual extracted tree at the coarser level is exactly the truncation
of the finer extracted tree, pointwise and for every parent colour. -/
theorem truncateRuleTree_encode (depth : ℕ) (parent : Fin 4) (configuration : Conf (depth+1)) :
    truncateRuleTree depth (encode (depth+1) parent configuration) =
      encode depth parent (coarse depth configuration) := by
  induction depth generalizing parent with
  | zero => rfl
  | succ depth induction =>
      change (conditionedOutcome parent (firstGeneration (depth+1) configuration),
        fun edge => truncateRuleTree depth (encode (depth+1)
          (colour parent (conditionedOutcome parent (firstGeneration (depth+1) configuration)) edge)
          (orientedChild (depth+1) parent configuration edge))) =
        (conditionedOutcome parent (firstGeneration depth (coarse (depth+1) configuration)),
        fun edge => encode depth
          (colour parent (conditionedOutcome parent (firstGeneration depth (coarse (depth+1) configuration))) edge)
          (orientedChild depth parent (coarse (depth+1) configuration) edge))
      rw [firstGeneration_coarse]
      congr 1
      funext edge
      rw [induction, orientedChild_coarse]

theorem coarse_preimage_parentEvent (depth : ℕ) (parent : Fin 4) :
    (coarse depth) ⁻¹' parentEvent depth parent = parentEvent (depth+1) parent := by
  ext configuration
  simp only [Set.mem_preimage, parentEvent, Set.mem_setOf_eq, conn_coarse]

theorem parentMeasure_map_coarse (depth : ℕ) (parent : Fin 4) :
    (parentMeasure (depth+1) parent).map (coarse depth) = parentMeasure depth parent := by
  have mass : confMeasure Reduced.pc (depth+1) (parentEvent (depth+1) parent) =
      confMeasure Reduced.pc depth (parentEvent depth parent) := by
    rw [← coarse_preimage_parentEvent,
      ← Measure.map_apply (measurable_coarse depth) MeasurableSet.of_discrete,
      confMeasure_map_coarse]
  rw [parentMeasure, parentMeasure, ProbabilityTheory.cond, ProbabilityTheory.cond,
    Measure.map_smul, mass, ← coarse_preimage_parentEvent,
    ← Measure.restrict_map (measurable_coarse depth) MeasurableSet.of_discrete,
    confMeasure_map_coarse]

theorem encodedLaw_map_truncate (depth : ℕ) (parent : Fin 4) :
    (encodedLaw (depth+1) parent).map (truncateRuleTree depth) = encodedLaw depth parent := by
  have composition : truncateRuleTree depth ∘ encode (depth+1) parent =
      encode depth parent ∘ coarse depth := by
    funext configuration
    exact truncateRuleTree_encode depth parent configuration
  rw [encodedLaw, Measure.map_map Measurable.of_discrete Measurable.of_discrete,
    composition, ← Measure.map_map Measurable.of_discrete Measurable.of_discrete,
    parentMeasure_map_coarse]
  rfl

theorem ruleTreeLaw_map_truncate (depth : ℕ) (parent : Fin 4) :
    (ruleTreeLaw (depth+1) parent).map (truncateRuleTree depth) = ruleTreeLaw depth parent := by
  rw [← actual_encodedLaw_eq_ruleTreeLaw, encodedLaw_map_truncate, actual_encodedLaw_eq_ruleTreeLaw]

end Outlook.FourColourProjectiveConsistency

#print axioms Outlook.FourColourProjectiveConsistency.coarse_reverseConfiguration
#print axioms Outlook.FourColourProjectiveConsistency.truncateRuleTree_encode
#print axioms Outlook.FourColourProjectiveConsistency.parentMeasure_map_coarse
#print axioms Outlook.FourColourProjectiveConsistency.encodedLaw_map_truncate
#print axioms Outlook.FourColourProjectiveConsistency.ruleTreeLaw_map_truncate
