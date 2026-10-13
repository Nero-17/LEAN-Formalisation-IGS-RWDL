import RequestProject.Outlook.FourColourProjectiveConsistency
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-! Full joint-law identification for the actual compatible critical cluster.
The finite branching laws determine a unique compatible process; successive
depths are not assumed independent. -/
namespace Outlook.FourColourInfiniteProcess
open Cluster MeasureTheory ProbabilityTheory Finset Preorder
open FourColourConditionalHierarchy FourColourCodingTree FourColourBranchingLaw
open FourColourProjectiveConsistency

noncomputable section

instance ruleTree_nonempty (depth : ℕ) : Nonempty (RuleTree depth) :=
  ⟨cemeteryTree depth⟩

instance ruleTreeLaw_probability (depth : ℕ) (parent : Fin 4) :
    IsProbabilityMeasure (ruleTreeLaw depth parent) := by
  rw [← actual_encodedLaw_eq_ruleTreeLaw]
  infer_instance

/-- Conditional refinement of the independently specified finite branching laws. -/
def ruleTreePathMeasure (parent : Fin 4) : Measure ((depth : ℕ) → RuleTree depth) :=
  InverseSystem.pathMeasure (fun depth => ruleTreeLaw depth parent) truncateRuleTree

instance ruleTreePathMeasure_probability (parent : Fin 4) :
    IsProbabilityMeasure (ruleTreePathMeasure parent) := by
  unfold ruleTreePathMeasure
  infer_instance

theorem ruleTreePathMeasure_map_eval (parent : Fin 4) (depth : ℕ) :
    (ruleTreePathMeasure parent).map (fun path => path depth) = ruleTreeLaw depth parent :=
  InverseSystem.pathMeasure_map_eval _ _ (fun _ => Measurable.of_discrete)
    (fun depth => ruleTreeLaw_map_truncate depth parent) depth

theorem ruleTreePathMeasure_bonded (parent : Fin 4) :
    ∀ᵐ path ∂ruleTreePathMeasure parent, ∀ depth,
      truncateRuleTree depth (path (depth+1)) = path depth :=
  InverseSystem.pathMeasure_all_bonded _ _ (fun _ => Measurable.of_discrete)
    (fun depth => ruleTreeLaw_map_truncate depth parent)

def CompatibleRuleTree := InverseSystem.compatiblePaths truncateRuleTree

instance : MeasurableSpace CompatibleRuleTree :=
  inferInstanceAs (MeasurableSpace (InverseSystem.compatiblePaths truncateRuleTree))

def compatibleRuleTreeMeasure (parent : Fin 4) : Measure CompatibleRuleTree :=
  InverseSystem.compatibleMeasure (fun depth => ruleTreeLaw depth parent) truncateRuleTree

theorem compatibleRuleTreeMeasure_map_val (parent : Fin 4) :
    (compatibleRuleTreeMeasure parent).map Subtype.val = ruleTreePathMeasure parent :=
  InverseSystem.compatibleMeasure_map_val _ _ (fun _ => Measurable.of_discrete)
    (fun depth => ruleTreeLaw_map_truncate depth parent)

/-- Recover any earlier level by genuine iterated tree truncation. -/
def restrictTree : (upper : ℕ) → RuleTree upper →
    (lower : ℕ) → lower ≤ upper → RuleTree lower
  | 0, tree, lower, bound => by
      have equality : lower=0 := Nat.eq_zero_of_le_zero bound
      subst lower
      exact tree
  | upper+1, tree, lower, bound =>
      if equality : lower=upper+1 then equality.symm ▸ tree
      else restrictTree upper (truncateRuleTree upper tree) lower (by omega)

theorem restrictTree_of_bonded (path : (depth : ℕ) → RuleTree depth)
    (bonded : ∀ depth, truncateRuleTree depth (path (depth+1)) = path depth)
    (upper lower : ℕ) (bound : lower ≤ upper) :
    restrictTree upper (path upper) lower bound = path lower := by
  induction upper with
  | zero =>
      have equality : lower=0 := Nat.eq_zero_of_le_zero bound
      subst lower
      rfl
  | succ upper induction =>
      rw [restrictTree]
      split_ifs with equality
      · subst lower
        rfl
      · rw [bonded upper]
        exact induction (by omega)

def treePrefix (depth : ℕ) (tree : RuleTree depth) :
    (index : Iic depth) → RuleTree index :=
  fun index => restrictTree depth tree index (mem_Iic.mp index.property)

theorem prefix_of_bonded (path : (depth : ℕ) → RuleTree depth)
    (bonded : ∀ depth, truncateRuleTree depth (path (depth+1)) = path depth)
    (depth : ℕ) : frestrictLe depth path = treePrefix depth (path depth) := by
  funext index
  exact (restrictTree_of_bonded path bonded depth index (mem_Iic.mp index.property)).symm

/-- The complete prefix is the image of the highest-level law, not a product of marginals. -/
theorem ruleTreePathMeasure_prefix (parent : Fin 4) (depth : ℕ) :
    (ruleTreePathMeasure parent).map (frestrictLe depth) =
      (ruleTreeLaw depth parent).map (treePrefix depth) := by
  calc
    _ = (ruleTreePathMeasure parent).map
        (treePrefix depth ∘ fun path => path depth) := by
      apply Measure.map_congr
      filter_upwards [ruleTreePathMeasure_bonded parent] with path bonded
      exact prefix_of_bonded path bonded depth
    _ = _ := by
      rw [← Measure.map_map Measurable.of_discrete (measurable_pi_apply depth),
        ruleTreePathMeasure_map_eval]

/-- The original nested configuration, encoded at every level. -/
def nestedEncodedSequence (cluster : NestedCluster) (depth : ℕ) : RuleTree depth :=
  encode depth 0 (nestedConfiguration depth cluster)

theorem measurable_nestedEncodedSequence : Measurable nestedEncodedSequence :=
  measurable_pi_lambda _ (fun depth =>
    Measurable.of_discrete.comp (measurable_nestedConfiguration depth))

theorem nestedEncodedSequence_bonded (cluster : NestedCluster) (depth : ℕ) :
    truncateRuleTree depth (nestedEncodedSequence cluster (depth+1)) =
      nestedEncodedSequence cluster depth := by
  rw [nestedEncodedSequence, truncateRuleTree_encode, nestedConfiguration_bonded]
  rfl

theorem connectedMeasure_eq_parentMeasure (depth : ℕ) :
    connectedMeasure depth = parentMeasure depth 0 := by
  rfl

theorem nestedEncodedSequence_eval_law (depth : ℕ) :
    nestedClusterMeasure.map (fun cluster => nestedEncodedSequence cluster depth) =
      ruleTreeLaw depth 0 := by
  change nestedClusterMeasure.map (encode depth 0 ∘ nestedConfiguration depth) = _
  rw [← Measure.map_map Measurable.of_discrete (measurable_nestedConfiguration depth),
    nestedConfiguration_law, connectedMeasure_eq_parentMeasure]
  exact actual_encodedLaw_eq_ruleTreeLaw depth 0

/-- All joint cylinders up to this depth are identified simultaneously. -/
theorem nestedEncodedSequence_prefix_law (depth : ℕ) :
    nestedClusterMeasure.map (fun cluster => frestrictLe depth (nestedEncodedSequence cluster)) =
      (ruleTreeLaw depth 0).map (treePrefix depth) := by
  have equality : (fun cluster => frestrictLe depth (nestedEncodedSequence cluster)) =
      treePrefix depth ∘ (fun cluster => nestedEncodedSequence cluster depth) := by
    funext cluster
    exact prefix_of_bonded _ (nestedEncodedSequence_bonded cluster) depth
  have measurable_level : Measurable (fun cluster => nestedEncodedSequence cluster depth) :=
    (measurable_pi_apply depth).comp measurable_nestedEncodedSequence
  rw [equality, ← Measure.map_map
    (Measurable.of_discrete : Measurable (treePrefix depth)) measurable_level,
    nestedEncodedSequence_eval_law]

/-- Dependent-coordinate version of the original FullProcessLaw uniqueness argument. -/
private theorem measure_eq_of_prefixes {X : ℕ → Type*} [∀ depth, MeasurableSpace (X depth)]
    (first_measure second_measure : Measure ((depth : ℕ) → X depth))
    [IsFiniteMeasure second_measure]
    (prefix_laws : ∀ depth, first_measure.map (frestrictLe depth) =
      second_measure.map (frestrictLe depth)) : first_measure = second_measure := by
  let family : (indices : Finset ℕ) → Measure ((index : indices) → X index) :=
    fun indices => second_measure.map indices.restrict
  have projective_family : IsProjectiveMeasureFamily family :=
    isProjectiveMeasureFamily_map_restrict
      (P := second_measure) (X := fun depth trajectory => trajectory depth)
      (fun depth => (measurable_pi_apply depth).aemeasurable)
  haveI : ∀ indices, IsFiniteMeasure (family indices) := fun indices => by
    dsimp [family]
    infer_instance
  have first_projective : IsProjectiveLimit first_measure family := by
    apply (isProjectiveLimit_nat_iff projective_family first_measure).mpr
    exact prefix_laws
  have second_projective : IsProjectiveLimit second_measure family := fun _ => rfl
  exact first_projective.unique second_projective

/-- Equality of the full dependent product-space laws of the coupled tree sequence. -/
theorem nested_encoded_full_process_law :
    nestedClusterMeasure.map nestedEncodedSequence = ruleTreePathMeasure 0 := by
  apply measure_eq_of_prefixes
  intro depth
  rw [Measure.map_map (measurable_frestrictLe depth) measurable_nestedEncodedSequence]
  exact (nestedEncodedSequence_prefix_law depth).trans (ruleTreePathMeasure_prefix 0 depth).symm

/-- Arbitrary finite sets of depths, including nonconsecutive joint observations. -/
theorem nested_encoded_finite_joint_law (indices : Finset ℕ) :
    nestedClusterMeasure.map (fun cluster => indices.restrict (nestedEncodedSequence cluster)) =
      (ruleTreePathMeasure 0).map indices.restrict := by
  have measurable_restriction : Measurable
      (indices.restrict : ((depth : ℕ) → RuleTree depth) → ((index : indices) → RuleTree index)) :=
    measurable_pi_lambda _ (fun index => measurable_pi_apply index.val)
  rw [← nested_encoded_full_process_law,
    Measure.map_map measurable_restriction measurable_nestedEncodedSequence]
  rfl

/-- The same full law is carried by the independently constructed inverse limit. -/
theorem nested_encoded_compatible_process_law :
    nestedClusterMeasure.map nestedEncodedSequence =
      (compatibleRuleTreeMeasure 0).map Subtype.val := by
  rw [compatibleRuleTreeMeasure_map_val, nested_encoded_full_process_law]

/-- Full law also on the original all-sequences realization of the critical process. -/
theorem infinite_cluster_encoded_full_process_law :
    infiniteClusterMeasure.map (fun path depth => encode depth 0 (path depth)) =
      ruleTreePathMeasure 0 := by
  have inclusion : nestedClusterMeasure.map Subtype.val = infiniteClusterMeasure :=
    InverseSystem.compatibleMeasure_map_val connectedMeasure coarse measurable_coarse
      connectedMeasure_map_coarse
  have measurable_encoding : Measurable
      (fun (path : (depth : ℕ) → Conf depth) depth => encode depth 0 (path depth)) :=
    measurable_pi_lambda _ (fun depth =>
      (Measurable.of_discrete : Measurable (encode depth 0)).comp (measurable_pi_apply depth))
  rw [← inclusion, Measure.map_map measurable_encoding measurable_subtype_coe]
  exact nested_encoded_full_process_law

end
end Outlook.FourColourInfiniteProcess

#print axioms Outlook.FourColourInfiniteProcess.ruleTreePathMeasure_bonded
#print axioms Outlook.FourColourInfiniteProcess.ruleTreePathMeasure_prefix
#print axioms Outlook.FourColourInfiniteProcess.nestedEncodedSequence_prefix_law
#print axioms Outlook.FourColourInfiniteProcess.nested_encoded_full_process_law
#print axioms Outlook.FourColourInfiniteProcess.nested_encoded_finite_joint_law
#print axioms Outlook.FourColourInfiniteProcess.nested_encoded_compatible_process_law
#print axioms Outlook.FourColourInfiniteProcess.infinite_cluster_encoded_full_process_law
