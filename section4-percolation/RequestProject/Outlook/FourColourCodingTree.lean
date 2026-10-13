import RequestProject.Outlook.FourColourConditionalHierarchy

/-! The actual all-depth extraction map from Bernoulli configurations to the
adopted oriented rule tree. Its recursive conditional states are proved valid;
the graph-law identification and the rule-tree measure identity are separate. -/
namespace Outlook.FourColourCodingTree
open Cluster FourColourRuleAudit FourColourOrientationCandidate FourColourConditionalHierarchy
open MeasureTheory ProbabilityTheory
set_option maxHeartbeats 2000000
local instance : DecidableEq (Conf 0) := inferInstanceAs (DecidableEq Bool)

theorem parentMeasure_reverse_singleton (depth : ℕ) (parent : Fin 4)
    (configuration : Conf depth) :
    parentMeasure depth parent {reverseConfiguration depth configuration} =
      parentMeasure depth parent {configuration} := by
  classical
  have intersection (value : Conf depth) : parentEvent depth parent ∩ {value} =
      if value ∈ parentEvent depth parent then {value} else ∅ := by
    by_cases membership : value ∈ parentEvent depth parent
    · simp [membership]
    · simp [membership]
  have reversed : reverseConfiguration depth configuration ∈ parentEvent depth parent ↔
      configuration ∈ parentEvent depth parent := by
    simp only [parentEvent, Set.mem_setOf_eq, conn_reverseConfiguration]
  rw [parentMeasure, ProbabilityTheory.cond_apply MeasurableSet.of_discrete,
    ProbabilityTheory.cond_apply MeasurableSet.of_discrete, intersection, intersection]
  simp only [reversed]
  split_ifs
  · rw [confMeasure_reverse_singleton _ Reduced.pc_pos.le Reduced.pc_lt_one.le]
  · rfl

/-- Reorienting a real conditioned child leaves its full configuration law
unchanged; this is not merely equality of endpoint moments. -/
theorem parentMeasure_map_reverse (depth : ℕ) (parent : Fin 4) :
    (parentMeasure depth parent).map (reverseConfiguration depth) = parentMeasure depth parent := by
  apply Measure.ext_of_singleton
  intro configuration
  have preimage : reverseConfiguration depth ⁻¹' {configuration} =
      {reverseConfiguration depth configuration} := by
    ext candidate
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro equal
      rw [← equal, reverseConfiguration_involutive depth candidate]
    · rintro rfl
      exact reverseConfiguration_involutive depth configuration
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
    preimage, parentMeasure_reverse_singleton]

def childConfiguration (depth : ℕ) (configuration : Conf (depth+1)) : Fin 4 → Conf depth :=
  ![configuration.1, configuration.2.1, configuration.2.2.1, configuration.2.2.2]

theorem childConfiguration_conn (depth : ℕ) (configuration : Conf (depth+1)) (edge : Fin 4) :
    conn depth (childConfiguration depth configuration edge) =
      openCell (firstGeneration depth configuration) edge := by
  fin_cases edge <;> rfl

def orientedChild (depth : ℕ) (parent : Fin 4) (configuration : Conf (depth+1))
    (edge : Fin 4) : Conf depth :=
  if reverseGreen parent (conditionedOutcome parent (firstGeneration depth configuration)) edge
  then reverseConfiguration depth (childConfiguration depth configuration edge)
  else childConfiguration depth configuration edge

private theorem local_child_condition (parent : Fin 4) (configuration : Conf 1)
    (condition : configuration ∈ conditioningEvent parent) (edge : Fin 4) :
    (openCell configuration edge : Conf 0) ∈
      parentEvent 0 (colour parent (conditionedOutcome parent configuration) edge) := by
  revert condition
  simp only [conditioningEvent, parentEvent, Set.mem_setOf_eq]
  rcases configuration with ⟨first, second, third, fourth⟩
  fin_cases parent <;> cases first <;> cases second <;> cases third <;> cases fourth <;>
    fin_cases edge <;> decide

/-- Every actual recursively selected child satisfies its actual colour's
conditioning event, including the mirrored green children. -/
theorem orientedChild_condition (depth : ℕ) (parent : Fin 4)
    (configuration : Conf (depth+1)) (condition : configuration ∈ parentEvent (depth+1) parent)
    (edge : Fin 4) :
    orientedChild depth parent configuration edge ∈ parentEvent depth
      (colour parent (conditionedOutcome parent (firstGeneration depth configuration)) edge) := by
  have localCondition := local_child_condition parent (firstGeneration depth configuration) condition edge
  change (if _=0 then _=true else if _=3 then True else _=false) at localCondition ⊢
  have connectivity : conn depth (orientedChild depth parent configuration edge) =
      openCell (firstGeneration depth configuration) edge := by
    unfold orientedChild
    split <;> simp only [conn_reverseConfiguration, childConfiguration_conn]
  rw [connectivity]
  exact localCondition

def RuleTree : ℕ → Type
  | 0 => Unit
  | depth+1 => Fin 9 × (Fin 4 → RuleTree depth)

instance treeFintype : (depth : ℕ) → Fintype (RuleTree depth)
  | 0 => inferInstanceAs (Fintype Unit)
  | depth+1 => by
      haveI := treeFintype depth
      exact inferInstanceAs (Fintype (Fin 9 × (Fin 4 → RuleTree depth)))

instance (depth : ℕ) : MeasurableSpace (RuleTree depth) := ⊤
instance (depth : ℕ) : DiscreteMeasurableSpace (RuleTree depth) := ⟨fun _ => trivial⟩

/-- Read the actual configuration in each cell's adopted orientation. -/
def encode : (depth : ℕ) → Fin 4 → Conf depth → RuleTree depth
  | 0, _, _ => ()
  | depth+1, parent, configuration =>
      (conditionedOutcome parent (firstGeneration depth configuration), fun edge =>
        encode depth (colour parent (conditionedOutcome parent (firstGeneration depth configuration)) edge)
          (orientedChild depth parent configuration edge))

/-- The cemetery records no retained edge, regardless of the hidden bonds. -/
def cemeteryTree : (depth : ℕ) → RuleTree depth
  | 0 => ()
  | depth+1 => (0, fun _ => cemeteryTree depth)

private theorem colour_black (edge : Fin 4) : colour 3 0 edge = 3 := by
  fin_cases edge <;> rfl

theorem encode_black (depth : ℕ) (configuration : Conf depth) :
    encode depth 3 configuration = cemeteryTree depth := by
  induction depth with
  | zero => rfl
  | succ depth induction =>
      change (0, fun edge => encode depth (colour 3 0 edge)
        (orientedChild depth 3 configuration edge)) = (0, fun _ => cemeteryTree depth)
      congr 1
      funext edge
      rw [colour_black, induction]

noncomputable def encodedLaw (depth : ℕ) (parent : Fin 4) : Measure (RuleTree depth) :=
  (parentMeasure depth parent).map (encode depth parent)

theorem encodedLaw_reversed_input (depth : ℕ) (parent : Fin 4) :
    (parentMeasure depth parent).map
      (fun configuration => encode depth parent (reverseConfiguration depth configuration)) =
      encodedLaw depth parent := by
  rw [show (fun configuration => encode depth parent (reverseConfiguration depth configuration)) =
    encode depth parent ∘ reverseConfiguration depth by rfl,
    ← Measure.map_map Measurable.of_discrete Measurable.of_discrete,
    parentMeasure_map_reverse]
  rfl

def AllowedTree : (depth : ℕ) → Fin 4 → RuleTree depth → Prop
  | 0, _, _ => True
  | depth+1, parent, tree =>
      (if parent=0 then tree.1<7 else if parent=2 then tree.1<4 else if parent=3 then tree.1=0 else True) ∧
      ∀ edge, AllowedTree depth (colour parent tree.1 edge) (tree.2 edge)

private theorem local_outcome_allowed (parent : Fin 4) (configuration : Conf 1) :
    if parent=0 then conditionedOutcome parent configuration<7
    else if parent=2 then conditionedOutcome parent configuration<4
    else if parent=3 then conditionedOutcome parent configuration=0 else True := by
  rcases configuration with ⟨first, second, third, fourth⟩
  fin_cases parent <;> cases first <;> cases second <;> cases third <;> cases fourth <;> decide

theorem actual_encode_allowed (depth : ℕ) (parent : Fin 4) (configuration : Conf depth)
    (condition : configuration ∈ parentEvent depth parent) :
    AllowedTree depth parent (encode depth parent configuration) := by
  induction depth generalizing parent with
  | zero => trivial
  | succ depth induction =>
      constructor
      · exact local_outcome_allowed parent (firstGeneration depth configuration)
      · intro edge
        exact induction _ _ (orientedChild_condition depth parent configuration condition edge)

theorem actual_encode_allowed_ae (depth : ℕ) (parent : Fin 4) :
    ∀ᵐ configuration ∂parentMeasure depth parent,
      AllowedTree depth parent (encode depth parent configuration) := by
  exact ae_cond_of_forall_mem MeasurableSet.of_discrete
    (fun configuration condition => actual_encode_allowed depth parent configuration condition)

end Outlook.FourColourCodingTree

#print axioms Outlook.FourColourCodingTree.childConfiguration_conn
#print axioms Outlook.FourColourCodingTree.parentMeasure_map_reverse
#print axioms Outlook.FourColourCodingTree.orientedChild_condition
#print axioms Outlook.FourColourCodingTree.actual_encode_allowed
#print axioms Outlook.FourColourCodingTree.actual_encode_allowed_ae
#print axioms Outlook.FourColourCodingTree.encode_black
#print axioms Outlook.FourColourCodingTree.encodedLaw_reversed_input
