import RequestProject.Outlook.FourColourCodingTree

/-! Conditional laws of actual child encodings. Black children discard their
hidden configurations; every live child retains its actual conditional law. -/
namespace Outlook.FourColourChildCodingLaw
open Cluster FourColourRuleAudit FourColourOrientationCandidate FourColourConditionalHierarchy
open FourColourCodingTree MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option maxHeartbeats 2000000

theorem connectivityEvent_mass (depth : ℕ) (connected : Bool) :
    confMeasure Reduced.pc depth (connectivityEvent depth connected) =
      ENNReal.ofReal (if connected then Reduced.pc else 1-Reduced.pc) := by
  have mapping := congrArg (fun measure : Measure Bool => measure {connected})
    (conn_map_critical depth)
  dsimp only at mapping
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete] at mapping
  change confMeasure Reduced.pc depth (connectivityEvent depth connected) = _ at mapping
  rw [mapping]
  cases connected <;> simp [bern]

instance connectivityMeasure_probability (depth : ℕ) (connected : Bool) :
    IsProbabilityMeasure (connectivityMeasure depth connected) := by
  haveI := isProb_confMeasure Reduced.pc_pos.le Reduced.pc_lt_one.le depth
  apply cond_isProbabilityMeasure
  rw [connectivityEvent_mass]
  cases connected <;> simp [ENNReal.ofReal_eq_zero, Reduced.pc_pos.not_ge,
    (sub_pos.mpr Reduced.pc_lt_one).not_ge]

instance parentMeasure_probability (depth : ℕ) (parent : Fin 4) :
    IsProbabilityMeasure (parentMeasure depth parent) := by
  haveI := isProb_confMeasure Reduced.pc_pos.le Reduced.pc_lt_one.le depth
  fin_cases parent
  · exact connectivityMeasure_probability depth true
  · exact connectivityMeasure_probability depth false
  · exact connectivityMeasure_probability depth false
  · have event : parentEvent depth 3 = Set.univ := by
      ext configuration
      simp [parentEvent]
    change IsProbabilityMeasure (ProbabilityTheory.cond (confMeasure Reduced.pc depth)
      (parentEvent depth 3))
    rw [event, cond_univ]
    infer_instance

instance encodedLaw_probability (depth : ℕ) (parent : Fin 4) :
    IsProbabilityMeasure (encodedLaw depth parent) := by
  unfold encodedLaw
  exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable

theorem encodedLaw_black (depth : ℕ) :
    encodedLaw depth 3 = Measure.dirac (cemeteryTree depth) := by
  have constant : encode depth 3 = fun _ => cemeteryTree depth := funext (encode_black depth)
  simp [encodedLaw, constant]

theorem black_encoding_under_connectivity (depth : ℕ) (connected : Bool) :
    (connectivityMeasure depth connected).map (encode depth 3) = encodedLaw depth 3 := by
  rw [encodedLaw_black]
  have constant : encode depth 3 = fun _ => cemeteryTree depth := funext (encode_black depth)
  simp [constant]

private theorem live_child_bit (parent : Fin 4) (configuration : Conf 1)
    (condition : configuration ∈ conditioningEvent parent) (edge : Fin 4)
    (live : colour parent (conditionedOutcome parent configuration) edge ≠ 3) :
    (if colour parent (conditionedOutcome parent configuration) edge = 0 then true else false) =
      openCell configuration edge := by
  revert condition live
  simp only [conditioningEvent, Set.mem_setOf_eq]
  rcases configuration with ⟨first, second, third, fourth⟩
  fin_cases parent <;> cases first <;> cases second <;> cases third <;> cases fourth <;>
    fin_cases edge <;> decide

private theorem live_parentMeasure (depth : ℕ) (parent : Fin 4) (live : parent ≠ 3) :
    parentMeasure depth parent = connectivityMeasure depth (if parent=0 then true else false) := by
  fin_cases parent <;> first | rfl | contradiction

def childEncoding (depth : ℕ) (parent : Fin 4) (coarseConfiguration : Conf 1)
    (edge : Fin 4) (configuration : Conf depth) : RuleTree depth :=
  encode depth (colour parent (conditionedOutcome parent coarseConfiguration) edge)
    (if reverseGreen parent (conditionedOutcome parent coarseConfiguration) edge
     then reverseConfiguration depth configuration else configuration)

/-- This conditional child law is computed from the actual connectivity event.
The inactive black case is proved by constancy, without asserting that its
unobserved bond configurations have an unconditional distribution. -/
theorem actual_child_encoding_law (depth : ℕ) (parent : Fin 4) (coarseConfiguration : Conf 1)
    (condition : coarseConfiguration ∈ conditioningEvent parent) (edge : Fin 4) :
    (connectivityMeasure depth (openCell coarseConfiguration edge)).map
      (childEncoding depth parent coarseConfiguration edge) =
      encodedLaw depth (colour parent (conditionedOutcome parent coarseConfiguration) edge) := by
  by_cases black : colour parent (conditionedOutcome parent coarseConfiguration) edge = 3
  · have constant : childEncoding depth parent coarseConfiguration edge =
        fun _ => cemeteryTree depth := by
      funext configuration
      unfold childEncoding
      rw [black, encode_black]
    rw [constant, black, encodedLaw_black]
    simp
  · have measures : connectivityMeasure depth (openCell coarseConfiguration edge) =
        parentMeasure depth (colour parent (conditionedOutcome parent coarseConfiguration) edge) := by
      rw [live_parentMeasure _ _ black, live_child_bit parent coarseConfiguration condition edge black]
    rw [measures]
    change (parentMeasure depth (colour parent (conditionedOutcome parent coarseConfiguration) edge)).map
      (fun configuration =>
        encode depth (colour parent (conditionedOutcome parent coarseConfiguration) edge)
          (if reverseGreen parent (conditionedOutcome parent coarseConfiguration) edge
           then reverseConfiguration depth configuration else configuration)) = _
    by_cases reversed : reverseGreen parent (conditionedOutcome parent coarseConfiguration) edge
    · simp only [reversed, if_true]
      exact encodedLaw_reversed_input depth _
    · simp only [reversed, if_false]
      rfl

theorem actual_four_child_encoding_law (depth : ℕ) (parent : Fin 4)
    (coarseConfiguration : Conf 1) (condition : coarseConfiguration ∈ conditioningEvent parent) :
    (ProbabilityTheory.cond (confMeasure Reduced.pc (depth+1))
      {configuration | firstGeneration depth configuration=coarseConfiguration}).map
      (fun configuration =>
        (childEncoding depth parent coarseConfiguration 0 configuration.1,
          childEncoding depth parent coarseConfiguration 1 configuration.2.1,
          childEncoding depth parent coarseConfiguration 2 configuration.2.2.1,
          childEncoding depth parent coarseConfiguration 3 configuration.2.2.2)) =
      (encodedLaw depth (colour parent (conditionedOutcome parent coarseConfiguration) 0)).prod
        ((encodedLaw depth (colour parent (conditionedOutcome parent coarseConfiguration) 1)).prod
          ((encodedLaw depth (colour parent (conditionedOutcome parent coarseConfiguration) 2)).prod
            (encodedLaw depth (colour parent (conditionedOutcome parent coarseConfiguration) 3)))) := by
  rw [actual_child_conditional_independence]
  change ((connectivityMeasure depth coarseConfiguration.1).prod
    ((connectivityMeasure depth coarseConfiguration.2.1).prod
      ((connectivityMeasure depth coarseConfiguration.2.2.1).prod
        (connectivityMeasure depth coarseConfiguration.2.2.2)))).map
    (Prod.map (childEncoding depth parent coarseConfiguration 0)
      (Prod.map (childEncoding depth parent coarseConfiguration 1)
        (Prod.map (childEncoding depth parent coarseConfiguration 2)
          (childEncoding depth parent coarseConfiguration 3)))) = _
  rw [← Measure.map_prod_map _ _ Measurable.of_discrete Measurable.of_discrete,
    ← Measure.map_prod_map _ _ Measurable.of_discrete Measurable.of_discrete,
    ← Measure.map_prod_map _ _ Measurable.of_discrete Measurable.of_discrete]
  have first := actual_child_encoding_law depth parent coarseConfiguration condition 0
  have second := actual_child_encoding_law depth parent coarseConfiguration condition 1
  have third := actual_child_encoding_law depth parent coarseConfiguration condition 2
  have fourth := actual_child_encoding_law depth parent coarseConfiguration condition 3
  change (connectivityMeasure depth coarseConfiguration.1).map _ = _ at first
  change (connectivityMeasure depth coarseConfiguration.2.1).map _ = _ at second
  change (connectivityMeasure depth coarseConfiguration.2.2.1).map _ = _ at third
  change (connectivityMeasure depth coarseConfiguration.2.2.2).map _ = _ at fourth
  rw [first, second, third, fourth]

end Outlook.FourColourChildCodingLaw

#print axioms Outlook.FourColourChildCodingLaw.connectivityEvent_mass
#print axioms Outlook.FourColourChildCodingLaw.connectivityMeasure_probability
#print axioms Outlook.FourColourChildCodingLaw.parentMeasure_probability
#print axioms Outlook.FourColourChildCodingLaw.encodedLaw_black
#print axioms Outlook.FourColourChildCodingLaw.black_encoding_under_connectivity
#print axioms Outlook.FourColourChildCodingLaw.actual_child_encoding_law
#print axioms Outlook.FourColourChildCodingLaw.actual_four_child_encoding_law
