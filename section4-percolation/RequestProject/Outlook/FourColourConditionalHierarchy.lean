import RequestProject.Outlook.FourColourOrientationCandidate
import RequestProject.Outlook.FourColourTerminalAudit
import Mathlib.MeasureTheory.Measure.WithDensity

/-! All-depth conditional decomposition of the existing actual Bernoulli DHL
configurations. This is the probabilistic induction interface for the adopted
oriented coding, not a replacement cluster or an assumed graph-law identity. -/
namespace Outlook.FourColourConditionalHierarchy
open Cluster FourColourRuleAudit FourColourOrientationCandidate MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option maxHeartbeats 2000000

def firstGeneration (depth : ℕ) (configuration : Conf (depth+1)) : Conf 1 :=
  (conn depth configuration.1, conn depth configuration.2.1,
    conn depth configuration.2.2.1, conn depth configuration.2.2.2)

theorem firstGeneration_conn (depth : ℕ) (configuration : Conf (depth+1)) :
    conn 1 (firstGeneration depth configuration) = conn (depth+1) configuration := rfl

theorem conn_map_critical (depth : ℕ) :
    (confMeasure Reduced.pc depth).map (conn depth) = bern Reduced.pc := by
  induction depth with
  | zero =>
      change (bern Reduced.pc).map id = _
      exact Measure.map_id
  | succ depth induction =>
      have composition : conn (depth+1) = conn depth ∘ coarse depth := by
        funext configuration
        exact (conn_coarse depth configuration).symm
      rw [composition, ← Measure.map_map Measurable.of_discrete Measurable.of_discrete,
        confMeasure_map_coarse, induction]

theorem firstGeneration_map_critical (depth : ℕ) :
    (confMeasure Reduced.pc (depth+1)).map (firstGeneration depth) = confMeasure Reduced.pc 1 := by
  haveI := isProb_confMeasure Reduced.pc_pos.le Reduced.pc_lt_one.le depth
  have mapping : firstGeneration depth =
      Prod.map (conn depth) (Prod.map (conn depth) (Prod.map (conn depth) (conn depth))) := rfl
  rw [mapping]
  change ((confMeasure Reduced.pc depth).prod ((confMeasure Reduced.pc depth).prod
    ((confMeasure Reduced.pc depth).prod (confMeasure Reduced.pc depth)))).map _ = _
  rw [← Measure.map_prod_map _ _ Measurable.of_discrete Measurable.of_discrete,
    ← Measure.map_prod_map _ _ Measurable.of_discrete Measurable.of_discrete,
    ← Measure.map_prod_map _ _ Measurable.of_discrete Measurable.of_discrete]
  simp_rw [conn_map_critical]
  rfl

def parentEvent (depth : ℕ) (parent : Fin 4) : Set (Conf depth) :=
  {configuration | if parent=0 then conn depth configuration=true
    else if parent=3 then True else conn depth configuration=false}

noncomputable def parentMeasure (depth : ℕ) (parent : Fin 4) : Measure (Conf depth) :=
  ProbabilityTheory.cond (confMeasure Reduced.pc depth) (parentEvent depth parent)

theorem parentEvent_preimage (depth : ℕ) (parent : Fin 4) :
    parentEvent (depth+1) parent = firstGeneration depth ⁻¹' conditioningEvent parent := rfl

private theorem map_cond_preimage {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (measure : Measure α) (mapping : α → β) (measurable : Measurable mapping)
    (event : Set β) (eventMeasurable : MeasurableSet event) :
    (ProbabilityTheory.cond measure (mapping ⁻¹' event)).map mapping =
      ProbabilityTheory.cond (measure.map mapping) event := by
  ext target targetMeasurable
  rw [Measure.map_apply measurable targetMeasurable,
    ProbabilityTheory.cond_apply (measurable eventMeasurable),
    ProbabilityTheory.cond_apply eventMeasurable,
    Measure.map_apply measurable eventMeasurable,
    Measure.map_apply measurable (eventMeasurable.inter targetMeasurable)]
  rfl

theorem firstGeneration_parentMeasure (depth : ℕ) (parent : Fin 4) :
    (parentMeasure (depth+1) parent).map (firstGeneration depth) =
      ProbabilityTheory.cond (confMeasure Reduced.pc 1) (conditioningEvent parent) := by
  rw [parentMeasure, parentEvent_preimage, map_cond_preimage _ _ Measurable.of_discrete
    _ MeasurableSet.of_discrete, firstGeneration_map_critical]

theorem actual_outcome_probability_all_depths (depth : ℕ) (parent : Fin 4) (outcome : Fin 9) :
    (parentMeasure (depth+1) parent).real
      {configuration | conditionedOutcome parent (firstGeneration depth configuration)=outcome} =
      criticalWeights parent outcome := by
  have result := critical_conditional_figure_probabilities parent outcome
  rw [← firstGeneration_parentMeasure depth parent, measureReal_def,
    Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete] at result
  exact result

theorem actual_oriented_states_all_depths (depth : ℕ) (parent : Fin 4) :
    ∀ᵐ configuration ∂parentMeasure (depth+1) parent,
      derivedColour parent (firstGeneration depth configuration) =
          colour parent (conditionedOutcome parent (firstGeneration depth configuration)) ∧
      derivedReverse parent (firstGeneration depth configuration) =
          reverseGreen parent (conditionedOutcome parent (firstGeneration depth configuration)) := by
  unfold parentMeasure
  apply ae_cond_of_forall_mem MeasurableSet.of_discrete
  intro configuration condition
  exact all_conditional_configuration_states parent (firstGeneration depth configuration) condition

def connectivityEvent (depth : ℕ) (connected : Bool) : Set (Conf depth) :=
  {configuration | conn depth configuration=connected}

noncomputable def connectivityMeasure (depth : ℕ) (connected : Bool) : Measure (Conf depth) :=
  ProbabilityTheory.cond (confMeasure Reduced.pc depth) (connectivityEvent depth connected)

private theorem cond_product {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (first : Measure α) (second : Measure β) [IsFiniteMeasure first] [IsFiniteMeasure second]
    (firstEvent : Set α) (secondEvent : Set β) :
    ProbabilityTheory.cond (first.prod second) (firstEvent ×ˢ secondEvent) =
      (ProbabilityTheory.cond first firstEvent).prod
        (ProbabilityTheory.cond second secondEvent) := by
  simp only [ProbabilityTheory.cond, Measure.prod_prod,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.prod_restrict]
  rw [ENNReal.mul_inv (Or.inr (measure_ne_top second secondEvent))
    (Or.inl (measure_ne_top first firstEvent)), mul_comm]

/-- Given all four coarse connectivity bits, the four actual child
configurations are independent with their corresponding conditional laws. -/
theorem actual_child_conditional_independence (depth : ℕ) (coarseConfiguration : Conf 1) :
    ProbabilityTheory.cond (confMeasure Reduced.pc (depth+1))
      {configuration | firstGeneration depth configuration=coarseConfiguration} =
    (connectivityMeasure depth coarseConfiguration.1).prod
      ((connectivityMeasure depth coarseConfiguration.2.1).prod
        ((connectivityMeasure depth coarseConfiguration.2.2.1).prod
          (connectivityMeasure depth coarseConfiguration.2.2.2))) := by
  haveI := isProb_confMeasure Reduced.pc_pos.le Reduced.pc_lt_one.le depth
  have event : {configuration | firstGeneration depth configuration=coarseConfiguration} =
      connectivityEvent depth coarseConfiguration.1 ×ˢ
      (connectivityEvent depth coarseConfiguration.2.1 ×ˢ
      (connectivityEvent depth coarseConfiguration.2.2.1 ×ˢ
        connectivityEvent depth coarseConfiguration.2.2.2)) := by
    ext configuration
    change (conn depth configuration.1, conn depth configuration.2.1,
      conn depth configuration.2.2.1, conn depth configuration.2.2.2) =
      (coarseConfiguration.1, coarseConfiguration.2.1, coarseConfiguration.2.2.1,
        coarseConfiguration.2.2.2) ↔
      (conn depth configuration.1 = coarseConfiguration.1 ∧
        conn depth configuration.2.1 = coarseConfiguration.2.1 ∧
        conn depth configuration.2.2.1 = coarseConfiguration.2.2.1 ∧
        conn depth configuration.2.2.2 = coarseConfiguration.2.2.2)
    simp only [Prod.mk.injEq]
  rw [event]
  change ProbabilityTheory.cond ((confMeasure Reduced.pc depth).prod
    ((confMeasure Reduced.pc depth).prod ((confMeasure Reduced.pc depth).prod
    (confMeasure Reduced.pc depth)))) _ = _
  rw [cond_product, cond_product, cond_product]
  rfl

end Outlook.FourColourConditionalHierarchy

#print axioms Outlook.FourColourConditionalHierarchy.conn_map_critical
#print axioms Outlook.FourColourConditionalHierarchy.firstGeneration_map_critical
#print axioms Outlook.FourColourConditionalHierarchy.firstGeneration_parentMeasure
#print axioms Outlook.FourColourConditionalHierarchy.actual_outcome_probability_all_depths
#print axioms Outlook.FourColourConditionalHierarchy.actual_oriented_states_all_depths
#print axioms Outlook.FourColourConditionalHierarchy.actual_child_conditional_independence
