import RequestProject.Outlook.FourColourConditionalRules
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting

/-! Independent, unadopted correction candidate. Green means precisely one
active endpoint and its arrow points from that endpoint to the inactive one.
Nothing in the already adopted figure, matrix, or manuscript is modified. -/
namespace Outlook.FourColourOrientationCandidate
open Cluster FourColourRuleAudit MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
local instance : DecidableEq (Conf 0) := inferInstanceAs (DecidableEq Bool)

def openCell (configuration : Conf 1) : Fin 4 → Bool :=
  ![configuration.1, configuration.2.1, configuration.2.2.1, configuration.2.2.2]

/-- The actual four undirected Bernoulli bonds of the one-step diamond. -/
def openDiamond (configuration : Conf 1) : SimpleGraph (Fin 4) where
  Adj first second := ∃ edge, openCell configuration edge=true ∧
    ((source edge=first ∧ target edge=second) ∨ (source edge=second ∧ target edge=first))
  symm := by
    intro first second ⟨edge, opened, incidence⟩
    exact ⟨edge, opened, incidence.elim Or.inr Or.inl⟩
  loopless := by
    constructor
    intro vertex ⟨edge, _, incidence⟩
    have distinct : source edge ≠ target edge := by fin_cases edge <;> decide
    rcases incidence with ⟨left, right⟩ | ⟨left, right⟩
    · exact distinct (left.trans right.symm)
    · exact distinct (left.trans right.symm)

instance (configuration : Conf 1) : DecidableRel (openDiamond configuration).Adj := by
  intro first second
  change Decidable (∃ edge, openCell configuration edge=true ∧
    ((source edge=first ∧ target edge=second) ∨ (source edge=second ∧ target edge=first)))
  infer_instance

def activeVertex (parent : Fin 4) (configuration : Conf 1) (vertex : Fin 4) : Prop :=
  parent≠3 ∧ ((openDiamond configuration).Reachable 0 vertex ∨
    (parent≠2 ∧ (openDiamond configuration).Reachable 2 vertex))

instance (parent : Fin 4) (configuration : Conf 1) (vertex : Fin 4) :
    Decidable (activeVertex parent configuration vertex) := by
  unfold activeVertex
  infer_instance

def derivedColour (parent : Fin 4) (configuration : Conf 1) (edge : Fin 4) : Fin 4 :=
  if activeVertex parent configuration (source edge) then
    if activeVertex parent configuration (target edge) then
      if openCell configuration edge then 0 else 1
    else 2
  else if activeVertex parent configuration (target edge) then 2 else 3

def derivedReverse (parent : Fin 4) (configuration : Conf 1) (edge : Fin 4) : Bool :=
  decide (activeVertex parent configuration (target edge) ∧
    ¬ activeVertex parent configuration (source edge))

/-- Outcome and edge numbering agree with the frozen literal audit. -/
def reverseGreen (parent : Fin 4) (outcome : Fin 9) (edge : Fin 4) : Bool :=
  if parent=0 then decide ((outcome=5 ∧ edge=3) ∨ (outcome=6 ∧ edge=1))
  else if parent=1 then
    decide (((outcome=0 ∨ outcome=1) ∧ edge=3) ∨
    ((outcome=2 ∨ outcome=3) ∧ edge=1) ∨ (outcome=8 ∧ (edge=1 ∨ edge=3)))
  else false

theorem openDiamond_terminal_connectivity (configuration : Conf 1) :
    (openDiamond configuration).Reachable 0 2 ↔ conn 1 configuration=true := by
  rcases configuration with ⟨first, second, third, fourth⟩
  cases first <;> cases second <;> cases third <;> cases fourth <;> decide

/-- Exhaustive actual reachability derivation of every permitted local state.
The green outcomes collapse several inactive configurations, as in the figure. -/
theorem all_conditional_configuration_states (parent : Fin 4) (configuration : Conf 1)
    (condition : configuration ∈ conditioningEvent parent) :
    derivedColour parent configuration = colour parent (conditionedOutcome parent configuration) ∧
    derivedReverse parent configuration = reverseGreen parent (conditionedOutcome parent configuration) := by
  revert condition
  simp only [conditioningEvent, Set.mem_setOf_eq]
  rcases configuration with ⟨first, second, third, fourth⟩
  fin_cases parent <;> cases first <;> cases second <;> cases third <;> cases fourth <;> decide

theorem actual_conditional_states_ae (p : ℝ) (parent : Fin 4) :
    ∀ᵐ configuration ∂ProbabilityTheory.cond (confMeasure p 1) (conditioningEvent parent),
      derivedColour parent configuration = colour parent (conditionedOutcome parent configuration) ∧
      derivedReverse parent configuration = reverseGreen parent (conditionedOutcome parent configuration) := by
  exact ae_cond_of_forall_mem MeasurableSet.of_discrete
    (fun configuration condition => all_conditional_configuration_states parent configuration condition)

def candidateSource (parent : Fin 4) (outcome : Fin 9) (edge : Fin 4) : Fin 4 :=
  if reverseGreen parent outcome edge then target edge else source edge

def candidateTarget (parent : Fin 4) (outcome : Fin 9) (edge : Fin 4) : Fin 4 :=
  if reverseGreen parent outcome edge then source edge else target edge

def candidateRuleGraph (parent : Fin 4) (outcome : Fin 9) : EIGS.ColGraph 4 where
  V := Fin 4
  E := Fin 4
  tail := candidateSource parent outcome
  head := candidateTarget parent outcome
  col := colour parent outcome

def candidateRuleSystem (outcomes : Fin 4 → Fin 9) : EIGS.EIGSData 4 where
  initCol := 0
  rule := fun parent => candidateRuleGraph parent (outcomes parent)
  plantPlus := fun _ => (0 : Fin 4)
  plantMinus := fun _ => (2 : Fin 4)
  plant_ne := by intro parent; change (0 : Fin 4) ≠ 2; decide

theorem only_green_reversed (parent : Fin 4) (outcome : Fin 9) (edge : Fin 4)
    (reversed : reverseGreen parent outcome edge=true) : colour parent outcome edge=2 := by
  revert reversed
  fin_cases parent <;> fin_cases outcome <;> fin_cases edge <;> decide

theorem exact_reversal_condition (parent : Fin 4) (outcome : Fin 9) (edge : Fin 4) :
    reverseGreen parent outcome edge=true ↔
      (parent=0 ∨ parent=1) ∧ colour parent outcome edge=2 ∧ (edge=1 ∨ edge=3) := by
  fin_cases parent <;> fin_cases outcome <;> fin_cases edge <;> decide

def boundaryCount (row : Fin 8) (outcome : Fin 9) (column : Fin 8) : ℕ :=
  ∑ edge : Fin 4, if colour (boundaryParent row) outcome edge=boundaryParent column ∧
    (if column.val%2=0 then ((candidateRuleGraph (boundaryParent row) outcome).tail edge : Fin 4)
      else ((candidateRuleGraph (boundaryParent row) outcome).head edge : Fin 4)) =
    (if row.val%2=0 then (0 : Fin 4) else 2) then 1 else 0

theorem boundaryCount_formula : boundaryCount = fun row outcome column =>
    if row.val%2=0 then
      if column.val%2=0 then outgoingCount (boundaryParent row) outcome (boundaryParent column) else 0
    else if row.val<4 ∧ column=4 then incomingCount (boundaryParent row) outcome 2
    else if row.val<4 ∧ column=5 then 0
    else if column.val%2=1 then incomingCount (boundaryParent row) outcome (boundaryParent column) else 0 := by
  decide

noncomputable def candidateMeanBoundary : Matrix (Fin 8) (Fin 8) ℝ := fun row column =>
  if boundaryParent row=3 ∨ boundaryParent column=3 then 0
  else expected (boundaryParent row) (fun outcome => boundaryCount row outcome column)

/-- The exact candidate mean. Off-parity entries record reversed green cells. -/
def candidateBoundaryMatrix {R : Type*} [CommRing R] (p : R) : Matrix (Fin 8) (Fin 8) R :=
  !![4*p^2,0,2*p^4,0,2*p^5,0,0,0;
     0,4*p^2,0,2*p^4,2*p^5,0,0,0;
     2*p^2,0,2*p^2,0,2*p^3,0,0,0;
     0,2*p^2,0,2*p^2,2*p^3,0,0,0;
     2*p^2,0,0,0,2*p,0,0,0;
     0,0,0,0,0,2*p^2,0,0;
     0,0,0,0,0,0,0,0;
     0,0,0,0,0,0,0,0]

private theorem candidateMeanBoundary_transform : candidateMeanBoundary = fun row column =>
    if row=1 ∨ row=3 then
      if column=4 then meanLiveBoundary row 5
      else if column=5 then 0 else meanLiveBoundary row column
    else meanLiveBoundary row column := by
  ext row column
  simp_rw [candidateMeanBoundary, boundaryCount_formula]
  fin_cases row <;> fin_cases column <;>
    norm_num [meanLiveBoundary, boundaryParent, expected, Fin.ext_iff]
  all_goals rfl

theorem candidateMeanBoundary_eq :
    candidateMeanBoundary = candidateBoundaryMatrix Reduced.pc := by
  rw [candidateMeanBoundary_transform]
  simp_rw [meanLiveBoundary_eq_correctedCriticalEN]
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [candidateBoundaryMatrix, Outlook.correctedCriticalEN, Outlook.EN, Fin.ext_iff]
  all_goals rfl

noncomputable def candidateMeanMass : Matrix (Fin 4) (Fin 4) ℝ := fun parent selected =>
  if parent=3 ∨ selected=3 then 0 else expected parent (fun outcome =>
    (Outlook.colourEdges Finset.univ (candidateRuleGraph parent outcome).col selected).card)

theorem massMean_unchanged : candidateMeanMass = Outlook.EM Reduced.pc := by
  change meanLiveMass = Outlook.EM Reduced.pc
  exact meanLiveMass_eq_EM

end Outlook.FourColourOrientationCandidate

#print axioms Outlook.FourColourOrientationCandidate.openDiamond_terminal_connectivity
#print axioms Outlook.FourColourOrientationCandidate.candidateRuleSystem
#print axioms Outlook.FourColourOrientationCandidate.all_conditional_configuration_states
#print axioms Outlook.FourColourOrientationCandidate.actual_conditional_states_ae
#print axioms Outlook.FourColourOrientationCandidate.only_green_reversed
#print axioms Outlook.FourColourOrientationCandidate.exact_reversal_condition
#print axioms Outlook.FourColourOrientationCandidate.boundaryCount_formula
#print axioms Outlook.FourColourOrientationCandidate.candidateMeanBoundary_eq
#print axioms Outlook.FourColourOrientationCandidate.massMean_unchanged
