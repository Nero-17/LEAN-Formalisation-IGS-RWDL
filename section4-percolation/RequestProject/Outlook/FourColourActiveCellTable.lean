import RequestProject.Outlook.FourColourRetainedGraph

/-! Finite component-membership table for the four actual cell positions.
The two vertex flags represent reachability from the child's two terminals;
their consistency when the child connects is an explicit mathematical premise. -/
namespace Outlook.FourColourActiveCellTable
open Cluster FourColourRuleAudit FourColourOrientationCandidate

set_option maxHeartbeats 2000000

def childComponentTest (parent : Fin 4) (configuration : Conf 1) (edge : Fin 4)
    (fromSource fromTarget : Bool) : Bool :=
  if parent=3 then false else if parent=2 then
    ![fromSource, configuration.1 && fromSource, fromSource, configuration.2.2.1 && fromSource] edge
  else
    ![fromSource || (configuration.2.1 && fromTarget), (configuration.1 && fromSource) || fromTarget,
      fromSource || (configuration.2.2.2 && fromTarget), (configuration.2.2.1 && fromSource) || fromTarget] edge

def orientedColourTest (parent : Fin 4) (reversed : Bool) (fromSource fromTarget : Bool) : Bool :=
  if parent=3 then false else if parent=2 then
    (if reversed then fromTarget else fromSource) else fromSource || fromTarget

theorem all_actual_component_states (parent : Fin 4) (configuration : Conf 1)
    (condition : configuration ∈ conditioningEvent parent) (edge : Fin 4)
    (fromSource fromTarget : Bool)
    (consistent : openCell configuration edge=true → fromSource=fromTarget) :
    childComponentTest parent configuration edge fromSource fromTarget =
      orientedColourTest (colour parent (conditionedOutcome parent configuration) edge)
        (reverseGreen parent (conditionedOutcome parent configuration) edge) fromSource fromTarget := by
  revert condition consistent
  simp only [conditioningEvent, Set.mem_setOf_eq]
  rcases configuration with ⟨first, second, third, fourth⟩
  fin_cases parent <;> cases first <;> cases second <;> cases third <;> cases fourth <;>
    fin_cases edge <;> cases fromSource <;> cases fromTarget <;> decide

end Outlook.FourColourActiveCellTable

#print axioms Outlook.FourColourActiveCellTable.all_actual_component_states
