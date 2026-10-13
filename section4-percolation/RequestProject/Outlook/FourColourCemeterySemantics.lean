import RequestProject.Outlook.FourColourActualCellComponents

/-! Semantic audit. The cemetery state forgets internal connectivity;
it records that no terminal component remains active. This does not alter any
adopted substitution rule or any already verified graph-law statement. -/
namespace Outlook.FourColourCemeterySemantics
open Cluster FourColourRuleAudit FourColourConditionalHierarchy FourColourCodingTree
open FourColourOrientationCandidate FourColourActualCellComponents

/-- The upper-left and both lower bonds are closed; the upper-right bond is open. -/
def hiddenOpenConfiguration : Conf 1 := (false, true, false, false)

theorem hiddenOpen_parent_condition : hiddenOpenConfiguration ∈ parentEvent 1 2 := by
  change conn 1 hiddenOpenConfiguration = false
  decide

theorem hiddenOpen_child_colour :
    colour 2 (conditionedOutcome 2 (firstGeneration 0 hiddenOpenConfiguration)) 1 = 3 := by
  decide

theorem hiddenOpen_child_connected :
    conn 0 (childConfiguration 0 hiddenOpenConfiguration 1) = true := by
  decide

/-- The genuinely open right-hand child has no vertex in the active source
component of its green parent; its black designation is therefore correct. -/
theorem hiddenOpen_child_inactive
    (vertex : (net 0 (childConfiguration 0 hiddenOpenConfiguration 1)).V) :
    ¬ TTN.activeComponent (net 1 hiddenOpenConfiguration) 2 false
      (actualChildEmbedding 0 hiddenOpenConfiguration 1 vertex) := by
  rw [actual_child_active_iff 0 2 hiddenOpenConfiguration hiddenOpen_parent_condition 1 vertex,
    hiddenOpen_child_colour]
  simp [TTN.activeComponent]

end Outlook.FourColourCemeterySemantics

#print axioms Outlook.FourColourCemeterySemantics.hiddenOpen_parent_condition
#print axioms Outlook.FourColourCemeterySemantics.hiddenOpen_child_colour
#print axioms Outlook.FourColourCemeterySemantics.hiddenOpen_child_connected
#print axioms Outlook.FourColourCemeterySemantics.hiddenOpen_child_inactive
