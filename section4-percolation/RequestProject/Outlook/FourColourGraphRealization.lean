import RequestProject.Outlook.FourColourNetworkPruning
import RequestProject.Outlook.FourColourActualCellComponents
import RequestProject.Outlook.FourColourBranchingLaw

/-! The adopted graphical rule is realized by the original series/parallel
gluing. At depth zero precisely the red cell contributes an open edge.
Green orientation is implemented by reversing the child network, not by
changing a terminal-count statistic. -/
namespace Outlook.FourColourGraphRealization
open Cluster FourColourRuleAudit FourColourOrientationCandidate FourColourCodingTree
open FourColourConditionalHierarchy FourColourActualCellComponents

def orientNetwork (reversed : Bool) (network : TTN) : TTN :=
  if reversed then TTN.reverseNetwork network else network

def diamondNetwork (children : Fin 4 → TTN) : TTN :=
  TTN.parTTN (TTN.seriesTTN (children 0) (children 1))
    (TTN.seriesTTN (children 2) (children 3))

def realize : (depth : ℕ) → Fin 4 → RuleTree depth → TTN
  | 0, parent, _ => if parent=0 then TTN.edgeTTN else TTN.gapTTN
  | depth+1, parent, tree => diamondNetwork (fun edge =>
      orientNetwork (reverseGreen parent tree.1 edge)
        (realize depth (colour parent tree.1 edge) (tree.2 edge)))

def diamondIso {firstChildren secondChildren : Fin 4 → TTN}
    (isomorphisms : ∀ edge, TTN.IncidenceIso (firstChildren edge) (secondChildren edge)) :
    TTN.IncidenceIso (diamondNetwork firstChildren) (diamondNetwork secondChildren) :=
  TTN.IncidenceIso.parallel
    (TTN.IncidenceIso.series (isomorphisms 0) (isomorphisms 1))
    (TTN.IncidenceIso.series (isomorphisms 2) (isomorphisms 3))

def actualEdgeEmbedding (depth : ℕ) (configuration : Conf (depth+1)) (edge : Fin 4) :
    (net depth (childConfiguration depth configuration edge)).E → (net (depth+1) configuration).E := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun impossible => Fin.elim0 impossible)))) edge
  · exact Sum.inl ∘ Sum.inl
  · exact Sum.inl ∘ Sum.inr
  · exact Sum.inr ∘ Sum.inl
  · exact Sum.inr ∘ Sum.inr

theorem actualEdgeEmbedding_tail (depth : ℕ) (configuration : Conf (depth+1)) (edge : Fin 4)
    (childEdge : (net depth (childConfiguration depth configuration edge)).E) :
    (net (depth+1) configuration).tail (actualEdgeEmbedding depth configuration edge childEdge) =
      actualChildEmbedding depth configuration edge
        ((net depth (childConfiguration depth configuration edge)).tail childEdge) := by
  fin_cases edge <;> rfl

theorem actualEdgeEmbedding_head (depth : ℕ) (configuration : Conf (depth+1)) (edge : Fin 4)
    (childEdge : (net depth (childConfiguration depth configuration edge)).E) :
    (net (depth+1) configuration).head (actualEdgeEmbedding depth configuration edge childEdge) =
      actualChildEmbedding depth configuration edge
        ((net depth (childConfiguration depth configuration edge)).head childEdge) := by
  fin_cases edge <;> rfl

theorem actual_child_retainedEdge_iff (depth : ℕ) (parent : Fin 4) (configuration : Conf (depth+1))
    (condition : configuration ∈ parentEvent (depth+1) parent) (edge : Fin 4)
    (childEdge : (net depth (childConfiguration depth configuration edge)).E) :
    TTN.retainedEdge (net (depth+1) configuration) parent false
      (actualEdgeEmbedding depth configuration edge childEdge) ↔
      TTN.retainedEdge (net depth (childConfiguration depth configuration edge))
        (colour parent (conditionedOutcome parent (firstGeneration depth configuration)) edge)
        (reverseGreen parent (conditionedOutcome parent (firstGeneration depth configuration)) edge) childEdge := by
  unfold TTN.retainedEdge
  rw [actualEdgeEmbedding_tail]
  exact actual_child_active_iff depth parent configuration condition edge _

noncomputable def retainedChildren (depth : ℕ) (parent : Fin 4) (configuration : Conf (depth+1))
    (edge : Fin 4) : TTN :=
  TTN.retainedNetwork (net depth (childConfiguration depth configuration edge))
    (colour parent (conditionedOutcome parent (firstGeneration depth configuration)) edge)
    (reverseGreen parent (conditionedOutcome parent (firstGeneration depth configuration)) edge)

noncomputable def retainedDiamondEdgeEquiv (depth : ℕ) (parent : Fin 4) (configuration : Conf (depth+1))
    (condition : configuration ∈ parentEvent (depth+1) parent) :
    (diamondNetwork (retainedChildren depth parent configuration)).E ≃
      (TTN.retainedNetwork (net (depth+1) configuration) parent false).E where
  toFun := by
    rintro ((edge | edge) | (edge | edge))
    · exact ⟨actualEdgeEmbedding depth configuration 0 edge.1,
        (actual_child_retainedEdge_iff depth parent configuration condition 0 edge.1).mpr edge.2⟩
    · exact ⟨actualEdgeEmbedding depth configuration 1 edge.1,
        (actual_child_retainedEdge_iff depth parent configuration condition 1 edge.1).mpr edge.2⟩
    · exact ⟨actualEdgeEmbedding depth configuration 2 edge.1,
        (actual_child_retainedEdge_iff depth parent configuration condition 2 edge.1).mpr edge.2⟩
    · exact ⟨actualEdgeEmbedding depth configuration 3 edge.1,
        (actual_child_retainedEdge_iff depth parent configuration condition 3 edge.1).mpr edge.2⟩
  invFun := by
    rintro ⟨((edge | edge) | (edge | edge)), active⟩
    · exact Sum.inl (Sum.inl ⟨edge,
        (actual_child_retainedEdge_iff depth parent configuration condition 0 edge).mp active⟩)
    · exact Sum.inl (Sum.inr ⟨edge,
        (actual_child_retainedEdge_iff depth parent configuration condition 1 edge).mp active⟩)
    · exact Sum.inr (Sum.inl ⟨edge,
        (actual_child_retainedEdge_iff depth parent configuration condition 2 edge).mp active⟩)
    · exact Sum.inr (Sum.inr ⟨edge,
        (actual_child_retainedEdge_iff depth parent configuration condition 3 edge).mp active⟩)
  left_inv := by rintro ((edge | edge) | (edge | edge)) <;> rfl
  right_inv := by rintro ⟨((edge | edge) | (edge | edge)), active⟩ <;> rfl

/-- The four genuinely retained child networks glue to exactly the parent's
retained edges, with their original incidence and terminals. -/
noncomputable def retainedDiamondIso (depth : ℕ) (parent : Fin 4) (configuration : Conf (depth+1))
    (condition : configuration ∈ parentEvent (depth+1) parent) :
    TTN.IncidenceIso (diamondNetwork (retainedChildren depth parent configuration))
      (TTN.retainedNetwork (net (depth+1) configuration) parent false) where
  vertices := Equiv.refl _
  edges := retainedDiamondEdgeEquiv depth parent configuration condition
  tail := by rintro ((edge | edge) | (edge | edge)) <;> rfl
  head := by rintro ((edge | edge) | (edge | edge)) <;> rfl
  source := rfl
  target := rfl

noncomputable def retainedRedEdgeIso :
    TTN.IncidenceIso TTN.edgeTTN (TTN.retainedNetwork TTN.edgeTTN 0 false) where
  vertices := Equiv.refl _
  edges := (Equiv.subtypeUnivEquiv (fun edge : TTN.edgeTTN.E =>
    show TTN.retainedEdge TTN.edgeTTN 0 false edge from
      Or.inl (TTN.edgePath_self TTN.edgeTTN TTN.edgeTTN.a))).symm
  tail := fun _ => rfl
  head := fun _ => rfl
  source := rfl
  target := rfl

noncomputable def retainedGapIso (parent : Fin 4) (reversed : Bool) :
    TTN.IncidenceIso TTN.gapTTN (TTN.retainedNetwork TTN.gapTTN parent reversed) where
  vertices := Equiv.refl _
  edges := {
    toFun := fun edge => Empty.elim edge
    invFun := fun edge => edge.1
    left_inv := fun edge => Empty.elim edge
    right_inv := fun edge => Empty.elim edge.1 }
  tail := fun edge => Empty.elim edge
  head := fun edge => Empty.elim edge
  source := rfl
  target := rfl

noncomputable def retainedBlackEdgeIso :
    TTN.IncidenceIso TTN.gapTTN (TTN.retainedNetwork TTN.edgeTTN 3 false) := by
  haveI : IsEmpty (TTN.retainedNetwork TTN.edgeTTN 3 false).E :=
    ⟨fun edge => show False from edge.2⟩
  exact {
    vertices := Equiv.refl _
    edges := {
      toFun := fun edge => Empty.elim edge
      invFun := fun edge => False.elim edge.2
      left_inv := fun edge => Empty.elim edge
      right_inv := fun edge => False.elim edge.2 }
    tail := fun edge => Empty.elim edge
    head := fun edge => Empty.elim edge
    source := rfl
    target := rfl }

noncomputable def leafRealizationIso (parent : Fin 4) (configuration : Conf 0)
    (condition : configuration ∈ parentEvent 0 parent) :
    TTN.IncidenceIso (realize 0 parent (encode 0 parent configuration))
      (TTN.retainedNetwork (net 0 configuration) parent false) := by
  by_cases red : parent=0
  · subst parent
    have openEdge : configuration=true := condition
    subst configuration
    exact retainedRedEdgeIso
  · cases configuration
    · simpa only [realize, if_neg red, net] using retainedGapIso parent false
    · have black : parent=3 := by
        by_contra nonblack
        simpa [parentEvent, red, nonblack, conn] using condition
      subst parent
      exact retainedBlackEdgeIso

/-- All-depth incidence identification of the realized rule tree with the
actual retained network. Inactive ambient vertices are removed separately
when passing to the connected cluster graph. -/
noncomputable def actualRealizationIso (depth : ℕ) (parent : Fin 4) (configuration : Conf depth)
    (condition : configuration ∈ parentEvent depth parent) :
    TTN.IncidenceIso (realize depth parent (encode depth parent configuration))
      (TTN.retainedNetwork (net depth configuration) parent false) := by
  induction depth generalizing parent with
  | zero => exact leafRealizationIso parent configuration condition
  | succ depth induction =>
      refine (diamondIso (fun edge => ?_)).trans (retainedDiamondIso depth parent configuration condition)
      have childIso := induction
        (colour parent (conditionedOutcome parent (firstGeneration depth configuration)) edge)
        (orientedChild depth parent configuration edge)
        (orientedChild_condition depth parent configuration condition edge)
      by_cases reversed : reverseGreen parent (conditionedOutcome parent (firstGeneration depth configuration)) edge=true
      · simp only [orientedChild, reversed, if_true] at childIso
        have reflection := TTN.retainedNetworkReflection
          (actualNetworkReflection depth (childConfiguration depth configuration edge))
          (colour parent (conditionedOutcome parent (firstGeneration depth configuration)) edge) true
        have undoReflection := (TTN.IncidenceIso.fromReflection reflection).symm.reverse
        simpa only [encode, orientNetwork, retainedChildren, orientedChild, reversed, if_true] using
          childIso.reverse.trans undoReflection
      · have forward : reverseGreen parent (conditionedOutcome parent (firstGeneration depth configuration)) edge=false :=
          Bool.eq_false_iff.mpr reversed
        simpa only [encode, orientNetwork, retainedChildren, orientedChild, forward, Bool.false_eq_true, if_false] using childIso

end Outlook.FourColourGraphRealization

#print axioms Outlook.FourColourGraphRealization.diamondIso
#print axioms Outlook.FourColourGraphRealization.actual_child_retainedEdge_iff
#print axioms Outlook.FourColourGraphRealization.retainedDiamondIso
#print axioms Outlook.FourColourGraphRealization.leafRealizationIso
#print axioms Outlook.FourColourGraphRealization.actualRealizationIso
