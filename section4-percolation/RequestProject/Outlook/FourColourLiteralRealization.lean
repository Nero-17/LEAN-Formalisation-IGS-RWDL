import RequestProject.Outlook.FourColourUndirectedNetworkIso
import RequestProject.Outlook.FourColourActualGraphLaw

/-! Literal adopted EIGS attachment: when a green parent arrow is reversed,
the child template's two planting attachments are exchanged, while every
internal tail/head pair remains exactly as drawn in its template. -/
namespace Outlook.FourColourLiteralRealization
open Cluster MeasureTheory FourColourRuleAudit FourColourOrientationCandidate
open FourColourConditionalHierarchy FourColourCodingTree FourColourBranchingLaw
open FourColourGraphRealization FourColourClusterIsomorphism FourColourActualGraphLaw

def swapTerminals (network : TTN) : TTN where
  V := network.V
  E := network.E
  fintypeV := network.fintypeV
  decEqV := network.decEqV
  fintypeE := network.fintypeE
  tail := network.tail
  head := network.head
  a := network.b
  b := network.a
  hab := Ne.symm network.hab

def attachNetwork (reversed : Bool) (network : TTN) : TTN :=
  if reversed then swapTerminals network else network

def literalRealize : (depth : ℕ) → Fin 4 → RuleTree depth → TTN
  | 0, parent, _ => if parent=0 then TTN.edgeTTN else TTN.gapTTN
  | depth+1, parent, tree => diamondNetwork (fun edge =>
      attachNetwork (reverseGreen parent tree.1 edge)
        (literalRealize depth (colour parent tree.1 edge) (tree.2 edge)))

def reversedAttachmentIso {firstNetwork secondNetwork : TTN}
    (isomorphism : TTN.UndirectedIso firstNetwork secondNetwork) :
    TTN.UndirectedIso (swapTerminals firstNetwork) (TTN.reverseNetwork secondNetwork) where
  vertices := isomorphism.vertices
  edges := isomorphism.edges
  ends := fun edge => (isomorphism.ends edge).symm
  source := isomorphism.target
  target := isomorphism.source

def diamondUndirectedIso {firstChildren secondChildren : Fin 4 → TTN}
    (isomorphisms : ∀ edge, TTN.UndirectedIso (firstChildren edge) (secondChildren edge)) :
    TTN.UndirectedIso (diamondNetwork firstChildren) (diamondNetwork secondChildren) :=
  TTN.UndirectedIso.parallel
    (TTN.UndirectedIso.series (isomorphisms 0) (isomorphisms 1))
    (TTN.UndirectedIso.series (isomorphisms 2) (isomorphisms 3))

/-- The literal directed realization and the orientation-normalized electrical
realization have the same undirected edge incidences and the same two marked
terminals, through explicit vertex and edge bijections. -/
def literalRealizationIso (depth : ℕ) (parent : Fin 4) (tree : RuleTree depth) :
    TTN.UndirectedIso (literalRealize depth parent tree) (realize depth parent tree) := by
  induction depth generalizing parent with
  | zero => exact TTN.UndirectedIso.refl _
  | succ depth induction =>
      refine diamondUndirectedIso (fun edge => ?_)
      have childIso := induction (colour parent tree.1 edge) (tree.2 edge)
      by_cases reversed : reverseGreen parent tree.1 edge=true
      · simpa only [attachNetwork, orientNetwork, reversed, if_true] using reversedAttachmentIso childIso
      · have forward : reverseGreen parent tree.1 edge=false := Bool.eq_false_iff.mpr reversed
        simpa only [attachNetwork, orientNetwork, forward, Bool.false_eq_true, if_false] using childIso

noncomputable def literalRedClusterIso (depth : ℕ) (configuration : Conf depth)
    (connected : configuration ∈ parentEvent depth 0) :
    TTN.sourceClusterGraph (literalRealize depth 0 (encode depth 0 configuration)) ≃g
      TTN.sourceClusterGraph (net depth configuration) :=
  (literalRealizationIso depth 0 (encode depth 0 configuration)).sourceClusterIso.trans
    (actualRedClusterIso depth configuration connected)

theorem literalSourceClusterShape_eq (depth : ℕ) (parent : Fin 4) (tree : RuleTree depth) :
    sourceClusterShape (literalRealize depth parent tree) = sourceClusterShape (realize depth parent tree) :=
  Quotient.sound ⟨(literalRealizationIso depth parent tree).sourceClusterIso⟩

/-- Exact finite-generation law for the original cluster and the literal
adopted substitution. The graph shape removes inactive isolated vertices.
No equality of internal directed-arrow conventions is asserted. -/
theorem actual_literal_red_sourceClusterLaw (depth : ℕ) :
    (parentMeasure depth 0).map (fun configuration => sourceClusterShape (net depth configuration)) =
      (ruleTreeLaw depth 0).map (fun tree => sourceClusterShape (literalRealize depth 0 tree)) := by
  rw [actual_red_sourceClusterLaw]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall (fun tree => (literalSourceClusterShape_eq depth 0 tree).symm)

end Outlook.FourColourLiteralRealization

#print axioms Outlook.FourColourLiteralRealization.literalRealizationIso
#print axioms Outlook.FourColourLiteralRealization.literalRedClusterIso
#print axioms Outlook.FourColourLiteralRealization.literalSourceClusterShape_eq
#print axioms Outlook.FourColourLiteralRealization.actual_literal_red_sourceClusterLaw
