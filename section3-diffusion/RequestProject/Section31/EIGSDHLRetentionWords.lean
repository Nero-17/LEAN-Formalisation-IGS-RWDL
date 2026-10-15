import RequestProject.Section31.EIGSDHLAddressLetters

/-! Good words retain one actual coarse terminal through DHL substitutions.
The orientation state is updated after every letter; the backward first
branch is included. Every branch word gives a distinct good edge word. -/

namespace EIGS
open scoped Classical
noncomputable section

def dhlEndpointChild (head : Bool) (branch : Fin 2) : Fin 2 × Fin 2 :=
  (branch, if head then 1 else 0)

def dhlEndpointAfterChild (head : Bool) (branch : Fin 2) : Bool :=
  if branch.val = 0 then !head else head

def dhlEdgeEndpoint (level : ℕ) (edge : XiEdge (flowerSystem 2 2).toRuleData level)
    (head : Bool) : XiVtx (flowerSystem 2 2) level :=
  if head then XiHead (flowerSystem 2 2) level edge else XiTail (flowerSystem 2 2) level edge

theorem dhlEndpointChild_preserves_vertex (level : ℕ)
    (edge : XiEdge (flowerSystem 2 2).toRuleData level) (head : Bool) (branch : Fin 2) :
    dhlEdgeEndpoint (level + 1) ⟨edge, dhlEndpointChild head branch⟩
      (dhlEndpointAfterChild head branch) = Sum.inl (dhlEdgeEndpoint level edge head) := by
  cases head <;> fin_cases branch <;>
    simp [dhlEdgeEndpoint, dhlEndpointChild, dhlEndpointAfterChild, XiTail_succ, XiHead_succ,
      flowerSystem, flowerGraph, flowerEdgeStart, flowerEdgeEnd, flowerPoint, embedRuleVtx]

def dhlRetentionEndpoint : (width : ℕ) → Bool → (Fin width → Fin 2) → Bool
  | 0, head, _ => head
  | width + 1, head, branches =>
      dhlEndpointAfterChild
        (dhlRetentionEndpoint width head (fun position => branches position.castSucc))
        (branches (Fin.last width))

def dhlRetentionWord : (width : ℕ) → Bool → (Fin width → Fin 2) → (Fin width → Fin 2 × Fin 2)
  | 0, _, _ => fun position => Fin.elim0 position
  | width + 1, head, branches =>
      Fin.lastCases
        (dhlEndpointChild (dhlRetentionEndpoint width head (fun position => branches position.castSucc))
          (branches (Fin.last width)))
        (dhlRetentionWord width head (fun position => branches position.castSucc))

theorem dhlRetentionWord_branch (width : ℕ) (head : Bool) (branches : Fin width → Fin 2)
    (position : Fin width) : (dhlRetentionWord width head branches position).1 = branches position := by
  induction width generalizing head with
  | zero => exact Fin.elim0 position
  | succ width induction =>
      refine Fin.lastCases ?_ (fun earlier => ?_) position
      · simp [dhlRetentionWord, dhlEndpointChild]
      · simpa only [dhlRetentionWord, Fin.lastCases_castSucc] using
          induction head (fun index => branches index.castSucc) earlier

theorem dhlRetentionWord_injective (width : ℕ) (head : Bool) :
    Function.Injective (dhlRetentionWord width head) := by
  intro first second equality
  funext position
  have coordinates := congrArg (fun word : Fin width → Fin 2 × Fin 2 => (word position).1) equality
  simpa only [dhlRetentionWord_branch] using coordinates

def dhlDescendantEdge (coarse : ℕ) : (width : ℕ) →
    XiEdge (flowerSystem 2 2).toRuleData coarse → (Fin width → Fin 2 × Fin 2) →
      XiEdge (flowerSystem 2 2).toRuleData (coarse + width)
  | 0, edge, _ => edge
  | width + 1, edge, word =>
      ⟨dhlDescendantEdge coarse width edge (fun position => word position.castSucc), word (Fin.last width)⟩

theorem dhlRetentionWord_preserves_terminal (coarse width : ℕ)
    (edge : XiEdge (flowerSystem 2 2).toRuleData coarse) (head : Bool) (branches : Fin width → Fin 2) :
    dhlEdgeEndpoint (coarse + width) (dhlDescendantEdge coarse width edge (dhlRetentionWord width head branches))
      (dhlRetentionEndpoint width head branches) =
        xiForward (flowerSystem 2 2) coarse width (dhlEdgeEndpoint coarse edge head) := by
  induction width generalizing head with
  | zero => rfl
  | succ width induction =>
      have wordPrefixEquality :
          (fun position : Fin width => dhlRetentionWord (width + 1) head branches position.castSucc) =
            dhlRetentionWord width head (fun position => branches position.castSucc) := by
        funext position
        simp only [dhlRetentionWord, Fin.lastCases_castSucc]
      have wordLastEquality : dhlRetentionWord (width + 1) head branches (Fin.last width) =
          dhlEndpointChild
            (dhlRetentionEndpoint width head (fun position => branches position.castSucc))
            (branches (Fin.last width)) := by
        simp only [dhlRetentionWord, Fin.lastCases_last]
      change dhlEdgeEndpoint ((coarse + width) + 1)
        ⟨dhlDescendantEdge coarse width edge
            (fun position : Fin width => dhlRetentionWord (width + 1) head branches position.castSucc),
          dhlRetentionWord (width + 1) head branches (Fin.last width)⟩
        (dhlEndpointAfterChild
          (dhlRetentionEndpoint width head (fun position => branches position.castSucc))
          (branches (Fin.last width))) =
        Sum.inl (xiForward (flowerSystem 2 2) coarse width (dhlEdgeEndpoint coarse edge head))
      rw [wordPrefixEquality, wordLastEquality, dhlEndpointChild_preserves_vertex]
      exact congrArg Sum.inl (induction head (fun position => branches position.castSucc))

end
end EIGS

#print axioms EIGS.dhlEndpointChild_preserves_vertex
#print axioms EIGS.dhlRetentionWord_branch
#print axioms EIGS.dhlRetentionWord_injective
#print axioms EIGS.dhlRetentionWord_preserves_terminal
