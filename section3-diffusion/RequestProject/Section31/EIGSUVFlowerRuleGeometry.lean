import RequestProject.Section31.EIGSUVFlowerModel
import RequestProject.Section1Connected
import RequestProject.Section2Simplicity
import RequestProject.Section2Concrete

/-! Literal path geometry for the genuine unequal-path flower. These
statements concern the new two-path graph, not the legacy DHL family. -/

namespace EIGS
noncomputable section
open scoped Classical

def uvFlowerPathHeight (length : ℕ) : Bool ⊕ Fin (length - 1) → ℕ
  | Sum.inl false => 0
  | Sum.inl true => length
  | Sum.inr vertex => vertex.val + 1

@[simp] theorem uvFlowerPathTail_height (length : ℕ) (edge : Fin length) :
    uvFlowerPathHeight length (uvFlowerPathTail length edge) = edge.val := by
  by_cases first : edge.val = 0
  · simp [uvFlowerPathTail, uvFlowerPathHeight, first]
  · simp only [uvFlowerPathTail, dif_neg first, uvFlowerPathHeight]
    omega

@[simp] theorem uvFlowerPathHead_height (length : ℕ) (edge : Fin length) :
    uvFlowerPathHeight length (uvFlowerPathHead length edge) = edge.val + 1 := by
  by_cases last : edge.val + 1 = length <;>
    simp [uvFlowerPathHead, uvFlowerPathHeight, last]

def uvFlowerLeftProjection (firstLength secondLength : ℕ) :
    UVFlowerVertex firstLength secondLength → Bool ⊕ Fin (firstLength - 1)
  | Sum.inl endpoint => Sum.inl endpoint
  | Sum.inr (Sum.inl vertex) => Sum.inr vertex
  | Sum.inr (Sum.inr _) => Sum.inl false

def uvFlowerRightProjection (firstLength secondLength : ℕ) :
    UVFlowerVertex firstLength secondLength → Bool ⊕ Fin (secondLength - 1)
  | Sum.inl endpoint => Sum.inl endpoint
  | Sum.inr (Sum.inl _) => Sum.inl false
  | Sum.inr (Sum.inr vertex) => Sum.inr vertex

@[simp] theorem uvFlowerLeftProjection_embedding (firstLength secondLength : ℕ)
    (vertex : Bool ⊕ Fin (firstLength - 1)) :
    uvFlowerLeftProjection firstLength secondLength
      (uvFlowerLeftEmbedding firstLength secondLength vertex) = vertex := by
  cases vertex <;> rfl

@[simp] theorem uvFlowerRightProjection_embedding (firstLength secondLength : ℕ)
    (vertex : Bool ⊕ Fin (secondLength - 1)) :
    uvFlowerRightProjection firstLength secondLength
      (uvFlowerRightEmbedding firstLength secondLength vertex) = vertex := by
  cases vertex <;> rfl

def uvFlowerBranchLabel (firstLength secondLength : ℕ) :
    UVFlowerVertex firstLength secondLength → Option Bool
  | Sum.inl _ => none
  | Sum.inr (Sum.inl _) => some false
  | Sum.inr (Sum.inr _) => some true

def uvFlowerEdgeBranch (firstLength secondLength : ℕ) :
    UVFlowerEdge firstLength secondLength → Bool := Sum.elim (fun _ => false) (fun _ => true)

theorem uvFlowerRuleGraph_endpoint_labels (firstLength secondLength : ℕ)
    (edge : UVFlowerEdge firstLength secondLength) :
    (uvFlowerBranchLabel firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).tail edge) = none ∨
      uvFlowerBranchLabel firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).tail edge) =
        some (uvFlowerEdgeBranch firstLength secondLength edge)) ∧
    (uvFlowerBranchLabel firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).head edge) = none ∨
      uvFlowerBranchLabel firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).head edge) =
        some (uvFlowerEdgeBranch firstLength secondLength edge)) := by
  cases edge with
  | inl edge =>
    simp only [uvFlowerRuleGraph, Sum.elim_inl, uvFlowerEdgeBranch]
    constructor <;> simp only [uvFlowerPathTail, uvFlowerPathHead] <;>
      split_ifs <;> simp [uvFlowerLeftEmbedding, uvFlowerBranchLabel]
  | inr edge =>
    simp only [uvFlowerRuleGraph, Sum.elim_inr, uvFlowerEdgeBranch]
    constructor <;> simp only [uvFlowerPathTail, uvFlowerPathHead] <;>
      split_ifs <;> simp [uvFlowerRightEmbedding, uvFlowerBranchLabel]

theorem uvFlowerRuleGraph_has_labeled_endpoint (firstLength secondLength : ℕ)
    (firstAtLeastTwo : 2 ≤ firstLength) (secondAtLeastTwo : 2 ≤ secondLength)
    (edge : UVFlowerEdge firstLength secondLength) :
    uvFlowerBranchLabel firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).tail edge) =
        some (uvFlowerEdgeBranch firstLength secondLength edge) ∨
      uvFlowerBranchLabel firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).head edge) =
        some (uvFlowerEdgeBranch firstLength secondLength edge) := by
  cases edge with
  | inl edge =>
    by_cases first : edge.val = 0
    · left
      have notLast : edge.val + 1 ≠ firstLength := by omega
      simp [uvFlowerRuleGraph, uvFlowerPathHead, notLast, uvFlowerLeftEmbedding,
        uvFlowerBranchLabel, uvFlowerEdgeBranch]
    · right
      simp [uvFlowerRuleGraph, uvFlowerPathTail, first, uvFlowerLeftEmbedding,
        uvFlowerBranchLabel, uvFlowerEdgeBranch]
  | inr edge =>
    by_cases first : edge.val = 0
    · right
      have notLast : edge.val + 1 ≠ secondLength := by omega
      simp [uvFlowerRuleGraph, uvFlowerPathHead, notLast, uvFlowerRightEmbedding,
        uvFlowerBranchLabel, uvFlowerEdgeBranch]
    · left
      simp [uvFlowerRuleGraph, uvFlowerPathTail, first, uvFlowerRightEmbedding,
        uvFlowerBranchLabel, uvFlowerEdgeBranch]

theorem uvFlowerRuleGraph_edges (firstLength secondLength : ℕ) :
    Fintype.card (uvFlowerRuleGraph firstLength secondLength).E = firstLength + secondLength := by
  simp [uvFlowerRuleGraph, UVFlowerEdge]

theorem uvFlowerRuleGraph_vertices (firstLength secondLength : ℕ)
    (firstPositive : 0 < firstLength) (secondPositive : 0 < secondLength) :
    Fintype.card (uvFlowerRuleGraph firstLength secondLength).V = firstLength + secondLength := by
  simp only [uvFlowerRuleGraph, UVFlowerVertex, Fintype.card_sum, Fintype.card_bool, Fintype.card_fin]
  omega

theorem uvFlowerSystem_loopless (firstLength secondLength : ℕ) (colour : Fin 1) :
    ((uvFlowerSystem firstLength secondLength).ruleNetwork colour).Loopless := by
  intro edge equality
  cases edge with
  | inl edge =>
    have heights := congrArg
      (fun vertex => uvFlowerPathHeight firstLength (uvFlowerLeftProjection firstLength secondLength vertex)) equality
    change uvFlowerPathHeight firstLength (uvFlowerLeftProjection firstLength secondLength
        (uvFlowerLeftEmbedding firstLength secondLength (uvFlowerPathHead firstLength edge))) =
      uvFlowerPathHeight firstLength (uvFlowerLeftProjection firstLength secondLength
        (uvFlowerLeftEmbedding firstLength secondLength (uvFlowerPathTail firstLength edge))) at heights
    simp only [uvFlowerLeftProjection_embedding, uvFlowerPathHead_height, uvFlowerPathTail_height] at heights
    omega
  | inr edge =>
    have heights := congrArg
      (fun vertex => uvFlowerPathHeight secondLength (uvFlowerRightProjection firstLength secondLength vertex)) equality
    change uvFlowerPathHeight secondLength (uvFlowerRightProjection firstLength secondLength
        (uvFlowerRightEmbedding firstLength secondLength (uvFlowerPathTail secondLength edge))) =
      uvFlowerPathHeight secondLength (uvFlowerRightProjection firstLength secondLength
        (uvFlowerRightEmbedding firstLength secondLength (uvFlowerPathHead secondLength edge))) at heights
    simp only [uvFlowerRightProjection_embedding, uvFlowerPathHead_height, uvFlowerPathTail_height] at heights
    omega

end
end EIGS

#print axioms EIGS.uvFlowerPathTail_height
#print axioms EIGS.uvFlowerPathHead_height
#print axioms EIGS.uvFlowerRuleGraph_endpoint_labels
#print axioms EIGS.uvFlowerRuleGraph_has_labeled_endpoint
#print axioms EIGS.uvFlowerRuleGraph_edges
#print axioms EIGS.uvFlowerRuleGraph_vertices
#print axioms EIGS.uvFlowerSystem_loopless
