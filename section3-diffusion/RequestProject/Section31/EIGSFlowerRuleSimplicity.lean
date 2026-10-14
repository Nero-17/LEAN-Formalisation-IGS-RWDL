import RequestProject.Section31.EIGSFlowerRuleGraph

/-! The actual parallel-chain flower has no repeated undirected edges
when each chain has at least two segments. Endpoint heights recover the
segment index; an interior endpoint recovers its branch. -/

namespace EIGS
open scoped Classical
noncomputable section

def flowerBranchLabel (branches segments : ℕ) :
    Bool ⊕ (Fin branches × Fin (segments - 1)) → Option (Fin branches)
  | Sum.inl _ => none
  | Sum.inr interior => some interior.1

theorem flowerPoint_branch_label (branches segments : ℕ) (branch : Fin branches)
    (position : Fin (segments + 1)) :
    flowerBranchLabel branches segments (flowerPoint branches segments branch position) = none ∨
      flowerBranchLabel branches segments (flowerPoint branches segments branch position) = some branch := by
  unfold flowerPoint
  split_ifs <;> simp [flowerBranchLabel]

theorem flowerGraph_endpoint_branch_labels (branches segments : ℕ)
    (edge : Fin branches × Fin segments) :
    (flowerBranchLabel branches segments ((flowerGraph branches segments).tail edge) = none ∨
      flowerBranchLabel branches segments ((flowerGraph branches segments).tail edge) = some edge.1) ∧
    (flowerBranchLabel branches segments ((flowerGraph branches segments).head edge) = none ∨
      flowerBranchLabel branches segments ((flowerGraph branches segments).head edge) = some edge.1) := by
  have start := flowerPoint_branch_label branches segments edge.1 ⟨edge.2.val, by omega⟩
  have finish := flowerPoint_branch_label branches segments edge.1 ⟨edge.2.val + 1, by omega⟩
  by_cases backwards : edge.1.val = 0
  · simpa only [flowerGraph, if_pos backwards, flowerEdgeStart, flowerEdgeEnd] using And.intro finish start
  · simpa only [flowerGraph, if_neg backwards, flowerEdgeStart, flowerEdgeEnd] using And.intro start finish

theorem flowerGraph_has_labeled_endpoint (branches segments : ℕ)
    (segmentsAtLeastTwo : 2 ≤ segments) (edge : Fin branches × Fin segments) :
    flowerBranchLabel branches segments ((flowerGraph branches segments).tail edge) = some edge.1 ∨
      flowerBranchLabel branches segments ((flowerGraph branches segments).head edge) = some edge.1 := by
  by_cases initialSegment : edge.2.val = 0
  · have finish : flowerBranchLabel branches segments (flowerEdgeEnd branches segments edge) = some edge.1 := by
      simp [flowerEdgeEnd, flowerPoint, flowerBranchLabel, initialSegment,
        show (1 : ℕ) ≠ segments by omega]
    by_cases backwards : edge.1.val = 0
    · left
      simpa only [flowerGraph, if_pos backwards] using finish
    · right
      simpa only [flowerGraph, if_neg backwards] using finish
  · have start : flowerBranchLabel branches segments (flowerEdgeStart branches segments edge) = some edge.1 := by
      simp [flowerEdgeStart, flowerPoint, flowerBranchLabel, initialSegment, Nat.ne_of_lt edge.2.isLt]
    by_cases backwards : edge.1.val = 0
    · right
      simpa only [flowerGraph, if_pos backwards] using start
    · left
      simpa only [flowerGraph, if_neg backwards] using start

theorem flowerGraph_minimum_endpoint_height (branches segments : ℕ)
    (edge : Fin branches × Fin segments) :
    min (flowerHeight branches segments ((flowerGraph branches segments).tail edge))
      (flowerHeight branches segments ((flowerGraph branches segments).head edge)) = edge.2.val := by
  rcases flowerGraph_edge_height branches segments edge with ⟨tail, head⟩ | ⟨tail, head⟩ <;>
    rw [tail, head] <;> omega

theorem flowerSystem_edgesUnique (branches segments : ℕ)
    (segmentsAtLeastTwo : 2 ≤ segments) (colour : Fin 1) :
    ((flowerSystem branches segments).ruleNetwork colour).EdgesUnique := by
  intro first second endpoints
  change (((flowerGraph branches segments).tail first = (flowerGraph branches segments).tail second ∧
      (flowerGraph branches segments).head first = (flowerGraph branches segments).head second) ∨
    ((flowerGraph branches segments).tail first = (flowerGraph branches segments).head second ∧
      (flowerGraph branches segments).head first = (flowerGraph branches segments).tail second)) at endpoints
  have branchEquality : first.1 = second.1 := by
    have supported := flowerGraph_has_labeled_endpoint branches segments segmentsAtLeastTwo first
    have secondLabels := flowerGraph_endpoint_branch_labels branches segments second
    have determine (label : Option (Fin branches))
        (secondLabel : label = none ∨ label = some second.1) (firstLabel : label = some first.1) :
        first.1 = second.1 := by
      rcases secondLabel with absent | present
      · rw [absent] at firstLabel
        cases firstLabel
      · exact Option.some.inj (firstLabel.symm.trans present)
    rcases endpoints with ⟨tail, head⟩ | ⟨tail, head⟩
    · rw [tail, head] at supported
      exact supported.elim (determine _ secondLabels.1) (determine _ secondLabels.2)
    · rw [tail, head] at supported
      exact supported.elim (determine _ secondLabels.2) (determine _ secondLabels.1)
  have minimumEquality :
      min (flowerHeight branches segments ((flowerGraph branches segments).tail first))
        (flowerHeight branches segments ((flowerGraph branches segments).head first)) =
      min (flowerHeight branches segments ((flowerGraph branches segments).tail second))
        (flowerHeight branches segments ((flowerGraph branches segments).head second)) := by
    rcases endpoints with ⟨tail, head⟩ | ⟨tail, head⟩
    · simp only [tail, head]
    · rw [tail, head]
      exact min_comm _ _
  have segmentEquality : first.2 = second.2 := Fin.ext
    ((flowerGraph_minimum_endpoint_height branches segments first).symm.trans
      (minimumEquality.trans (flowerGraph_minimum_endpoint_height branches segments second)))
  exact Prod.ext branchEquality segmentEquality

end
end EIGS

#print axioms EIGS.flowerPoint_branch_label
#print axioms EIGS.flowerGraph_endpoint_branch_labels
#print axioms EIGS.flowerGraph_has_labeled_endpoint
#print axioms EIGS.flowerGraph_minimum_endpoint_height
#print axioms EIGS.flowerSystem_edgesUnique
