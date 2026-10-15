import RequestProject.Section31.EIGSDHLRetentionWordMass

/-! A successful independent word block actually retains the terminal of
the edge present at its starting generation. This connects the iid block
event to the original sigma address genealogy, including arbitrary offsets. -/

namespace EIGS
noncomputable section

theorem dhlAddressOfLetters_block_descendant (sample : ℕ → Fin 2 × Fin 2) (offset width : ℕ) :
    xiAddressEdge (flowerSystem 2 2) (offset + width) (dhlAddressOfLetters sample) =
      dhlDescendantEdge offset width
        (xiAddressEdge (flowerSystem 2 2) offset (dhlAddressOfLetters sample))
        (independentWordBlock width offset 0 sample) := by
  induction width with
  | zero => rfl
  | succ width induction =>
      change (⟨dhlEdgeOfWord (offset + width) (fun position => sample position.val),
        sample (offset + width)⟩ : XiEdge (flowerSystem 2 2).toRuleData ((offset + width) + 1)) =
        ⟨dhlDescendantEdge offset width
            (xiAddressEdge (flowerSystem 2 2) offset (dhlAddressOfLetters sample))
            (independentWordBlock width offset 0 sample), sample (offset + width)⟩
      exact congrArg (fun parent : XiEdge (flowerSystem 2 2).toRuleData (offset + width) =>
        (⟨parent, sample (offset + width)⟩ : XiEdge (flowerSystem 2 2).toRuleData ((offset + width) + 1))) induction

theorem dhlLetters_retention_block_incident (sample : ℕ → Fin 2 × Fin 2) (offset width : ℕ)
    (success : independentWordBlock width offset 0 sample ∈ dhlGoodRetentionWords width false) :
    XiTail (flowerSystem 2 2) (offset + width)
        (xiAddressEdge (flowerSystem 2 2) (offset + width) (dhlAddressOfLetters sample)) =
        xiForward (flowerSystem 2 2) offset width
          (XiTail (flowerSystem 2 2) offset
            (xiAddressEdge (flowerSystem 2 2) offset (dhlAddressOfLetters sample))) ∨
    XiHead (flowerSystem 2 2) (offset + width)
        (xiAddressEdge (flowerSystem 2 2) (offset + width) (dhlAddressOfLetters sample)) =
        xiForward (flowerSystem 2 2) offset width
          (XiTail (flowerSystem 2 2) offset
            (xiAddressEdge (flowerSystem 2 2) offset (dhlAddressOfLetters sample))) := by
  obtain ⟨branches, wordEquality⟩ := success
  have terminal := dhlRetentionWord_preserves_terminal offset width
    (xiAddressEdge (flowerSystem 2 2) offset (dhlAddressOfLetters sample)) false branches
  rw [wordEquality, ← dhlAddressOfLetters_block_descendant] at terminal
  cases state : dhlRetentionEndpoint width false branches
  · left
    simpa only [dhlEdgeEndpoint, state, Bool.false_eq_true, if_false] using terminal
  · right
    simpa only [dhlEdgeEndpoint, state, if_true] using terminal

end
end EIGS

#print axioms EIGS.dhlAddressOfLetters_block_descendant
#print axioms EIGS.dhlLetters_retention_block_incident
