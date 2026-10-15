import RequestProject.Section31.EIGSFlowerCanonicalRates
import RequestProject.Section31.EIGSEdgeAddressMeasure

/-! Actual child-letter coding for DHL(2,2). A letter is its actual branch
and segment edge. The recursive sigma edge construction is used directly,
including the backward orientation of the first branch. Probability-law
identification and retention words are separate successors. -/

namespace EIGS
open MeasureTheory
noncomputable section

def dhlEdgeOfWord : (level : ℕ) → (Fin level → Fin 2 × Fin 2) →
    XiEdge (flowerSystem 2 2).toRuleData level
  | 0, _ => ()
  | level + 1, word =>
      ⟨dhlEdgeOfWord level (fun position => word position.castSucc), word (Fin.last level)⟩

theorem dhlEdgeOfWord_injective (level : ℕ) : Function.Injective (dhlEdgeOfWord level) := by
  induction level with
  | zero => intro first second _; exact Subsingleton.elim _ _
  | succ level induction =>
      intro first second equality
      have parents := congrArg (xiEdgeParent (flowerSystem 2 2) level) equality
      have prefixes : (fun position : Fin level => first position.castSucc) =
          (fun position : Fin level => second position.castSucc) := induction parents
      have last : first (Fin.last level) = second (Fin.last level) :=
        congrArg (fun edge : XiEdge (flowerSystem 2 2).toRuleData (level + 1) =>
          (edge.2 : Fin 2 × Fin 2)) equality
      funext position
      exact Fin.lastCases last (fun earlier => congrFun prefixes earlier) position

theorem dhlEdgeOfWord_surjective (level : ℕ) : Function.Surjective (dhlEdgeOfWord level) := by
  induction level with
  | zero =>
      intro edge
      change Unit at edge
      cases edge
      exact ⟨fun position => Fin.elim0 position, rfl⟩
  | succ level induction =>
      intro edge
      obtain ⟨word, parent⟩ := induction edge.1
      refine ⟨Fin.lastCases (edge.2 : Fin 2 × Fin 2) word, ?_⟩
      have wordPrefixEquality : (fun position : Fin level =>
          Fin.lastCases (edge.2 : Fin 2 × Fin 2) word position.castSucc) = word := by
        funext position
        exact Fin.lastCases_castSucc position
      change (⟨dhlEdgeOfWord level (fun position : Fin level =>
        Fin.lastCases (edge.2 : Fin 2 × Fin 2) word position.castSucc),
          Fin.lastCases (edge.2 : Fin 2 × Fin 2) word (Fin.last level)⟩ :
            XiEdge (flowerSystem 2 2).toRuleData (level + 1)) = edge
      rw [wordPrefixEquality, Fin.lastCases_last, parent]
      cases edge
      rfl

def dhlWordEdgeEquiv (level : ℕ) :
    (Fin level → Fin 2 × Fin 2) ≃ XiEdge (flowerSystem 2 2).toRuleData level :=
  Equiv.ofBijective (dhlEdgeOfWord level) ⟨dhlEdgeOfWord_injective level, dhlEdgeOfWord_surjective level⟩

def dhlAddressOfLetters (sample : ℕ → Fin 2 × Fin 2) : XiEdgeAddress (flowerSystem 2 2) :=
  ⟨fun level => dhlEdgeOfWord level (fun position => sample position.val), fun _ => rfl⟩

theorem dhlAddressOfLetters_coordinate (sample : ℕ → Fin 2 × Fin 2) (level : ℕ) :
    xiAddressEdge (flowerSystem 2 2) level (dhlAddressOfLetters sample) =
      dhlEdgeOfWord level (fun position => sample position.val) := rfl

theorem measurable_dhlAddressOfLetters : Measurable dhlAddressOfLetters := by
  apply Measurable.subtype_mk
  apply measurable_pi_iff.mpr
  intro level
  exact (Measurable.of_discrete (f := dhlEdgeOfWord level)).comp
    (measurable_pi_iff.mpr (fun position : Fin level => measurable_pi_apply position.val))

end
end EIGS

#print axioms EIGS.dhlEdgeOfWord_injective
#print axioms EIGS.dhlEdgeOfWord_surjective
#print axioms EIGS.dhlAddressOfLetters_coordinate
#print axioms EIGS.measurable_dhlAddressOfLetters
