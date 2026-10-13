import Mathlib.Data.Nat.Find
import Mathlib.Order.Directed

/-! A compatible sequence of values on increasing, exhaustive subsets glues to
one actual function on their union. This is a construction, not a gluing axiom. -/

namespace IGS.Sec31

variable {Space : Type*} {Value : Type*}

theorem exists_nested_value_extension
    (levelSets : ℕ → Set Space) (setsIncreasing : Monotone levelSets)
    (setsExhaustive : ∀ vertex, ∃ level, vertex ∈ levelSets level)
    (levelValues : ∀ level, levelSets level → Value)
    (valuesCompatible : ∀ level (vertex : levelSets level),
      levelValues (level + 1) ⟨vertex.val, setsIncreasing (Nat.le_succ level) vertex.property⟩ =
        levelValues level vertex) :
    ∃ extension : Space → Value, ∀ level (vertex : levelSets level),
      extension vertex.val = levelValues level vertex := by
  classical
  have valuesAgree : ∀ first second, first ≤ second →
      ∀ vertex (firstMembership : vertex ∈ levelSets first)
        (secondMembership : vertex ∈ levelSets second),
      levelValues first ⟨vertex, firstMembership⟩ = levelValues second ⟨vertex, secondMembership⟩ := by
    intro first second comparison
    induction second, comparison using Nat.le_induction with
    | base => intro vertex firstMembership secondMembership; rfl
    | succ second comparison induction =>
        intro vertex firstMembership secondMembership
        have intermediateMembership := setsIncreasing comparison firstMembership
        exact (induction vertex firstMembership intermediateMembership).trans
          (valuesCompatible second ⟨vertex, intermediateMembership⟩).symm
  let chosenLevel : Space → ℕ := fun vertex => Classical.choose (setsExhaustive vertex)
  have chosenMembership : ∀ vertex, vertex ∈ levelSets (chosenLevel vertex) :=
    fun vertex => Classical.choose_spec (setsExhaustive vertex)
  refine ⟨fun vertex => levelValues (chosenLevel vertex) ⟨vertex, chosenMembership vertex⟩, ?_⟩
  intro level vertex
  have firstAgreement := valuesAgree (chosenLevel vertex.val) (max (chosenLevel vertex.val) level)
    (le_max_left _ _) vertex.val (chosenMembership vertex.val)
    (setsIncreasing (le_max_right _ _) vertex.property)
  have secondAgreement := valuesAgree level (max (chosenLevel vertex.val) level)
    (le_max_right _ _) vertex.val vertex.property
    (setsIncreasing (le_max_right _ _) vertex.property)
  exact firstAgreement.trans secondAgreement.symm

end IGS.Sec31
