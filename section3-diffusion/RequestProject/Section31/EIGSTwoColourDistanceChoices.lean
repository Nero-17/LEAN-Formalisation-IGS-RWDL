import RequestProject.Section31.EIGSTwoColourRuleGraph
import RequestProject.Section2PathSelection

/-! Exact simple-terminal-path selection matrices of the literal Figure 3.
The finite enumeration below runs over actual graph paths, not over a proposed
list of row counts. Natural edge counts permit kernel decision of the finite
certificate; the final bridge identifies them with the existing real-valued
pathSelectionMatrix. Candidate until whole-file compilation is accepted. -/

namespace EIGS
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 12000000
set_option maxRecDepth 16000

instance twoColourNetwork_decidableAdj (colour : Fin 2) :
    DecidableRel (twoColourSystem.ruleNetwork colour).toSimpleGraph.Adj := by
  intro first second
  dsimp only [Network.toSimpleGraph, SimpleGraph.fromRel]
  infer_instance

abbrev TwoColourTerminalPathSelection :=
  ∀ colour : Fin 2, (twoColourSystem.ruleNetwork colour).toSimpleGraph.Path
    (twoColourSystem.plantPlus colour) (twoColourSystem.plantMinus colour)

def twoColourPathColourCountNat (colour : Fin 2)
    (path : (twoColourSystem.ruleNetwork colour).toSimpleGraph.Path
      (twoColourSystem.plantPlus colour) (twoColourSystem.plantMinus colour))
    (edgeColour : Fin 2) : ℕ :=
  (Finset.univ.filter fun edge : (twoColourSystem.ruleNetwork colour).E =>
    (twoColourSystem.ruleNetwork colour).color edge = edgeColour ∧
      s((twoColourSystem.ruleNetwork colour).tail edge,
        (twoColourSystem.ruleNetwork colour).head edge) ∈ path.val.edges).card

def twoColourPathSelectionMatrixNat (selection : TwoColourTerminalPathSelection) :
    Matrix (Fin 2) (Fin 2) ℕ :=
  fun ruleColour edgeColour => twoColourPathColourCountNat ruleColour (selection ruleColour) edgeColour

def twoColourDisplayedDistanceChoicesNat : Finset (Matrix (Fin 2) (Fin 2) ℕ) :=
  {!![1, 1; 1, 1], !![1, 1; 1, 2], !![3, 1; 1, 1],
    !![3, 1; 1, 2], !![1, 3; 1, 1], !![1, 3; 1, 2]}

theorem twoColourSystem_actual_distance_choices_nat :
    (Finset.univ : Finset TwoColourTerminalPathSelection).image twoColourPathSelectionMatrixNat =
      twoColourDisplayedDistanceChoicesNat := by
  decide

theorem twoColourSystem_actual_distance_choices_card :
    ((Finset.univ : Finset TwoColourTerminalPathSelection).image twoColourPathSelectionMatrixNat).card = 6 := by
  rw [twoColourSystem_actual_distance_choices_nat]
  decide

theorem twoColourPathColourCountNat_cast (colour : Fin 2)
    (path : (twoColourSystem.ruleNetwork colour).toSimpleGraph.Path
      (twoColourSystem.plantPlus colour) (twoColourSystem.plantMinus colour))
    (edgeColour : Fin 2) :
    (twoColourPathColourCountNat colour path edgeColour : ℝ) =
      (twoColourSystem.ruleNetwork colour).pathColourCount path edgeColour := by
  classical
  simp only [twoColourPathColourCountNat, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Network.pathColourCount]

def twoColourDistanceMatrixReal (matrix : Matrix (Fin 2) (Fin 2) ℕ) :
    Matrix (Fin 2) (Fin 2) ℝ := fun row column => matrix row column

theorem twoColourSystem_pathSelectionMatrix_from_actual_counts
    (selection : TwoColourTerminalPathSelection) :
    (twoColourSystem.connectedRuleSystem twoColourSystem_connected).pathSelectionMatrix selection =
      twoColourDistanceMatrixReal (twoColourPathSelectionMatrixNat selection) := by
  ext row column
  exact (twoColourPathColourCountNat_cast row (selection row) column).symm

theorem twoColourSystem_actual_distance_choices :
    Set.range (twoColourSystem.connectedRuleSystem twoColourSystem_connected).pathSelectionMatrix =
      twoColourDistanceMatrixReal '' (↑twoColourDisplayedDistanceChoicesNat :
        Set (Matrix (Fin 2) (Fin 2) ℕ)) := by
  classical
  ext matrix
  constructor
  · rintro ⟨selection, rfl⟩
    refine ⟨twoColourPathSelectionMatrixNat selection, ?_,
      (twoColourSystem_pathSelectionMatrix_from_actual_counts selection).symm⟩
    rw [← twoColourSystem_actual_distance_choices_nat]
    exact Finset.mem_image.mpr ⟨selection, Finset.mem_univ selection, rfl⟩
  · rintro ⟨naturalMatrix, membership, rfl⟩
    rw [← twoColourSystem_actual_distance_choices_nat] at membership
    obtain ⟨selection, _, equality⟩ := Finset.mem_image.mp membership
    refine ⟨selection, ?_⟩
    rw [twoColourSystem_pathSelectionMatrix_from_actual_counts, equality]

end
end EIGS

#print axioms EIGS.twoColourSystem_actual_distance_choices_nat
#print axioms EIGS.twoColourSystem_actual_distance_choices_card
#print axioms EIGS.twoColourSystem_pathSelectionMatrix_from_actual_counts
#print axioms EIGS.twoColourSystem_actual_distance_choices
