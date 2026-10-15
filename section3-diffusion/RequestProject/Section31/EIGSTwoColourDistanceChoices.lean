import RequestProject.Section31.EIGSTwoColourRuleGraph
import RequestProject.Section2PathSelection

/-! Exact actual simple-terminal-path selection matrices for Figure 3.
The proof searches actual adjacency on vertex lists with repeated vertices
pruned before recursion. Completeness is proved by induction on each actual
simple Walk and its finite length; named actual path witnesses prove the
reverse inclusion. The original public natural/real matrix-family and card
endpoints are preserved. Only tiny list and Fin3-by-Fin2 certificates use
kernel decide. The earlier unmodified C441 attempt was deliberately
interrupted for cost, not recorded as a mathematical failure. Candidate. -/

namespace EIGS.TwoColourDistanceSupport
open scoped BigOperators
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000

section Search
variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]

def supports (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (visited : Finset Vertex) : ℕ → Vertex → Vertex → Finset (List Vertex)
  | 0, source, sink => if source = sink then {[source]} else ∅
  | fuel + 1, source, sink =>
      (if source = sink then {[source]} else ∅) ∪
        (Finset.univ.filter (fun next => graph.Adj source next ∧ next ∉ insert source visited)).biUnion
          (fun next => (supports graph (insert source visited) fuel next sink).image (List.cons source))

theorem support_mem_search (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (fuel : ℕ) (source sink : Vertex) (visited : Finset Vertex)
    (walk : graph.Walk source sink) (simple : walk.IsPath)
    (lengthBound : walk.length ≤ fuel)
    (avoids : ∀ vertex ∈ walk.support, vertex ∉ visited) :
    walk.support ∈ supports graph visited fuel source sink := by
  induction fuel generalizing source visited with
  | zero =>
      cases walk with
      | nil => simp [supports]
      | cons adjacent rest =>
          simp only [SimpleGraph.Walk.length_cons] at lengthBound
          omega
  | succ fuel induction =>
      cases walk with
      | nil => simp [supports]
      | cons adjacent rest =>
          have tailSimple := (SimpleGraph.Walk.cons_isPath_iff adjacent rest).mp simple
          have tailAvoids : ∀ vertex ∈ rest.support, vertex ∉ insert source visited := by
            intro vertex membership
            rw [Finset.mem_insert]
            rintro (equality | visitedMembership)
            · subst vertex
              exact tailSimple.2 membership
            · exact avoids vertex (by
                simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
                exact Or.inr membership) visitedMembership
          have tailLength : rest.length ≤ fuel := by
            simp only [SimpleGraph.Walk.length_cons] at lengthBound
            omega
          have tailMembership := induction _ (insert source visited) rest tailSimple.1 tailLength tailAvoids
          rw [supports]
          apply Finset.mem_union_right
          apply Finset.mem_biUnion.mpr
          refine ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, adjacent,
            tailAvoids _ rest.start_mem_support⟩, ?_⟩
          exact Finset.mem_image.mpr ⟨rest.support, tailMembership, rfl⟩

end Search

instance actualAdjDecidable (colour : Fin 2) :
    DecidableRel (twoColourSystem.ruleNetwork colour).toSimpleGraph.Adj := by
  intro first second
  dsimp only [Network.toSimpleGraph, SimpleGraph.fromRel]
  infer_instance

abbrev redGraph : SimpleGraph (Fin 5) := (twoColourSystem.ruleNetwork 0).toSimpleGraph
abbrev blueGraph : SimpleGraph (Fin 5) := (twoColourSystem.ruleNetwork 1).toSimpleGraph

theorem red_search_exact :
    supports redGraph ∅ 4 (0 : Fin 5) 4 =
      {[0, 1, 4], [0, 3, 4], [0, 1, 2, 3, 4], [0, 3, 2, 1, 4]} := by
  decide

theorem blue_search_exact :
    supports blueGraph ∅ 4 (0 : Fin 5) 4 = {[0, 3, 4], [0, 1, 2, 4]} := by
  decide

theorem red_path_support_exhaustive (path : redGraph.Path (0 : Fin 5) 4) :
    path.val.support ∈ ({[0, 1, 4], [0, 3, 4], [0, 1, 2, 3, 4], [0, 3, 2, 1, 4]} : Finset (List (Fin 5))) := by
  have bound : path.val.length ≤ 4 := by
    have strict := path.property.length_lt
    change path.val.length < 5 at strict
    omega
  have membership := support_mem_search redGraph 4 (0 : Fin 5) 4 ∅ path.val path.property bound
    (by intro vertex _; simp)
  rw [red_search_exact] at membership
  exact membership

theorem blue_path_support_exhaustive (path : blueGraph.Path (0 : Fin 5) 4) :
    path.val.support ∈ ({[0, 3, 4], [0, 1, 2, 4]} : Finset (List (Fin 5))) := by
  have bound : path.val.length ≤ 4 := by
    have strict := path.property.length_lt
    change path.val.length < 5 at strict
    omega
  have membership := support_mem_search blueGraph 4 (0 : Fin 5) 4 ∅ path.val path.property bound
    (by intro vertex _; simp)
  rw [blue_search_exact] at membership
  exact membership

def redPath11 : redGraph.Path (0 : Fin 5) 4 := by
  refine ⟨.cons (v := (1 : Fin 5)) (by decide) (.cons (v := (4 : Fin 5)) (by decide) .nil), ?_⟩
  apply SimpleGraph.Walk.IsPath.mk'
  change ([0, 1, 4] : List (Fin 5)).Nodup
  decide

def redPath31 : redGraph.Path (0 : Fin 5) 4 := by
  refine ⟨.cons (v := (1 : Fin 5)) (by decide)
    (.cons (v := (2 : Fin 5)) (by decide)
      (.cons (v := (3 : Fin 5)) (by decide) (.cons (v := (4 : Fin 5)) (by decide) .nil))), ?_⟩
  apply SimpleGraph.Walk.IsPath.mk'
  change ([0, 1, 2, 3, 4] : List (Fin 5)).Nodup
  decide

def redPath13 : redGraph.Path (0 : Fin 5) 4 := by
  refine ⟨.cons (v := (3 : Fin 5)) (by decide)
    (.cons (v := (2 : Fin 5)) (by decide)
      (.cons (v := (1 : Fin 5)) (by decide) (.cons (v := (4 : Fin 5)) (by decide) .nil))), ?_⟩
  apply SimpleGraph.Walk.IsPath.mk'
  change ([0, 3, 2, 1, 4] : List (Fin 5)).Nodup
  decide

def bluePath11 : blueGraph.Path (0 : Fin 5) 4 := by
  refine ⟨.cons (v := (3 : Fin 5)) (by decide) (.cons (v := (4 : Fin 5)) (by decide) .nil), ?_⟩
  apply SimpleGraph.Walk.IsPath.mk'
  change ([0, 3, 4] : List (Fin 5)).Nodup
  decide

def bluePath12 : blueGraph.Path (0 : Fin 5) 4 := by
  refine ⟨.cons (v := (1 : Fin 5)) (by decide)
    (.cons (v := (2 : Fin 5)) (by decide) (.cons (v := (4 : Fin 5)) (by decide) .nil)), ?_⟩
  apply SimpleGraph.Walk.IsPath.mk'
  change ([0, 1, 2, 4] : List (Fin 5)).Nodup
  decide

def supportColourCounts (colour : Fin 2) (vertices : List (Fin 5)) (edgeColour : Fin 2) : ℕ :=
  (Finset.univ.filter (fun edge : (twoColourSystem.ruleNetwork colour).E =>
    (twoColourSystem.ruleNetwork colour).color edge = edgeColour ∧
      s((twoColourSystem.ruleNetwork colour).tail edge, (twoColourSystem.ruleNetwork colour).head edge) ∈
        List.zipWith (fun first second => s(first, second)) vertices vertices.tail)).card

theorem actual_counts_from_support (colour : Fin 2)
    (path : (twoColourSystem.ruleNetwork colour).toSimpleGraph.Path
      (twoColourSystem.plantPlus colour) (twoColourSystem.plantMinus colour)) (edgeColour : Fin 2) :
    (supportColourCounts colour path.val.support edgeColour : ℝ) =
      (twoColourSystem.ruleNetwork colour).pathColourCount path edgeColour := by
  classical
  simp only [supportColourCounts, Network.pathColourCount, Finset.card_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    SimpleGraph.Walk.edges_eq_zipWith_support]
  apply Finset.sum_congr rfl
  intro edge _
  split_ifs <;> first | rfl | contradiction

theorem red_actual_count_rows (path : redGraph.Path (0 : Fin 5) 4) :
    supportColourCounts 0 path.val.support ∈ ({![1, 1], ![3, 1], ![1, 3]} : Finset (Fin 2 → ℕ)) := by
  have membership := red_path_support_exhaustive path
  simp only [Finset.mem_insert, Finset.mem_singleton] at membership
  rcases membership with equality | equality | equality | equality
  all_goals rw [equality]; decide

theorem blue_actual_count_rows (path : blueGraph.Path (0 : Fin 5) 4) :
    supportColourCounts 1 path.val.support ∈ ({![1, 1], ![1, 2]} : Finset (Fin 2 → ℕ)) := by
  have membership := blue_path_support_exhaustive path
  simp only [Finset.mem_insert, Finset.mem_singleton] at membership
  rcases membership with equality | equality
  all_goals rw [equality]; decide

theorem five_actual_row_witnesses :
    supportColourCounts 0 redPath11.val.support = ![1, 1] ∧
    supportColourCounts 0 redPath31.val.support = ![3, 1] ∧
    supportColourCounts 0 redPath13.val.support = ![1, 3] ∧
    supportColourCounts 1 bluePath11.val.support = ![1, 1] ∧
    supportColourCounts 1 bluePath12.val.support = ![1, 2] := by
  decide

end EIGS.TwoColourDistanceSupport


namespace EIGS
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000

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

def twoColourDistanceSelectionWitness (redChoice : Fin 3) (blueChoice : Fin 2) :
    TwoColourTerminalPathSelection :=
  Fin.cases (![TwoColourDistanceSupport.redPath11, TwoColourDistanceSupport.redPath31,
      TwoColourDistanceSupport.redPath13] redChoice)
    (Fin.cases (![TwoColourDistanceSupport.bluePath11, TwoColourDistanceSupport.bluePath12] blueChoice)
      (fun impossible => impossible.elim0))

def twoColourDistanceChoiceMatrix (redChoice : Fin 3) (blueChoice : Fin 2) : Matrix (Fin 2) (Fin 2) ℕ :=
  ![(![![1, 1], ![3, 1], ![1, 3]] redChoice), (![![1, 1], ![1, 2]] blueChoice)]

theorem twoColourDistanceSelectionWitness_matrix :
    ∀ redChoice : Fin 3, ∀ blueChoice : Fin 2,
      twoColourPathSelectionMatrixNat (twoColourDistanceSelectionWitness redChoice blueChoice) =
        twoColourDistanceChoiceMatrix redChoice blueChoice := by
  decide

theorem twoColourSystem_actual_distance_choices_nat :
    (Finset.univ : Finset TwoColourTerminalPathSelection).image twoColourPathSelectionMatrixNat =
      twoColourDisplayedDistanceChoicesNat := by
  ext matrix
  constructor
  · intro membership
    obtain ⟨selection, _, rfl⟩ := Finset.mem_image.mp membership
    have rows (colour : Fin 2) : twoColourPathSelectionMatrixNat selection colour =
        TwoColourDistanceSupport.supportColourCounts colour (selection colour).val.support := by
      funext edgeColour
      unfold twoColourPathSelectionMatrixNat twoColourPathColourCountNat
        TwoColourDistanceSupport.supportColourCounts
      rw [SimpleGraph.Walk.edges_eq_zipWith_support]
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro edge _
      rfl
    have matrixRows : twoColourPathSelectionMatrixNat selection =
        ![TwoColourDistanceSupport.supportColourCounts 0 (selection 0).val.support,
          TwoColourDistanceSupport.supportColourCounts 1 (selection 1).val.support] := by
      funext colour
      fin_cases colour
      · exact rows 0
      · exact rows 1
    have redRows := TwoColourDistanceSupport.red_actual_count_rows (selection 0)
    have blueRows := TwoColourDistanceSupport.blue_actual_count_rows (selection 1)
    simp only [Finset.mem_insert, Finset.mem_singleton] at redRows blueRows
    rcases redRows with redEquality | redEquality | redEquality
    all_goals rcases blueRows with blueEquality | blueEquality
    all_goals rw [matrixRows, redEquality, blueEquality]; decide
  · intro membership
    simp only [twoColourDisplayedDistanceChoicesNat, Finset.mem_insert, Finset.mem_singleton] at membership
    rcases membership with equality | equality | equality | equality | equality | equality
    · exact Finset.mem_image.mpr ⟨twoColourDistanceSelectionWitness 0 0, Finset.mem_univ _,
        (twoColourDistanceSelectionWitness_matrix 0 0).trans equality.symm⟩
    · exact Finset.mem_image.mpr ⟨twoColourDistanceSelectionWitness 0 1, Finset.mem_univ _,
        (twoColourDistanceSelectionWitness_matrix 0 1).trans equality.symm⟩
    · exact Finset.mem_image.mpr ⟨twoColourDistanceSelectionWitness 1 0, Finset.mem_univ _,
        (twoColourDistanceSelectionWitness_matrix 1 0).trans equality.symm⟩
    · exact Finset.mem_image.mpr ⟨twoColourDistanceSelectionWitness 1 1, Finset.mem_univ _,
        (twoColourDistanceSelectionWitness_matrix 1 1).trans equality.symm⟩
    · exact Finset.mem_image.mpr ⟨twoColourDistanceSelectionWitness 2 0, Finset.mem_univ _,
        (twoColourDistanceSelectionWitness_matrix 2 0).trans equality.symm⟩
    · exact Finset.mem_image.mpr ⟨twoColourDistanceSelectionWitness 2 1, Finset.mem_univ _,
        (twoColourDistanceSelectionWitness_matrix 2 1).trans equality.symm⟩

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
  ext matrix
  constructor
  · rintro ⟨selection, rfl⟩
    change TwoColourTerminalPathSelection at selection
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
