import RequestProject.Section2AntiparallelSecondIterate
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

/-! Explicit original-standing-condition certificates for the accepted
antiparallel second-iterate counterexample. No frozen audit source is changed. -/

namespace EIGS.AntiparallelAudit

open scoped BigOperators Classical

theorem rule_source_middle (colour : Fin 1) :
    (ruleSG system colour).Adj Vertex.source Vertex.middle :=
  ⟨source_ne_middle, Or.inl ⟨(0 : Fin 4), rfl, rfl⟩⟩

theorem rule_middle_sink (colour : Fin 1) :
    (ruleSG system colour).Adj Vertex.middle Vertex.sink :=
  ⟨middle_ne_sink, Or.inl ⟨(2 : Fin 4), rfl, rfl⟩⟩

def ruleTerminalPath (colour : Fin 1) :
    (ruleSG system colour).Walk (system.plantPlus colour) (system.plantMinus colour) :=
  .cons (rule_source_middle colour) (.cons (rule_middle_sink colour) .nil)

theorem ruleTerminalPath_isPath (colour : Fin 1) : (ruleTerminalPath colour).IsPath := by
  rw [SimpleGraph.Walk.isPath_def]
  change [Vertex.source, Vertex.middle, Vertex.sink].Nodup
  decide

/-- Every individual arc has its underlying unoriented edge on the actual
simple terminal path, exactly the paper's canonicality requirement. -/
theorem every_rule_arc_on_terminal_simple_path (colour : Fin 1)
    (edge : (system.rule colour).E) :
    ∃ path : (ruleSG system colour).Walk (system.plantPlus colour) (system.plantMinus colour),
      path.IsPath ∧ s((system.rule colour).tail edge, (system.rule colour).head edge) ∈ path.edges := by
  refine ⟨ruleTerminalPath colour, ruleTerminalPath_isPath colour, ?_⟩
  change s(network.tail edge, network.head edge) ∈
    [s(Vertex.source, Vertex.middle), s(Vertex.middle, Vertex.sink)]
  fin_cases edge <;> simp [network, Sym2.eq_iff]

theorem rule_terminal_distance_two (colour : Fin 1) :
    (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) = 2 := by
  have distanceUpper := SimpleGraph.dist_le (ruleTerminalPath colour)
  have distanceLower := ((rules_connected colour) (system.plantPlus colour) (system.plantMinus colour)).one_lt_dist_of_ne_of_not_adj
    (system.plant_ne colour) (planting_nonadjacent colour)
  have pathLength : (ruleTerminalPath colour).length = 2 := rfl
  rw [pathLength] at distanceUpper
  omega

theorem degreeMatrix_entries_one (first second : Fin 1 ⊕ Fin 1) :
    degreeMatrix system first second = 1 := by
  fin_cases first <;> fin_cases second <;>
    dsimp only [degreeMatrix, Sum.elim] <;> norm_cast <;> decide

theorem degreeMatrix_primitive : (degreeMatrix system).IsPrimitive := by
  refine ⟨?_, 1, by omega, ?_⟩
  · intro first second
    rw [degreeMatrix_entries_one]
    norm_num
  · intro first second
    rw [pow_one, degreeMatrix_entries_one]
    norm_num

theorem massMatrix_entry_four : massMatrixR system.toRuleData 0 0 = 4 := by
  dsimp only [massMatrixR, massMatrix, EIGSData.toRuleData, system, network]
  norm_num [Finset.card_filter, Fin.sum_univ_succ]

/-- The original path, distance and primitive-degree conditions coexist with
the formally verified failure of simple-graph resistance renormalisation. -/
theorem original_standing_conditions_and_renormalization_failure :
    (∀ colour, (ruleSG system colour).Connected) ∧
    (∀ colour, (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) = 2) ∧
    (∀ colour (edge : (system.rule colour).E),
      ∃ path : (ruleSG system colour).Walk (system.plantPlus colour) (system.plantMinus colour),
        path.IsPath ∧ s((system.rule colour).tail edge, (system.rule colour).head edge) ∈ path.edges) ∧
    (degreeMatrix system).IsPrimitive ∧
    effResToBoundary (XiSimpleGraph system 2) (Finset.univ.erase secondSink) secondSource ≠
      simpleRulePsi (simpleRulePsi 1) := by
  exact ⟨rules_connected, rule_terminal_distance_two, every_rule_arc_on_terminal_simple_path,
    degreeMatrix_primitive, actual_second_iterate_ne_simple_rule_iteration⟩

end EIGS.AntiparallelAudit

#print axioms EIGS.AntiparallelAudit.every_rule_arc_on_terminal_simple_path
#print axioms EIGS.AntiparallelAudit.rule_terminal_distance_two
#print axioms EIGS.AntiparallelAudit.degreeMatrix_entries_one
#print axioms EIGS.AntiparallelAudit.degreeMatrix_primitive
#print axioms EIGS.AntiparallelAudit.massMatrix_entry_four
#print axioms EIGS.AntiparallelAudit.original_standing_conditions_and_renormalization_failure
