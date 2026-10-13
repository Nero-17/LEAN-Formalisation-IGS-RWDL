import RequestProject.Outlook.FourColourActiveCellTable

/-! Actual cell embeddings and component membership in the existing net.
The finite table is applied to genuine internal-vertex reachability flags. -/
namespace Outlook.FourColourActualCellComponents
open Cluster FourColourRuleAudit FourColourOrientationCandidate FourColourConditionalHierarchy
open FourColourCodingTree FourColourActiveCellTable

def actualChildEmbedding (depth : ℕ) (configuration : Conf (depth+1)) (edge : Fin 4) :
    (net depth (childConfiguration depth configuration edge)).V → (net (depth+1) configuration).V := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun impossible => Fin.elim0 impossible)))) edge
  · exact fun vertex => Sum.inl (Sum.inl vertex)
  · exact fun vertex => Sum.inl (TTN.seriesEmb (net depth configuration.1) (net depth configuration.2.1) vertex)
  · exact fun vertex => TTN.parEmb
      (TTN.seriesTTN (net depth configuration.1) (net depth configuration.2.1))
      (TTN.seriesTTN (net depth configuration.2.2.1) (net depth configuration.2.2.2)) (Sum.inl vertex)
  · exact fun vertex => TTN.parEmb
      (TTN.seriesTTN (net depth configuration.1) (net depth configuration.2.1))
      (TTN.seriesTTN (net depth configuration.2.2.1) (net depth configuration.2.2.2))
      (TTN.seriesEmb (net depth configuration.2.2.1) (net depth configuration.2.2.2) vertex)

noncomputable def sourceFlag (network : TTN) (vertex : network.V) : Bool := by
  classical
  exact decide (network.EdgePath network.a vertex)

noncomputable def targetFlag (network : TTN) (vertex : network.V) : Bool := by
  classical
  exact decide (network.EdgePath network.b vertex)

theorem connected_flags (network : TTN) (connected : network.EdgePath network.a network.b)
    (vertex : network.V) : sourceFlag network vertex = targetFlag network vertex := by
  classical
  unfold sourceFlag targetFlag
  rw [TTN.connected_components_iff network connected vertex]

theorem colourTest_iff_activeComponent (network : TTN) (parent : Fin 4) (reversed : Bool)
    (vertex : network.V) :
    orientedColourTest parent reversed (sourceFlag network vertex) (targetFlag network vertex)=true ↔
      TTN.activeComponent network parent reversed vertex := by
  classical
  fin_cases parent <;> cases reversed <;>
    simp [orientedColourTest, sourceFlag, targetFlag, TTN.activeComponent, TTN.boundaryComponent]

theorem actual_child_boundary_formula (depth : ℕ) (configuration : Conf (depth+1)) (edge : Fin 4)
    (vertex : (net depth (childConfiguration depth configuration edge)).V) :
    TTN.boundaryComponent (net (depth+1) configuration) (actualChildEmbedding depth configuration edge vertex) ↔
      childComponentTest 0 (firstGeneration depth configuration) edge
        (sourceFlag (net depth (childConfiguration depth configuration edge)) vertex)
        (targetFlag (net depth (childConfiguration depth configuration edge)) vertex)=true := by
  classical
  fin_cases edge
  all_goals
    simp only [actualChildEmbedding, Fin.mk_zero, Fin.cases_zero, Fin.cases_succ', childConfiguration, net]
  · rw [TTN.parallel_boundary_left_iff]
    simp [TTN.boundaryComponent, TTN.series_source_left_iff, TTN.series_sink_left_iff,
      actual_net_edgePath_iff_conn, childComponentTest, firstGeneration, sourceFlag, targetFlag]
  · rw [TTN.parallel_boundary_left_iff]
    simp [TTN.boundaryComponent, TTN.series_source_right_iff, TTN.series_sink_right_iff,
      actual_net_edgePath_iff_conn, childComponentTest, firstGeneration, sourceFlag, targetFlag]
  · rw [TTN.parallel_boundary_right_iff]
    simp [TTN.boundaryComponent, TTN.series_source_left_iff, TTN.series_sink_left_iff,
      actual_net_edgePath_iff_conn, childComponentTest, firstGeneration, sourceFlag, targetFlag]
  · rw [TTN.parallel_boundary_right_iff]
    simp [TTN.boundaryComponent, TTN.series_source_right_iff, TTN.series_sink_right_iff,
      actual_net_edgePath_iff_conn, childComponentTest, firstGeneration, sourceFlag, targetFlag]

theorem actual_child_source_formula (depth : ℕ) (configuration : Conf (depth+1))
    (disconnected : conn (depth+1) configuration=false) (edge : Fin 4)
    (vertex : (net depth (childConfiguration depth configuration edge)).V) :
    (net (depth+1) configuration).EdgePath (net (depth+1) configuration).a
      (actualChildEmbedding depth configuration edge vertex) ↔
      childComponentTest 2 (firstGeneration depth configuration) edge
        (sourceFlag (net depth (childConfiguration depth configuration edge)) vertex)
        (targetFlag (net depth (childConfiguration depth configuration edge)) vertex)=true := by
  classical
  have noPath : ¬(net (depth+1) configuration).EdgePath
      (net (depth+1) configuration).a (net (depth+1) configuration).b := by
    rw [actual_net_edgePath_iff_conn, disconnected]
    decide
  simp only [net, TTN.parallel_terminal_path_iff, not_or] at noPath
  fin_cases edge
  all_goals
    simp only [actualChildEmbedding, Fin.mk_zero, Fin.cases_zero, Fin.cases_succ', childConfiguration, net]
  · rw [TTN.parallel_source_left_iff _ _ noPath.1 noPath.2, TTN.series_source_left_iff]
    simp [childComponentTest, firstGeneration, sourceFlag]
  · rw [TTN.parallel_source_left_iff _ _ noPath.1 noPath.2, TTN.series_source_right_iff]
    simp [actual_net_edgePath_iff_conn, childComponentTest, firstGeneration, sourceFlag]
  · rw [TTN.parallel_source_right_iff _ _ noPath.1 noPath.2, TTN.series_source_left_iff]
    simp [childComponentTest, firstGeneration, sourceFlag]
  · rw [TTN.parallel_source_right_iff _ _ noPath.1 noPath.2, TTN.series_source_right_iff]
    simp [actual_net_edgePath_iff_conn, childComponentTest, firstGeneration, sourceFlag]

theorem actual_child_component_formula (depth : ℕ) (parent : Fin 4) (configuration : Conf (depth+1))
    (condition : configuration ∈ parentEvent (depth+1) parent) (edge : Fin 4)
    (vertex : (net depth (childConfiguration depth configuration edge)).V) :
    TTN.activeComponent (net (depth+1) configuration) parent false
      (actualChildEmbedding depth configuration edge vertex) ↔
      childComponentTest parent (firstGeneration depth configuration) edge
        (sourceFlag (net depth (childConfiguration depth configuration edge)) vertex)
        (targetFlag (net depth (childConfiguration depth configuration edge)) vertex)=true := by
  fin_cases parent
  · exact actual_child_boundary_formula depth configuration edge vertex
  · exact actual_child_boundary_formula depth configuration edge vertex
  · exact actual_child_source_formula depth configuration condition edge vertex
  · simp [TTN.activeComponent, childComponentTest]

theorem actual_child_active_iff (depth : ℕ) (parent : Fin 4) (configuration : Conf (depth+1))
    (condition : configuration ∈ parentEvent (depth+1) parent) (edge : Fin 4)
    (vertex : (net depth (childConfiguration depth configuration edge)).V) :
    TTN.activeComponent (net (depth+1) configuration) parent false
      (actualChildEmbedding depth configuration edge vertex) ↔
      TTN.activeComponent (net depth (childConfiguration depth configuration edge))
        (colour parent (conditionedOutcome parent (firstGeneration depth configuration)) edge)
        (reverseGreen parent (conditionedOutcome parent (firstGeneration depth configuration)) edge) vertex := by
  have consistent : openCell (firstGeneration depth configuration) edge=true →
      sourceFlag (net depth (childConfiguration depth configuration edge)) vertex =
        targetFlag (net depth (childConfiguration depth configuration edge)) vertex := by
    intro connected
    apply connected_flags
    rw [actual_net_edgePath_iff_conn, childConfiguration_conn]
    exact connected
  rw [actual_child_component_formula depth parent configuration condition edge vertex,
    all_actual_component_states parent (firstGeneration depth configuration) condition edge _ _ consistent,
    colourTest_iff_activeComponent]

end Outlook.FourColourActualCellComponents

#print axioms Outlook.FourColourActualCellComponents.connected_flags
#print axioms Outlook.FourColourActualCellComponents.actual_child_boundary_formula
#print axioms Outlook.FourColourActualCellComponents.actual_child_source_formula
#print axioms Outlook.FourColourActualCellComponents.actual_child_active_iff
