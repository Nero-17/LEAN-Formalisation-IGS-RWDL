import RequestProject.Outlook.FourColourGraphConnectivity

/-! Localization of genuine component membership under the existing TTN gluing
operations. These statements concern arbitrary actual internal vertices. -/
namespace Cluster.TTN

theorem series_source_left_iff (firstNetwork secondNetwork : TTN) (vertex : firstNetwork.V) :
    (seriesTTN firstNetwork secondNetwork).EdgePath (seriesTTN firstNetwork secondNetwork).a
      (Sum.inl vertex) ↔ firstNetwork.EdgePath firstNetwork.a vertex := by
  constructor
  · intro path
    exact series_path_project_left firstNetwork secondNetwork path
  · exact series_left_path firstNetwork secondNetwork

theorem series_sink_left_iff (firstNetwork secondNetwork : TTN) (vertex : firstNetwork.V) :
    (seriesTTN firstNetwork secondNetwork).EdgePath (seriesTTN firstNetwork secondNetwork).b
      (Sum.inl vertex) ↔ secondNetwork.EdgePath secondNetwork.a secondNetwork.b ∧
        firstNetwork.EdgePath firstNetwork.b vertex := by
  constructor
  · intro path
    have left := series_path_project_left firstNetwork secondNetwork path
    have right := series_path_project_right firstNetwork secondNetwork path
    change firstNetwork.EdgePath
      (seriesLeftRetraction firstNetwork secondNetwork (seriesEmb firstNetwork secondNetwork secondNetwork.b))
      vertex at left
    rw [seriesLeftRetraction_emb] at left
    change secondNetwork.EdgePath
      (seriesRightRetraction firstNetwork secondNetwork (seriesEmb firstNetwork secondNetwork secondNetwork.b))
      secondNetwork.a at right
    rw [seriesRightRetraction_emb] at right
    exact ⟨edgePath_symm right, left⟩
  · rintro ⟨right, left⟩
    have lifted := series_right_path firstNetwork secondNetwork (edgePath_symm right)
    have source : seriesEmb firstNetwork secondNetwork secondNetwork.a = Sum.inl firstNetwork.b := by
      simp [seriesEmb]
    rw [source] at lifted
    exact edgePath_trans lifted (series_left_path firstNetwork secondNetwork left)

theorem series_source_right_iff (firstNetwork secondNetwork : TTN) (vertex : secondNetwork.V) :
    (seriesTTN firstNetwork secondNetwork).EdgePath (seriesTTN firstNetwork secondNetwork).a
      (seriesEmb firstNetwork secondNetwork vertex) ↔
      firstNetwork.EdgePath firstNetwork.a firstNetwork.b ∧ secondNetwork.EdgePath secondNetwork.a vertex := by
  constructor
  · intro path
    have left := series_path_project_left firstNetwork secondNetwork path
    have right := series_path_project_right firstNetwork secondNetwork path
    change firstNetwork.EdgePath firstNetwork.a
      (seriesLeftRetraction firstNetwork secondNetwork (seriesEmb firstNetwork secondNetwork vertex)) at left
    rw [seriesLeftRetraction_emb] at left
    change secondNetwork.EdgePath secondNetwork.a
      (seriesRightRetraction firstNetwork secondNetwork (seriesEmb firstNetwork secondNetwork vertex)) at right
    rw [seriesRightRetraction_emb] at right
    exact ⟨left, right⟩
  · rintro ⟨left, right⟩
    have lifted := series_right_path firstNetwork secondNetwork right
    have source : seriesEmb firstNetwork secondNetwork secondNetwork.a = Sum.inl firstNetwork.b := by
      simp [seriesEmb]
    rw [source] at lifted
    exact edgePath_trans (series_left_path firstNetwork secondNetwork left) lifted

theorem series_sink_right_iff (firstNetwork secondNetwork : TTN) (vertex : secondNetwork.V) :
    (seriesTTN firstNetwork secondNetwork).EdgePath (seriesTTN firstNetwork secondNetwork).b
      (seriesEmb firstNetwork secondNetwork vertex) ↔ secondNetwork.EdgePath secondNetwork.b vertex := by
  constructor
  · intro path
    have projected := series_path_project_right firstNetwork secondNetwork path
    change secondNetwork.EdgePath
      (seriesRightRetraction firstNetwork secondNetwork (seriesEmb firstNetwork secondNetwork secondNetwork.b))
      (seriesRightRetraction firstNetwork secondNetwork (seriesEmb firstNetwork secondNetwork vertex)) at projected
    simpa only [seriesRightRetraction_emb] using projected
  · exact series_right_path firstNetwork secondNetwork

def parallelRegion (firstNetwork secondNetwork : TTN)
    (firstRegion : firstNetwork.V → Prop) (secondRegion : secondNetwork.V → Prop) :
    parV firstNetwork secondNetwork → Prop :=
  Sum.elim firstRegion (fun vertex => secondRegion vertex.1)

theorem parallelRegion_emb (firstNetwork secondNetwork : TTN)
    (firstRegion : firstNetwork.V → Prop) (secondRegion : secondNetwork.V → Prop)
    (source : firstRegion firstNetwork.a = secondRegion secondNetwork.a)
    (target : firstRegion firstNetwork.b = secondRegion secondNetwork.b) (vertex : secondNetwork.V) :
    parallelRegion firstNetwork secondNetwork firstRegion secondRegion
      (parEmb firstNetwork secondNetwork vertex) = secondRegion vertex := by
  unfold parEmb
  split
  · next equal => subst vertex; exact source
  · split
    · next equal => subst vertex; exact target
    · rfl

theorem parallelRegion_edges (firstNetwork secondNetwork : TTN)
    (firstRegion : firstNetwork.V → Prop) (secondRegion : secondNetwork.V → Prop)
    (source : firstRegion firstNetwork.a = secondRegion secondNetwork.a)
    (target : firstRegion firstNetwork.b = secondRegion secondNetwork.b)
    (firstEdges : ∀ edge, firstRegion (firstNetwork.tail edge)=firstRegion (firstNetwork.head edge))
    (secondEdges : ∀ edge, secondRegion (secondNetwork.tail edge)=secondRegion (secondNetwork.head edge))
    (edge : (parTTN firstNetwork secondNetwork).E) :
    parallelRegion firstNetwork secondNetwork firstRegion secondRegion ((parTTN firstNetwork secondNetwork).tail edge) =
      parallelRegion firstNetwork secondNetwork firstRegion secondRegion ((parTTN firstNetwork secondNetwork).head edge) := by
  rcases edge with edge | edge
  · exact firstEdges edge
  · change parallelRegion firstNetwork secondNetwork firstRegion secondRegion
      (parEmb firstNetwork secondNetwork (secondNetwork.tail edge)) =
        parallelRegion firstNetwork secondNetwork firstRegion secondRegion
          (parEmb firstNetwork secondNetwork (secondNetwork.head edge))
    rw [parallelRegion_emb _ _ _ _ source target, parallelRegion_emb _ _ _ _ source target]
    exact secondEdges edge

def boundaryComponent (network : TTN) (vertex : network.V) : Prop :=
  network.EdgePath network.a vertex ∨ network.EdgePath network.b vertex

@[simp] theorem boundaryComponent_source (network : TTN) : boundaryComponent network network.a :=
  Or.inl (edgePath_self _ _)

@[simp] theorem boundaryComponent_target (network : TTN) : boundaryComponent network network.b :=
  Or.inr (edgePath_self _ _)

theorem boundaryComponent_edge (network : TTN) (edge : network.E) :
    boundaryComponent network (network.tail edge) = boundaryComponent network (network.head edge) :=
  propext (or_congr (component_edge_iff network network.a edge) (component_edge_iff network network.b edge))

theorem parallel_boundary_left_iff (firstNetwork secondNetwork : TTN) (vertex : firstNetwork.V) :
    boundaryComponent (parTTN firstNetwork secondNetwork) (Sum.inl vertex) ↔
      boundaryComponent firstNetwork vertex := by
  constructor
  · intro membership
    have source : boundaryComponent firstNetwork firstNetwork.a = True := propext (iff_true_intro (boundaryComponent_source _))
    have target : boundaryComponent firstNetwork firstNetwork.b = True := propext (iff_true_intro (boundaryComponent_target _))
    have edges := parallelRegion_edges firstNetwork secondNetwork (boundaryComponent firstNetwork) (fun _ => True)
      source target (boundaryComponent_edge firstNetwork) (fun _ => rfl)
    rcases membership with path | path
    · have equal := edgePath_invariant (parTTN firstNetwork secondNetwork)
        (parallelRegion firstNetwork secondNetwork (boundaryComponent firstNetwork) (fun _ => True)) edges path
      change boundaryComponent firstNetwork firstNetwork.a = boundaryComponent firstNetwork vertex at equal
      exact equal ▸ boundaryComponent_source firstNetwork
    · have equal := edgePath_invariant (parTTN firstNetwork secondNetwork)
        (parallelRegion firstNetwork secondNetwork (boundaryComponent firstNetwork) (fun _ => True)) edges path
      change boundaryComponent firstNetwork firstNetwork.b = boundaryComponent firstNetwork vertex at equal
      exact equal ▸ boundaryComponent_target firstNetwork
  · rintro (path | path)
    · exact Or.inl (parallel_left_path firstNetwork secondNetwork path)
    · exact Or.inr (parallel_left_path firstNetwork secondNetwork path)

theorem parallel_boundary_right_iff (firstNetwork secondNetwork : TTN) (vertex : secondNetwork.V) :
    boundaryComponent (parTTN firstNetwork secondNetwork) (parEmb firstNetwork secondNetwork vertex) ↔
      boundaryComponent secondNetwork vertex := by
  have source : True = boundaryComponent secondNetwork secondNetwork.a := by simp
  have target : True = boundaryComponent secondNetwork secondNetwork.b := by simp
  constructor
  · intro membership
    have edges := parallelRegion_edges firstNetwork secondNetwork (fun _ => True) (boundaryComponent secondNetwork)
      source target (fun _ => rfl) (boundaryComponent_edge secondNetwork)
    rcases membership with path | path
    all_goals
      have equal := edgePath_invariant (parTTN firstNetwork secondNetwork)
        (parallelRegion firstNetwork secondNetwork (fun _ => True) (boundaryComponent secondNetwork)) edges path
      rw [parallelRegion_emb _ _ _ _ source target] at equal
      exact equal ▸ True.intro
  · rintro (path | path)
    · have lifted := parallel_right_path firstNetwork secondNetwork path
      have source : parEmb firstNetwork secondNetwork secondNetwork.a = Sum.inl firstNetwork.a := by simp [parEmb]
      rw [source] at lifted
      exact Or.inl lifted
    · have lifted := parallel_right_path firstNetwork secondNetwork path
      have target : parEmb firstNetwork secondNetwork secondNetwork.b = Sum.inl firstNetwork.b := by simp [parEmb, Ne.symm secondNetwork.hab]
      rw [target] at lifted
      exact Or.inr lifted

theorem parallel_source_left_iff (firstNetwork secondNetwork : TTN)
    (firstDisconnected : ¬firstNetwork.EdgePath firstNetwork.a firstNetwork.b)
    (secondDisconnected : ¬secondNetwork.EdgePath secondNetwork.a secondNetwork.b) (vertex : firstNetwork.V) :
    (parTTN firstNetwork secondNetwork).EdgePath (parTTN firstNetwork secondNetwork).a (Sum.inl vertex) ↔
      firstNetwork.EdgePath firstNetwork.a vertex := by
  constructor
  · intro path
    have source : firstNetwork.EdgePath firstNetwork.a firstNetwork.a =
        secondNetwork.EdgePath secondNetwork.a secondNetwork.a := by simp
    have target : firstNetwork.EdgePath firstNetwork.a firstNetwork.b =
        secondNetwork.EdgePath secondNetwork.a secondNetwork.b := by simp [firstDisconnected, secondDisconnected]
    have edges := parallelRegion_edges firstNetwork secondNetwork
      (firstNetwork.EdgePath firstNetwork.a) (secondNetwork.EdgePath secondNetwork.a) source target
      (fun edge => propext (component_edge_iff firstNetwork firstNetwork.a edge))
      (fun edge => propext (component_edge_iff secondNetwork secondNetwork.a edge))
    have equal := edgePath_invariant (parTTN firstNetwork secondNetwork)
      (parallelRegion firstNetwork secondNetwork (firstNetwork.EdgePath firstNetwork.a)
        (secondNetwork.EdgePath secondNetwork.a)) edges path
    change firstNetwork.EdgePath firstNetwork.a firstNetwork.a = firstNetwork.EdgePath firstNetwork.a vertex at equal
    exact equal ▸ edgePath_self firstNetwork firstNetwork.a
  · exact parallel_left_path firstNetwork secondNetwork

theorem parallel_source_right_iff (firstNetwork secondNetwork : TTN)
    (firstDisconnected : ¬firstNetwork.EdgePath firstNetwork.a firstNetwork.b)
    (secondDisconnected : ¬secondNetwork.EdgePath secondNetwork.a secondNetwork.b) (vertex : secondNetwork.V) :
    (parTTN firstNetwork secondNetwork).EdgePath (parTTN firstNetwork secondNetwork).a
      (parEmb firstNetwork secondNetwork vertex) ↔ secondNetwork.EdgePath secondNetwork.a vertex := by
  constructor
  · intro path
    have source : firstNetwork.EdgePath firstNetwork.a firstNetwork.a =
        secondNetwork.EdgePath secondNetwork.a secondNetwork.a := by simp
    have target : firstNetwork.EdgePath firstNetwork.a firstNetwork.b =
        secondNetwork.EdgePath secondNetwork.a secondNetwork.b := by simp [firstDisconnected, secondDisconnected]
    have edges := parallelRegion_edges firstNetwork secondNetwork
      (firstNetwork.EdgePath firstNetwork.a) (secondNetwork.EdgePath secondNetwork.a) source target
      (fun edge => propext (component_edge_iff firstNetwork firstNetwork.a edge))
      (fun edge => propext (component_edge_iff secondNetwork secondNetwork.a edge))
    have equal := edgePath_invariant (parTTN firstNetwork secondNetwork)
      (parallelRegion firstNetwork secondNetwork (firstNetwork.EdgePath firstNetwork.a)
        (secondNetwork.EdgePath secondNetwork.a)) edges path
    rw [parallelRegion_emb _ _ _ _ source target] at equal
    exact equal ▸ edgePath_self firstNetwork firstNetwork.a
  · intro path
    have lifted := parallel_right_path firstNetwork secondNetwork path
    have source : parEmb firstNetwork secondNetwork secondNetwork.a = Sum.inl firstNetwork.a := by simp [parEmb]
    rw [source] at lifted
    exact lifted

def activeFromTerminals (network : TTN) (sourceEnabled targetEnabled : Prop) (vertex : network.V) : Prop :=
  (sourceEnabled ∧ network.EdgePath network.a vertex) ∨
    (targetEnabled ∧ network.EdgePath network.b vertex)

theorem series_active_left_iff (firstNetwork secondNetwork : TTN)
    (sourceEnabled targetEnabled : Prop) (vertex : firstNetwork.V) :
    activeFromTerminals (seriesTTN firstNetwork secondNetwork) sourceEnabled targetEnabled (Sum.inl vertex) ↔
      activeFromTerminals firstNetwork sourceEnabled
        (targetEnabled ∧ secondNetwork.EdgePath secondNetwork.a secondNetwork.b) vertex := by
  simp only [activeFromTerminals, series_source_left_iff, series_sink_left_iff]
  tauto

theorem series_active_right_iff (firstNetwork secondNetwork : TTN)
    (sourceEnabled targetEnabled : Prop) (vertex : secondNetwork.V) :
    activeFromTerminals (seriesTTN firstNetwork secondNetwork) sourceEnabled targetEnabled
      (seriesEmb firstNetwork secondNetwork vertex) ↔
      activeFromTerminals secondNetwork
        (sourceEnabled ∧ firstNetwork.EdgePath firstNetwork.a firstNetwork.b) targetEnabled vertex := by
  simp only [activeFromTerminals, series_source_right_iff, series_sink_right_iff]
  tauto

end Cluster.TTN

#print axioms Cluster.TTN.series_source_left_iff
#print axioms Cluster.TTN.series_sink_left_iff
#print axioms Cluster.TTN.series_source_right_iff
#print axioms Cluster.TTN.series_sink_right_iff
#print axioms Cluster.TTN.parallel_boundary_left_iff
#print axioms Cluster.TTN.parallel_boundary_right_iff
#print axioms Cluster.TTN.parallel_source_left_iff
#print axioms Cluster.TTN.parallel_source_right_iff
#print axioms Cluster.TTN.series_active_left_iff
#print axioms Cluster.TTN.series_active_right_iff
