import RequestProject.Outlook.FourColourBranchingLaw

/-! Genuine graph connectivity of the existing TTN networks. Edge paths below
are proved equivalent to SimpleGraph.Reachable on the actual tail/head graph;
they are not a new recursive definition of cluster connectivity. -/
namespace Cluster.TTN

def underlyingGraph (network : TTN) : SimpleGraph network.V :=
  SimpleGraph.fromRel (fun first second =>
    ∃ edge : network.E, network.tail edge=first ∧ network.head edge=second)

def EdgePath (network : TTN) : network.V → network.V → Prop :=
  Relation.EqvGen (fun first second =>
    ∃ edge : network.E, network.tail edge=first ∧ network.head edge=second)

@[simp] theorem edgePath_self (network : TTN) (vertex : network.V) :
    network.EdgePath vertex vertex := Relation.EqvGen.refl vertex

theorem edgePath_edge (network : TTN) (edge : network.E) :
    network.EdgePath (network.tail edge) (network.head edge) :=
  Relation.EqvGen.rel _ _ ⟨edge, rfl, rfl⟩

theorem edgePath_symm {network : TTN} {first second : network.V}
    (path : network.EdgePath first second) : network.EdgePath second first :=
  Relation.EqvGen.symm _ _ path

theorem edgePath_trans {network : TTN} {first second third : network.V}
    (firstPath : network.EdgePath first second) (secondPath : network.EdgePath second third) :
    network.EdgePath first third := Relation.EqvGen.trans _ _ _ firstPath secondPath

theorem edgePath_iff_reachable (network : TTN) (first second : network.V) :
    network.EdgePath first second ↔ network.underlyingGraph.Reachable first second := by
  constructor
  · intro path
    induction path with
    | rel first second edge =>
        by_cases equal : first=second
        · subst second
          exact SimpleGraph.Reachable.refl first
        · exact SimpleGraph.Adj.reachable ⟨equal, Or.inl edge⟩
    | refl vertex => exact SimpleGraph.Reachable.refl vertex
    | symm _ _ _ induction => exact induction.symm
    | trans _ _ _ _ _ firstInduction secondInduction => exact firstInduction.trans secondInduction
  · rintro ⟨walk⟩
    induction walk with
    | nil => exact edgePath_self _ _
    | @cons first second third adjacent walk induction =>
        have step : network.EdgePath first second := by
          rcases adjacent.2 with edge | edge
          · exact Relation.EqvGen.rel _ _ edge
          · exact edgePath_symm (Relation.EqvGen.rel _ _ edge)
        exact edgePath_trans step induction

theorem edgePath_map (firstNetwork secondNetwork : TTN)
    (mapping : firstNetwork.V → secondNetwork.V)
    (edges : ∀ edge, secondNetwork.EdgePath (mapping (firstNetwork.tail edge))
      (mapping (firstNetwork.head edge))) {first second : firstNetwork.V}
    (path : firstNetwork.EdgePath first second) :
    secondNetwork.EdgePath (mapping first) (mapping second) := by
  induction path with
  | rel first second witness =>
      rcases witness with ⟨edge, rfl, rfl⟩
      exact edges edge
  | refl => exact edgePath_self _ _
  | symm _ _ _ induction => exact edgePath_symm induction
  | trans _ _ _ _ _ firstInduction secondInduction => exact edgePath_trans firstInduction secondInduction

theorem edgePath_invariant (network : TTN) {α : Sort*} (label : network.V → α)
    (edges : ∀ edge, label (network.tail edge)=label (network.head edge))
    {first second : network.V} (path : network.EdgePath first second) : label first=label second := by
  induction path with
  | rel first second witness =>
      rcases witness with ⟨edge, rfl, rfl⟩
      exact edges edge
  | refl => rfl
  | symm _ _ _ induction => exact induction.symm
  | trans _ _ _ _ _ firstInduction secondInduction => exact firstInduction.trans secondInduction

theorem component_edge_iff (network : TTN) (anchor : network.V) (edge : network.E) :
    network.EdgePath anchor (network.tail edge) ↔ network.EdgePath anchor (network.head edge) :=
  ⟨fun path => edgePath_trans path (edgePath_edge network edge),
    fun path => edgePath_trans path (edgePath_symm (edgePath_edge network edge))⟩

theorem series_left_path (firstNetwork secondNetwork : TTN) {first second : firstNetwork.V}
    (path : firstNetwork.EdgePath first second) :
    (seriesTTN firstNetwork secondNetwork).EdgePath (Sum.inl first) (Sum.inl second) := by
  refine edgePath_map firstNetwork (seriesTTN firstNetwork secondNetwork) Sum.inl ?_ path
  intro edge
  exact edgePath_edge (seriesTTN firstNetwork secondNetwork) (Sum.inl edge)

theorem series_right_path (firstNetwork secondNetwork : TTN) {first second : secondNetwork.V}
    (path : secondNetwork.EdgePath first second) :
    (seriesTTN firstNetwork secondNetwork).EdgePath (seriesEmb firstNetwork secondNetwork first)
      (seriesEmb firstNetwork secondNetwork second) := by
  refine edgePath_map secondNetwork (seriesTTN firstNetwork secondNetwork)
    (seriesEmb firstNetwork secondNetwork) ?_ path
  intro edge
  exact edgePath_edge (seriesTTN firstNetwork secondNetwork) (Sum.inr edge)

def seriesLeftRetraction (firstNetwork secondNetwork : TTN) : seriesV firstNetwork secondNetwork → firstNetwork.V :=
  Sum.elim id (fun _ => firstNetwork.b)

def seriesRightRetraction (firstNetwork secondNetwork : TTN) : seriesV firstNetwork secondNetwork → secondNetwork.V :=
  Sum.elim (fun _ => secondNetwork.a) Subtype.val

@[simp] theorem seriesLeftRetraction_emb (firstNetwork secondNetwork : TTN) (vertex : secondNetwork.V) :
    seriesLeftRetraction firstNetwork secondNetwork (seriesEmb firstNetwork secondNetwork vertex) =
      firstNetwork.b := by
  unfold seriesEmb
  split <;> rfl

@[simp] theorem seriesRightRetraction_emb (firstNetwork secondNetwork : TTN) (vertex : secondNetwork.V) :
    seriesRightRetraction firstNetwork secondNetwork (seriesEmb firstNetwork secondNetwork vertex) =
      vertex := by
  unfold seriesEmb
  split
  · next equal => exact equal.symm
  · rfl

theorem series_path_project_left (firstNetwork secondNetwork : TTN)
    {first second : (seriesTTN firstNetwork secondNetwork).V}
    (path : (seriesTTN firstNetwork secondNetwork).EdgePath first second) :
    firstNetwork.EdgePath (seriesLeftRetraction firstNetwork secondNetwork first)
      (seriesLeftRetraction firstNetwork secondNetwork second) := by
  apply edgePath_map _ firstNetwork (seriesLeftRetraction firstNetwork secondNetwork) _ path
  rintro (edge | edge)
  · exact edgePath_edge firstNetwork edge
  · change firstNetwork.EdgePath
      (seriesLeftRetraction firstNetwork secondNetwork (seriesEmb firstNetwork secondNetwork (secondNetwork.tail edge)))
      (seriesLeftRetraction firstNetwork secondNetwork (seriesEmb firstNetwork secondNetwork (secondNetwork.head edge)))
    simp only [seriesLeftRetraction_emb, edgePath_self]

theorem series_path_project_right (firstNetwork secondNetwork : TTN)
    {first second : (seriesTTN firstNetwork secondNetwork).V}
    (path : (seriesTTN firstNetwork secondNetwork).EdgePath first second) :
    secondNetwork.EdgePath (seriesRightRetraction firstNetwork secondNetwork first)
      (seriesRightRetraction firstNetwork secondNetwork second) := by
  apply edgePath_map _ secondNetwork (seriesRightRetraction firstNetwork secondNetwork) _ path
  rintro (edge | edge)
  · exact edgePath_self secondNetwork secondNetwork.a
  · change secondNetwork.EdgePath
      (seriesRightRetraction firstNetwork secondNetwork (seriesEmb firstNetwork secondNetwork (secondNetwork.tail edge)))
      (seriesRightRetraction firstNetwork secondNetwork (seriesEmb firstNetwork secondNetwork (secondNetwork.head edge)))
    simpa only [seriesRightRetraction_emb] using edgePath_edge secondNetwork edge

theorem series_terminal_path_iff (firstNetwork secondNetwork : TTN) :
    (seriesTTN firstNetwork secondNetwork).EdgePath
      (seriesTTN firstNetwork secondNetwork).a (seriesTTN firstNetwork secondNetwork).b ↔
      firstNetwork.EdgePath firstNetwork.a firstNetwork.b ∧
        secondNetwork.EdgePath secondNetwork.a secondNetwork.b := by
  constructor
  · intro path
    constructor
    · have projected := series_path_project_left firstNetwork secondNetwork path
      change firstNetwork.EdgePath firstNetwork.a
        (seriesLeftRetraction firstNetwork secondNetwork (seriesEmb firstNetwork secondNetwork secondNetwork.b)) at projected
      simpa only [seriesLeftRetraction_emb] using projected
    · have projected := series_path_project_right firstNetwork secondNetwork path
      change secondNetwork.EdgePath secondNetwork.a
        (seriesRightRetraction firstNetwork secondNetwork (seriesEmb firstNetwork secondNetwork secondNetwork.b)) at projected
      simpa only [seriesRightRetraction_emb] using projected
  · rintro ⟨firstPath, secondPath⟩
    have rightPath := series_right_path firstNetwork secondNetwork secondPath
    simp only [seriesEmb, dif_pos rfl] at rightPath
    exact edgePath_trans (series_left_path firstNetwork secondNetwork firstPath) rightPath

theorem parallel_left_path (firstNetwork secondNetwork : TTN) {first second : firstNetwork.V}
    (path : firstNetwork.EdgePath first second) :
    (parTTN firstNetwork secondNetwork).EdgePath (Sum.inl first) (Sum.inl second) := by
  refine edgePath_map firstNetwork (parTTN firstNetwork secondNetwork) Sum.inl ?_ path
  intro edge
  exact edgePath_edge (parTTN firstNetwork secondNetwork) (Sum.inl edge)

theorem parallel_right_path (firstNetwork secondNetwork : TTN) {first second : secondNetwork.V}
    (path : secondNetwork.EdgePath first second) :
    (parTTN firstNetwork secondNetwork).EdgePath (parEmb firstNetwork secondNetwork first)
      (parEmb firstNetwork secondNetwork second) := by
  refine edgePath_map secondNetwork (parTTN firstNetwork secondNetwork)
    (parEmb firstNetwork secondNetwork) ?_ path
  intro edge
  exact edgePath_edge (parTTN firstNetwork secondNetwork) (Sum.inr edge)

def parallelSourceRegion (firstNetwork secondNetwork : TTN) : parV firstNetwork secondNetwork → Prop :=
  Sum.elim (firstNetwork.EdgePath firstNetwork.a) (fun vertex => secondNetwork.EdgePath secondNetwork.a vertex.1)

theorem parallelSourceRegion_emb (firstNetwork secondNetwork : TTN)
    (firstDisconnected : ¬firstNetwork.EdgePath firstNetwork.a firstNetwork.b)
    (secondDisconnected : ¬secondNetwork.EdgePath secondNetwork.a secondNetwork.b)
    (vertex : secondNetwork.V) :
    parallelSourceRegion firstNetwork secondNetwork (parEmb firstNetwork secondNetwork vertex) =
      secondNetwork.EdgePath secondNetwork.a vertex := by
  by_cases source : vertex=secondNetwork.a
  · subst vertex
    simp [parEmb, parallelSourceRegion]
  · by_cases target : vertex=secondNetwork.b
    · subst vertex
      simp [parEmb, source, parallelSourceRegion, firstDisconnected, secondDisconnected]
    · simp [parEmb, source, target, parallelSourceRegion]

theorem parallel_terminal_path_iff (firstNetwork secondNetwork : TTN) :
    (parTTN firstNetwork secondNetwork).EdgePath
      (parTTN firstNetwork secondNetwork).a (parTTN firstNetwork secondNetwork).b ↔
      firstNetwork.EdgePath firstNetwork.a firstNetwork.b ∨
        secondNetwork.EdgePath secondNetwork.a secondNetwork.b := by
  constructor
  · intro path
    by_cases firstConnected : firstNetwork.EdgePath firstNetwork.a firstNetwork.b
    · exact Or.inl firstConnected
    by_cases secondConnected : secondNetwork.EdgePath secondNetwork.a secondNetwork.b
    · exact Or.inr secondConnected
    exfalso
    have edges : ∀ edge : (parTTN firstNetwork secondNetwork).E,
        parallelSourceRegion firstNetwork secondNetwork ((parTTN firstNetwork secondNetwork).tail edge) =
        parallelSourceRegion firstNetwork secondNetwork ((parTTN firstNetwork secondNetwork).head edge) := by
      rintro (edge | edge)
      · exact propext (component_edge_iff firstNetwork firstNetwork.a edge)
      · change parallelSourceRegion firstNetwork secondNetwork
          (parEmb firstNetwork secondNetwork (secondNetwork.tail edge)) =
            parallelSourceRegion firstNetwork secondNetwork
              (parEmb firstNetwork secondNetwork (secondNetwork.head edge))
        rw [parallelSourceRegion_emb _ _ firstConnected secondConnected,
          parallelSourceRegion_emb _ _ firstConnected secondConnected]
        exact propext (component_edge_iff secondNetwork secondNetwork.a edge)
    have equal := edgePath_invariant (parTTN firstNetwork secondNetwork)
      (parallelSourceRegion firstNetwork secondNetwork) edges path
    change firstNetwork.EdgePath firstNetwork.a firstNetwork.a =
      firstNetwork.EdgePath firstNetwork.a firstNetwork.b at equal
    exact firstConnected (equal ▸ edgePath_self firstNetwork firstNetwork.a)
  · rintro (path | path)
    · exact parallel_left_path firstNetwork secondNetwork path
    · have lifted := parallel_right_path firstNetwork secondNetwork path
      simpa only [parEmb, dif_pos rfl, dif_neg (Ne.symm secondNetwork.hab)] using lifted

end Cluster.TTN

namespace Cluster

theorem actual_net_edgePath_iff_conn (depth : ℕ) (configuration : Conf depth) :
    (net depth configuration).EdgePath (net depth configuration).a (net depth configuration).b ↔
      conn depth configuration=true := by
  induction depth with
  | zero =>
      cases configuration
      · change TTN.gapTTN.EdgePath false true ↔ false=true
        constructor
        · intro path
          have equal := TTN.edgePath_invariant TTN.gapTTN id (fun edge => nomatch edge) path
          exact equal
        · intro impossible
          cases impossible
      · change TTN.edgeTTN.EdgePath false true ↔ true=true
        exact ⟨fun _ => rfl, fun _ => TTN.edgePath_edge TTN.edgeTTN ()⟩
  | succ depth induction =>
      simp only [net, TTN.parallel_terminal_path_iff, TTN.series_terminal_path_iff,
        induction, conn_succ, Bool.or_eq_true, Bool.and_eq_true]

theorem actual_net_reachable_iff_conn (depth : ℕ) (configuration : Conf depth) :
    (net depth configuration).underlyingGraph.Reachable
      (net depth configuration).a (net depth configuration).b ↔ conn depth configuration=true := by
  rw [← TTN.edgePath_iff_reachable, actual_net_edgePath_iff_conn]

end Cluster

#print axioms Cluster.TTN.edgePath_iff_reachable
#print axioms Cluster.TTN.edgePath_map
#print axioms Cluster.TTN.edgePath_invariant
#print axioms Cluster.TTN.series_terminal_path_iff
#print axioms Cluster.TTN.parallel_terminal_path_iff
#print axioms Cluster.actual_net_reachable_iff_conn
