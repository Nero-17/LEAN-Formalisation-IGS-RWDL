import RequestProject.Section2WeightedSubstitution
import RequestProject.Section2PathMetric

/-! The finite simple-path colour-count minimum is the actual weighted walk
metric, under the explicit chosen-orientation convention. -/

namespace EIGS.Network

open scoped BigOperators Classical

variable {K : ℕ} (network : Network K)

theorem EdgeWalk.graph_edges_eq_map (loopless : network.Loopless)
    {source sink : network.V} (walk : network.EdgeWalk source sink) :
    (walk.toGraphWalk loopless).edges =
      walk.edges.map (fun edge => s(network.tail edge, network.head edge)) := by
  induction walk with
  | nil => rfl
  | @cons source next sink edge joins rest induction_hypothesis =>
    change s(source, next) :: (rest.toGraphWalk loopless).edges =
      s(network.tail edge, network.head edge) ::
        rest.edges.map (fun edge => s(network.tail edge, network.head edge))
    rw [induction_hypothesis]
    congr 1
    rcases joins with ⟨tail_eq, head_eq⟩ | ⟨tail_eq, head_eq⟩
    · simp only [tail_eq, head_eq]
    · simp only [tail_eq, head_eq, Sym2.eq_swap]

theorem EdgeWalk.edge_mem_graph_iff (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique) {source sink : network.V}
    (walk : network.EdgeWalk source sink) (edge : network.E) :
    s(network.tail edge, network.head edge) ∈ (walk.toGraphWalk loopless).edges ↔
      edge ∈ walk.edges := by
  rw [EdgeWalk.graph_edges_eq_map network loopless, List.mem_map]
  constructor
  · rintro ⟨candidate, membership, same_pair⟩
    have same_edge := unique_edges candidate edge (Sym2.eq_iff.mp same_pair)
    simpa only [same_edge] using membership
  · intro membership
    exact ⟨edge, membership, rfl⟩

private theorem sum_mem_list_le_sum_map {lengths : Fin K → ℝ}
    (nonnegative : 0 ≤ lengths) (edges : List network.E) :
    (∑ edge : network.E, if edge ∈ edges then lengths (network.color edge) else 0) ≤
      (edges.map (fun edge => lengths (network.color edge))).sum := by
  classical
  induction edges with
  | nil => simp
  | cons first rest induction_hypothesis =>
    have pointwise (edge : network.E) :
        (if edge ∈ first :: rest then lengths (network.color edge) else 0) ≤
          (if edge = first then lengths (network.color edge) else 0) +
            (if edge ∈ rest then lengths (network.color edge) else 0) := by
      by_cases same : edge = first
      · subst edge
        by_cases membership : first ∈ rest
        · have length_nonnegative := nonnegative (network.color first)
          change (0 : ℝ) ≤ lengths (network.color first) at length_nonnegative
          simpa [membership] using
            (show lengths (network.color first) ≤
              lengths (network.color first) + lengths (network.color first) by linarith)
        · simp [membership]
      · by_cases membership : edge ∈ rest <;> simp [List.mem_cons, same, membership]
    calc
      _ ≤ ∑ edge : network.E,
          ((if edge = first then lengths (network.color edge) else 0) +
            (if edge ∈ rest then lengths (network.color edge) else 0)) :=
        Finset.sum_le_sum (fun edge _ => pointwise edge)
      _ = lengths (network.color first) +
          ∑ edge : network.E, if edge ∈ rest then lengths (network.color edge) else 0 := by
        rw [Finset.sum_add_distrib]
        simp
      _ ≤ _ := by simpa only [List.map_cons, List.sum_cons] using
        add_le_add (le_refl (lengths (network.color first))) induction_hypothesis

private theorem sum_mem_list_eq_sum_map (lengths : Fin K → ℝ)
    (edges : List network.E) (nodup : edges.Nodup) :
    (∑ edge : network.E, if edge ∈ edges then lengths (network.color edge) else 0) =
      (edges.map (fun edge => lengths (network.color edge))).sum := by
  classical
  induction edges with
  | nil => simp
  | cons first rest induction_hypothesis =>
    obtain ⟨first_not_mem, rest_nodup⟩ := List.nodup_cons.mp nodup
    have pointwise (edge : network.E) :
        (if edge ∈ first :: rest then lengths (network.color edge) else 0) =
          (if edge = first then lengths (network.color edge) else 0) +
            (if edge ∈ rest then lengths (network.color edge) else 0) := by
      by_cases same : edge = first
      · subst edge
        simp [first_not_mem]
      · simp [List.mem_cons, same]
    simp_rw [pointwise]
    rw [Finset.sum_add_distrib]
    simp [induction_hypothesis rest_nodup]

theorem path_energy_eq_edge_sum {source sink : network.V}
    (reachable : network.toSimpleGraph.Reachable source sink)
    (path : network.toSimpleGraph.Path source sink) (lengths : Fin K → ℝ) :
    (network.pathThomsonData source sink reachable).energy path lengths =
      ∑ edge : network.E,
        if s(network.tail edge, network.head edge) ∈ path.val.edges then
          lengths (network.color edge) else 0 := by
  classical
  change (∑ colour, (∑ edge : network.E,
    if network.color edge = colour ∧
      s(network.tail edge, network.head edge) ∈ path.val.edges then (1 : ℝ) else 0) *
        lengths colour) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro edge _
  by_cases membership : s(network.tail edge, network.head edge) ∈ path.val.edges
  · simp [membership, Finset.sum_ite_eq']
  · simp [membership]

theorem path_energy_eq_ofGraphWalk_cost (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique) {source sink : network.V}
    (reachable : network.toSimpleGraph.Reachable source sink)
    (path : network.toSimpleGraph.Path source sink) (lengths : Fin K → ℝ) :
    (network.pathThomsonData source sink reachable).energy path lengths =
      (EdgeWalk.ofGraphWalk path.val).cost lengths := by
  let walk := EdgeWalk.ofGraphWalk path.val
  have graph_eq : walk.toGraphWalk loopless = path.val :=
    EdgeWalk.toGraphWalk_ofGraphWalk loopless path.val
  have nodup : walk.edges.Nodup := by
    apply List.Nodup.of_map (fun edge => s(network.tail edge, network.head edge))
    rw [← EdgeWalk.graph_edges_eq_map network loopless, graph_eq]
    exact path.property.isTrail.edges_nodup
  rw [network.path_energy_eq_edge_sum reachable path lengths]
  calc
    _ = ∑ edge : network.E, if edge ∈ walk.edges then lengths (network.color edge) else 0 := by
      apply Finset.sum_congr rfl
      intro edge _
      simp only [← graph_eq, EdgeWalk.edge_mem_graph_iff network loopless unique_edges]
    _ = (walk.edges.map (fun edge => lengths (network.color edge))).sum :=
      sum_mem_list_eq_sum_map network lengths walk.edges nodup
    _ = walk.cost lengths := (walk.cost_eq_sum_edges lengths).symm

theorem path_energy_toPath_le_walk_cost (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique) {source sink : network.V}
    (reachable : network.toSimpleGraph.Reachable source sink)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths)
    (walk : network.EdgeWalk source sink) :
    (network.pathThomsonData source sink reachable).energy
        (walk.toGraphWalk loopless).toPath lengths ≤ walk.cost lengths := by
  classical
  rw [network.path_energy_eq_edge_sum]
  have membership (edge : network.E)
      (member_path : s(network.tail edge, network.head edge) ∈
        (walk.toGraphWalk loopless).toPath.val.edges) : edge ∈ walk.edges :=
    (EdgeWalk.edge_mem_graph_iff network loopless unique_edges walk edge).mp
      ((walk.toGraphWalk loopless).edges_toPath_subset member_path)
  calc
    _ ≤ ∑ edge : network.E, if edge ∈ walk.edges then lengths (network.color edge) else 0 := by
      apply Finset.sum_le_sum
      intro edge _
      by_cases member_path : s(network.tail edge, network.head edge) ∈
          (walk.toGraphWalk loopless).toPath.val.edges
      · simp only [member_path, membership edge member_path, ↓reduceIte, le_refl]
      · simp only [member_path, ↓reduceIte]
        split_ifs
        · exact nonnegative _
        · exact le_rfl
    _ ≤ (walk.edges.map (fun edge => lengths (network.color edge))).sum :=
      sum_mem_list_le_sum_map network nonnegative walk.edges
    _ = walk.cost lengths := (walk.cost_eq_sum_edges lengths).symm

/-- Arbitrary nonnegative weighted path-count minimum agrees with the actual
network metric. Cycle removal costs nothing negative. -/
theorem path_eval_eq_weightedDistance (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique) (source sink : network.V)
    (reachable : network.toSimpleGraph.Reachable source sink)
    {lengths : Fin K → ℝ} (nonnegative : 0 ≤ lengths) :
    (network.pathThomsonData source sink reachable).eval lengths =
      network.weightedDistance lengths source sink := by
  letI : Nonempty (network.EdgeWalk source sink) :=
    ⟨EdgeWalk.ofGraphWalk (Classical.choice reachable)⟩
  letI : Nonempty (network.toSimpleGraph.Path source sink) :=
    (network.pathThomsonData source sink reachable).nonempty
  apply le_antisymm
  · apply le_ciInf
    intro walk
    exact (ciInf_le ((network.pathThomsonData source sink reachable).bddBelow_energy nonnegative)
      (walk.toGraphWalk loopless).toPath).trans
        (network.path_energy_toPath_le_walk_cost loopless unique_edges reachable nonnegative walk)
  · apply le_ciInf
    intro path
    rw [network.path_energy_eq_ofGraphWalk_cost loopless unique_edges reachable path lengths]
    exact network.weightedDistance_le_cost nonnegative (EdgeWalk.ofGraphWalk path.val)

end EIGS.Network
