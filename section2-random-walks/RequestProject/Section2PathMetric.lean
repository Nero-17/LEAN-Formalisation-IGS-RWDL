import RequestProject.Section2PathSelection
import RequestProject.Section2Simplicity
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! The path min-linear map agrees with graph distance at unit edge length,
under the explicit chosen-orientation convention for simple coloured edges. -/

namespace EIGS.Network

open scoped BigOperators

variable {K : ℕ} (network : EIGS.Network K)

theorem colourConsistent_of_edgesUnique (unique_edges : network.EdgesUnique) :
    network.ColourConsistent := by
  intro first second same_endpoints
  exact congrArg network.color (unique_edges first second (Sym2.eq_iff.mp same_endpoints))

theorem sum_pathColourCount_eq_length (unique_edges : network.EdgesUnique)
    {source sink : network.V} (path : network.toSimpleGraph.Path source sink) :
    (∑ colour, network.pathColourCount path colour) = (path.val.length : ℝ) := by
  classical
  have count_card : (Finset.univ.filter (fun edge : network.E =>
      s(network.tail edge, network.head edge) ∈ path.val.edges)).card =
        path.val.edges.toFinset.card := by
    apply Finset.card_bij (fun edge _ => s(network.tail edge, network.head edge))
    · intro edge membership
      exact List.mem_toFinset.mpr (Finset.mem_filter.mp membership).2
    · intro first _ second _ same
      exact unique_edges first second (Sym2.eq_iff.mp same)
    · intro pair membership
      induction pair using Sym2.inductionOn with
      | _ first second =>
        have pair_mem := List.mem_toFinset.mp membership
        have adjacent := path.val.adj_of_mem_edges pair_mem
        rcases adjacent.2 with ⟨edge, tail_eq, head_eq⟩ | ⟨edge, tail_eq, head_eq⟩
        · refine ⟨edge, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · simpa only [tail_eq, head_eq] using pair_mem
          · simp only [tail_eq, head_eq]
        · refine ⟨edge, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · simpa only [tail_eq, head_eq, Sym2.eq_swap] using pair_mem
          · simp only [tail_eq, head_eq, Sym2.eq_swap]
  calc
    (∑ colour, network.pathColourCount path colour) =
        ∑ edge : network.E,
          if s(network.tail edge, network.head edge) ∈ path.val.edges then (1 : ℝ) else 0 := by
      rw [show (∑ colour, network.pathColourCount path colour) =
        ∑ edge : network.E, ∑ colour : Fin K,
          if network.color edge = colour ∧
            s(network.tail edge, network.head edge) ∈ path.val.edges then (1 : ℝ) else 0
          from Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro edge _
      by_cases membership : s(network.tail edge, network.head edge) ∈ path.val.edges
      · simp [membership, Finset.sum_ite_eq']
      · simp [membership]
    _ = ((Finset.univ.filter (fun edge : network.E =>
          s(network.tail edge, network.head edge) ∈ path.val.edges)).card : ℝ) := by simp
    _ = (path.val.edges.toFinset.card : ℝ) := by rw [count_card]
    _ = (path.val.length : ℝ) := by
      rw [List.toFinset_card_of_nodup path.property.isTrail.edges_nodup,
        SimpleGraph.Walk.length_edges]

theorem path_eval_unit_eq_graphDistance (unique_edges : network.EdgesUnique)
    (source sink : network.V) (reachable : network.toSimpleGraph.Reachable source sink) :
    (network.pathThomsonData source sink reachable).eval (fun _ => 1) =
      (network.toSimpleGraph.dist source sink : ℝ) := by
  classical
  let data := network.pathThomsonData source sink reachable
  have energy_length : ∀ path : data.F,
      data.energy path (fun _ => 1) = (path.val.length : ℝ) := by
    intro path
    simpa only [ThomsonData.energy, pathThomsonData, mul_one] using
      network.sum_pathColourCount_eq_length unique_edges path
  obtain ⟨shortest, simple_shortest, shortest_length⟩ := reachable.exists_path_of_dist
  apply le_antisymm
  · have bound := ciInf_le (data.bddBelow_energy (fun _ => zero_le_one))
      (⟨shortest, simple_shortest⟩ : data.F)
    change data.eval (fun _ => 1) ≤ (network.toSimpleGraph.dist source sink : ℝ)
    exact bound.trans_eq (by rw [energy_length, shortest_length])
  · apply le_ciInf
    intro path
    rw [energy_length]
    exact_mod_cast network.toSimpleGraph.dist_le path.val

end EIGS.Network

namespace EIGS.RuleSystem

open scoped BigOperators

variable {K : ℕ} (rules : EIGS.RuleSystem K)

theorem pathRenormMap_unit_eq_graphDistances
    (reachable : ∀ colour, (rules.R colour).toSimpleGraph.Reachable
      (rules.βplus colour) (rules.βminus colour))
    (unique_edges : ∀ colour, (rules.R colour).EdgesUnique) :
    (rules.pathRenormMap reachable).apply (fun _ => 1) = fun colour =>
      ((rules.R colour).toSimpleGraph.dist (rules.βplus colour) (rules.βminus colour) : ℝ) := by
  ext colour
  exact (rules.R colour).path_eval_unit_eq_graphDistance (unique_edges colour) _ _ (reachable colour)

end EIGS.RuleSystem
