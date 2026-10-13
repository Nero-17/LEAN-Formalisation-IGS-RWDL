import RequestProject.Section2DistancePositive
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting

/-! A min-linear renormalisation built from the actual rule terminal paths.

For chosen orientations of simple edges the coefficients below are precisely
the colour counts of each simple path. On the larger multigraph type they count
all edge identities with unordered endpoints on the path, so identification
with graph distance requires the simple-edge convention explicitly.
-/

namespace EIGS.Network

open scoped BigOperators

variable {K : ℕ} (network : EIGS.Network K)

noncomputable def pathColourCount {source sink : network.V}
    (path : network.toSimpleGraph.Path source sink) (colour : Fin K) : ℝ :=
  ∑ edge : network.E,
    if network.color edge = colour ∧
      s(network.tail edge, network.head edge) ∈ path.val.edges then 1 else 0

theorem pathColourCount_nonnegative {source sink : network.V}
    (path : network.toSimpleGraph.Path source sink) (colour : Fin K) :
    0 ≤ network.pathColourCount path colour := by
  apply Finset.sum_nonneg
  intro edge _
  split_ifs <;> norm_num

theorem one_le_pathColourCount_of_usesColour {source sink : network.V}
    (path : network.toSimpleGraph.Path source sink) (colour : Fin K)
    (uses_colour : network.UsesColour path.val colour) :
    1 ≤ network.pathColourCount path colour := by
  classical
  obtain ⟨selected, colour_eq, edge_mem⟩ := uses_colour
  have bound := Finset.single_le_sum (s := Finset.univ)
    (f := fun edge : network.E =>
      if network.color edge = colour ∧
        s(network.tail edge, network.head edge) ∈ path.val.edges then (1 : ℝ) else 0)
    (fun edge _ => by dsimp only; split_ifs <;> norm_num) (Finset.mem_univ selected)
  simpa only [pathColourCount, colour_eq, edge_mem, and_self, ↓reduceIte] using bound

noncomputable def pathThomsonData (source sink : network.V)
    (reachable : network.toSimpleGraph.Reachable source sink) : EIGS.ThomsonData K where
  F := network.toSimpleGraph.Path source sink
  nonempty := by
    obtain ⟨path, simple_path⟩ := reachable.exists_isPath
    exact ⟨⟨path, simple_path⟩⟩
  w := network.pathColourCount
  w_nonneg := network.pathColourCount_nonnegative

theorem path_eval_ge_coordinate (source sink : network.V)
    (reachable : network.toSimpleGraph.Reachable source sink)
    (colour : Fin K) (vector : Fin K → ℝ) (nonnegative : 0 ≤ vector)
    (all_paths_use : ∀ path : network.toSimpleGraph.Walk source sink,
      path.IsPath → network.UsesColour path colour) :
    vector colour ≤ (network.pathThomsonData source sink reachable).eval vector := by
  classical
  apply le_ciInf
  intro path
  have count_bound := network.one_le_pathColourCount_of_usesColour path colour
    (all_paths_use path.val path.property)
  calc
    vector colour ≤ network.pathColourCount path colour * vector colour := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right count_bound (nonnegative colour)
    _ ≤ (network.pathThomsonData source sink reachable).energy path vector := by
      exact Finset.single_le_sum (fun index _ => mul_nonneg
        (network.pathColourCount_nonnegative path index) (nonnegative index))
        (Finset.mem_univ colour)

end EIGS.Network

namespace EIGS.RuleSystem

open scoped BigOperators
open Filter Topology

variable {K : ℕ} (rules : EIGS.RuleSystem K)

noncomputable def pathRenormMap
    (reachable : ∀ colour, (rules.R colour).toSimpleGraph.Reachable
      (rules.βplus colour) (rules.βminus colour)) : EIGS.RenormMap K where
  coord := fun colour => (rules.R colour).pathThomsonData _ _ (reachable colour)

theorem pathRenormMap_strongly_positive
    (reachable : ∀ colour, (rules.R colour).toSimpleGraph.Reachable
      (rules.βplus colour) (rules.βminus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ∀ path : (rules.R ruleColour).toSimpleGraph.Walk
        (rules.βplus ruleColour) (rules.βminus ruleColour),
          path.IsPath → (rules.R ruleColour).UsesColour path edgeColour)
    (vector : Fin K → ℝ) (nonnegative : 0 ≤ vector) (nonzero : vector ≠ 0) :
    ∀ colour, 0 < (rules.pathRenormMap reachable).apply vector colour := by
  classical
  have some_positive : ∃ colour, 0 < vector colour := by
    by_contra none_positive
    push_neg at none_positive
    apply nonzero
    ext colour
    exact le_antisymm (none_positive colour) (nonnegative colour)
  obtain ⟨positive_colour, positive_coordinate⟩ := some_positive
  intro colour
  exact positive_coordinate.trans_le ((rules.R colour).path_eval_ge_coordinate _ _
    (reachable colour) positive_colour vector nonnegative (distance_positive colour positive_colour))

theorem pathRenormMap_normalized_eigenpair_exists_unique
    (colours_positive : 0 < K)
    (reachable : ∀ colour, (rules.R colour).toSimpleGraph.Reachable
      (rules.βplus colour) (rules.βminus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ∀ path : (rules.R ruleColour).toSimpleGraph.Walk
        (rules.βplus ruleColour) (rules.βminus ruleColour),
          path.IsPath → (rules.R ruleColour).UsesColour path edgeColour) :
    ∃! pair : (Fin K → ℝ) × ℝ,
      (∀ colour, 0 < pair.1 colour) ∧ 0 < pair.2 ∧ (∑ colour, pair.1 colour) = 1 ∧
        (rules.pathRenormMap reachable).apply pair.1 = pair.2 • pair.1 := by
  exact (rules.pathRenormMap reachable).existsUnique_positive_normalized_eigenpair
    colours_positive (rules.pathRenormMap_strongly_positive reachable distance_positive)

theorem pathRenormMap_normalized_iterate_limit
    (colours_positive : 0 < K)
    (reachable : ∀ colour, (rules.R colour).toSimpleGraph.Reachable
      (rules.βplus colour) (rules.βminus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ∀ path : (rules.R ruleColour).toSimpleGraph.Walk
        (rules.βplus ruleColour) (rules.βminus ruleColour),
          path.IsPath → (rules.R ruleColour).UsesColour path edgeColour) :
    ∃ (rate limit : ℝ) (vector : Fin K → ℝ),
      0 < rate ∧ 0 < limit ∧ (∀ colour, 0 < vector colour) ∧
      (∑ colour, vector colour) = 1 ∧
      (rules.pathRenormMap reachable).apply vector = rate • vector ∧
      Tendsto (fun level => fun colour =>
        (rules.pathRenormMap reachable).apply^[level] (fun _ => 1) colour / rate ^ level)
        atTop (𝓝 (limit • vector)) := by
  obtain ⟨vector, rate, vector_positive, rate_positive, normalized, eigenpair⟩ :=
    (rules.pathRenormMap reachable).positive_eigenpair_of_strongly_positive colours_positive
      (rules.pathRenormMap_strongly_positive reachable distance_positive)
  obtain ⟨limit, limit_positive, convergence⟩ :=
    (rules.pathRenormMap reachable).iterate_normalized_limit_of_strongly_positive
      colours_positive (rules.pathRenormMap_strongly_positive reachable distance_positive)
      vector_positive rate_positive normalized eigenpair
  exact ⟨rate, limit, vector, rate_positive, limit_positive, vector_positive,
    normalized, eigenpair, convergence⟩

end EIGS.RuleSystem
