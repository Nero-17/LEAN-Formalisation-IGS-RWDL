import RequestProject.Section2DistanceRenormalization
import RequestProject.NonlinearCollatz
import Mathlib.Data.Matrix.Mul

/-! Attainment of the min-linear path eigenvalue by an actual path selection.

Every row is selected from a genuine simple terminal path. The min-linear
eigenvalue is realized by one selection and is at most every selection's
positive eigenvalue. Identifying these path counts with simple graph distances
and their iterated substitution is a separate combinatorial obligation.
-/

namespace EIGS.RuleSystem

open scoped BigOperators

variable {K : ℕ} (rules : EIGS.RuleSystem K)

noncomputable def pathSelectionMatrix
    (selection : ∀ colour, (rules.R colour).toSimpleGraph.Path
      (rules.βplus colour) (rules.βminus colour)) : Matrix (Fin K) (Fin K) ℝ :=
  fun ruleColour edgeColour => (rules.R ruleColour).pathColourCount (selection ruleColour) edgeColour

theorem pathRenormMap_le_selection
    (reachable : ∀ colour, (rules.R colour).toSimpleGraph.Reachable
      (rules.βplus colour) (rules.βminus colour))
    (selection : ∀ colour, (rules.R colour).toSimpleGraph.Path
      (rules.βplus colour) (rules.βminus colour))
    (vector : Fin K → ℝ) (vector_nonnegative : 0 ≤ vector) :
    (rules.pathRenormMap reachable).apply vector ≤
      (rules.pathSelectionMatrix selection).mulVec vector := by
  intro colour
  exact ciInf_le
    (((rules.R colour).pathThomsonData _ _ (reachable colour)).bddBelow_energy
      vector_nonnegative) (selection colour)

theorem pathRenormMap_coordinate_minimum
    (reachable : ∀ colour, (rules.R colour).toSimpleGraph.Reachable
      (rules.βplus colour) (rules.βminus colour))
    (vector : Fin K → ℝ) (vector_nonnegative : 0 ≤ vector) (colour : Fin K) :
    ∃ path : (rules.R colour).toSimpleGraph.Path (rules.βplus colour) (rules.βminus colour),
      (rules.pathRenormMap reachable).apply vector colour =
        ∑ edgeColour, (rules.R colour).pathColourCount path edgeColour * vector edgeColour := by
  classical
  let data := (rules.R colour).pathThomsonData _ _ (reachable colour)
  haveI : Nonempty data.F := data.nonempty
  letI : Fintype data.F := by
    change Fintype ((rules.R colour).toSimpleGraph.Path
      (rules.βplus colour) (rules.βminus colour))
    infer_instance
  obtain ⟨path, _, minimum⟩ := Finset.univ.exists_min_image
    (fun path : data.F => data.energy path vector) Finset.univ_nonempty
  refine ⟨path, le_antisymm (ciInf_le (data.bddBelow_energy vector_nonnegative) path) ?_⟩
  change data.energy path vector ≤ data.eval vector
  exact le_ciInf (fun other => minimum other (Finset.mem_univ other))

theorem path_eigenvalue_realized_and_minimal
    (colours_positive : 0 < K)
    (reachable : ∀ colour, (rules.R colour).toSimpleGraph.Reachable
      (rules.βplus colour) (rules.βminus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ∀ path : (rules.R ruleColour).toSimpleGraph.Walk
        (rules.βplus ruleColour) (rules.βminus ruleColour),
          path.IsPath → (rules.R ruleColour).UsesColour path edgeColour) :
    ∃ (vector : Fin K → ℝ) (rate : ℝ)
      (selection : ∀ colour, (rules.R colour).toSimpleGraph.Path
        (rules.βplus colour) (rules.βminus colour)),
      (∀ colour, 0 < vector colour) ∧ 0 < rate ∧ (∑ colour, vector colour) = 1 ∧
      (rules.pathRenormMap reachable).apply vector = rate • vector ∧
      (rules.pathSelectionMatrix selection).mulVec vector = rate • vector ∧
      ∀ (other : ∀ colour, (rules.R colour).toSimpleGraph.Path
          (rules.βplus colour) (rules.βminus colour))
        (otherVector : Fin K → ℝ) (otherRate : ℝ),
        (∀ colour, 0 < otherVector colour) →
        (rules.pathSelectionMatrix other).mulVec otherVector = otherRate • otherVector →
          rate ≤ otherRate := by
  classical
  obtain ⟨vector, rate, vector_positive, rate_positive, normalized, eigenpair⟩ :=
    (rules.pathRenormMap reachable).positive_eigenpair_of_strongly_positive colours_positive
      (rules.pathRenormMap_strongly_positive reachable distance_positive)
  choose selection minimizing using
    rules.pathRenormMap_coordinate_minimum reachable vector (fun colour => (vector_positive colour).le)
  refine ⟨vector, rate, selection, vector_positive, rate_positive, normalized, eigenpair, ?_, ?_⟩
  · ext colour
    exact (minimizing colour).symm.trans (congrFun eigenpair colour)
  · intro other otherVector otherRate other_positive other_eigenpair
    apply (rules.pathRenormMap reachable).eigenvalue_le_of_positive_supervector
      colours_positive vector otherVector rate otherRate vector_positive other_positive eigenpair
    exact (rules.pathRenormMap_le_selection reachable other otherVector
      (fun colour => (other_positive colour).le)).trans other_eigenpair.le

end EIGS.RuleSystem
