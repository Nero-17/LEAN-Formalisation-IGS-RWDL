import RequestProject.Section2PathSelection
import RequestProject.Section2DistanceScale
import RequestProject.Section2SpectralRadius

/-! The minimum over genuine terminal-path selection matrices uses their usual
complex spectral radii, rather than a separately chosen positive eigenvalue. -/

namespace EIGS.RuleSystem

open scoped BigOperators
open Filter Topology

variable {K : ℕ} (rules : EIGS.RuleSystem K)

noncomputable def pathMinimumSpectralRadius : ℝ :=
  ⨅ selection : ∀ colour, (rules.R colour).toSimpleGraph.Path
    (rules.βplus colour) (rules.βminus colour),
      EIGS.realMatrixSpectralRadius (rules.pathSelectionMatrix selection)

theorem pathSelectionMatrix_positive
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ∀ path : (rules.R ruleColour).toSimpleGraph.Walk
        (rules.βplus ruleColour) (rules.βminus ruleColour),
          path.IsPath → (rules.R ruleColour).UsesColour path edgeColour)
    (selection : ∀ colour, (rules.R colour).toSimpleGraph.Path
      (rules.βplus colour) (rules.βminus colour)) :
    ∀ row column, 0 < rules.pathSelectionMatrix selection row column := by
  intro row column
  exact zero_lt_one.trans_le ((rules.R row).one_le_pathColourCount_of_usesColour
    (selection row) column (distance_positive row column
      (selection row).val (selection row).property))

theorem pathMinimumSpectralRadius_le
    (selection : ∀ colour, (rules.R colour).toSimpleGraph.Path
      (rules.βplus colour) (rules.βminus colour)) :
    rules.pathMinimumSpectralRadius ≤
      EIGS.realMatrixSpectralRadius (rules.pathSelectionMatrix selection) := by
  apply ciInf_le _ selection
  exact ⟨0, by rintro value ⟨other, rfl⟩; exact ENNReal.toReal_nonneg⟩

theorem path_spectral_minimum_eigenpair_and_attainment
    (colours_positive : 0 < K)
    (reachable : ∀ colour, (rules.R colour).toSimpleGraph.Reachable
      (rules.βplus colour) (rules.βminus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ∀ path : (rules.R ruleColour).toSimpleGraph.Walk
        (rules.βplus ruleColour) (rules.βminus ruleColour),
          path.IsPath → (rules.R ruleColour).UsesColour path edgeColour) :
    ∃ (vector : Fin K → ℝ)
      (selection : ∀ colour, (rules.R colour).toSimpleGraph.Path
        (rules.βplus colour) (rules.βminus colour)),
      (∀ colour, 0 < vector colour) ∧ 0 < rules.pathMinimumSpectralRadius ∧
      (∑ colour, vector colour) = 1 ∧
      (rules.pathRenormMap reachable).apply vector = rules.pathMinimumSpectralRadius • vector ∧
      EIGS.realMatrixSpectralRadius (rules.pathSelectionMatrix selection) =
        rules.pathMinimumSpectralRadius := by
  obtain ⟨vector, rate, selection, vector_positive, rate_positive, normalized,
    eigenpair, selection_eigenpair, minimal⟩ :=
    rules.path_eigenvalue_realized_and_minimal colours_positive reachable distance_positive
  letI : Nonempty (∀ colour, (rules.R colour).toSimpleGraph.Path
      (rules.βplus colour) (rules.βminus colour)) := ⟨selection⟩
  have selected_radius : EIGS.realMatrixSpectralRadius
      (rules.pathSelectionMatrix selection) = rate :=
    EIGS.realMatrixSpectralRadius_eq_positive_eigenvalue colours_positive _
      (fun row column => (rules.pathSelectionMatrix_positive distance_positive selection row column).le)
      vector rate vector_positive rate_positive.le selection_eigenpair
  have rate_le_minimum : rate ≤ rules.pathMinimumSpectralRadius := by
    apply le_ciInf
    intro other
    obtain ⟨other_vector, other_positive, _, _, other_eigenpair⟩ :=
      EIGS.positive_matrix_spectralRadius_eigenpair colours_positive
        (rules.pathSelectionMatrix other) (rules.pathSelectionMatrix_positive distance_positive other)
    exact minimal other other_vector _ other_positive other_eigenpair
  have minimum_eq : rules.pathMinimumSpectralRadius = rate :=
    le_antisymm ((rules.pathMinimumSpectralRadius_le selection).trans selected_radius.le)
      rate_le_minimum
  exact ⟨vector, selection, vector_positive, minimum_eq.symm ▸ rate_positive, normalized,
    minimum_eq.symm ▸ eigenpair, selected_radius.trans minimum_eq.symm⟩

theorem path_spectral_minimum_normalized_iterate_limit
    (colours_positive : 0 < K)
    (reachable : ∀ colour, (rules.R colour).toSimpleGraph.Reachable
      (rules.βplus colour) (rules.βminus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ∀ path : (rules.R ruleColour).toSimpleGraph.Walk
        (rules.βplus ruleColour) (rules.βminus ruleColour),
          path.IsPath → (rules.R ruleColour).UsesColour path edgeColour) :
    ∃ (limit : ℝ) (vector : Fin K → ℝ),
      0 < rules.pathMinimumSpectralRadius ∧ 0 < limit ∧
      (∀ colour, 0 < vector colour) ∧ (∑ colour, vector colour) = 1 ∧
      (rules.pathRenormMap reachable).apply vector = rules.pathMinimumSpectralRadius • vector ∧
      Tendsto (fun level => fun colour =>
        (rules.pathRenormMap reachable).apply^[level] (fun _ => 1) colour /
          rules.pathMinimumSpectralRadius ^ level) atTop (nhds (limit • vector)) := by
  obtain ⟨vector, _, vector_positive, rate_positive, normalized, eigenpair, _⟩ :=
    rules.path_spectral_minimum_eigenpair_and_attainment colours_positive reachable distance_positive
  obtain ⟨limit, limit_positive, convergence⟩ :=
    (rules.pathRenormMap reachable).iterate_normalized_limit_of_strongly_positive
      colours_positive (rules.pathRenormMap_strongly_positive reachable distance_positive)
      vector_positive rate_positive normalized eigenpair
  exact ⟨limit, vector, rate_positive, limit_positive, vector_positive, normalized,
    eigenpair, convergence⟩

theorem path_spectral_minimum_ge_rule_distance_bound
    (colours_positive : 0 < K)
    (reachable : ∀ colour, (rules.R colour).toSimpleGraph.Reachable
      (rules.βplus colour) (rules.βminus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ∀ path : (rules.R ruleColour).toSimpleGraph.Walk
        (rules.βplus ruleColour) (rules.βminus ruleColour),
          path.IsPath → (rules.R ruleColour).UsesColour path edgeColour)
    (unique_edges : ∀ colour, (rules.R colour).EdgesUnique)
    (distance_bound : ℝ) (rule_distances : ∀ colour,
      distance_bound ≤ ((rules.R colour).toSimpleGraph.dist
        (rules.βplus colour) (rules.βminus colour) : ℝ)) :
    distance_bound ≤ rules.pathMinimumSpectralRadius := by
  obtain ⟨vector, _, vector_positive, _, _, eigenpair, _⟩ :=
    rules.path_spectral_minimum_eigenpair_and_attainment colours_positive reachable distance_positive
  exact rules.path_eigenvalue_ge_rule_distance_bound colours_positive reachable unique_edges
    distance_bound rule_distances vector _ vector_positive eigenpair

end EIGS.RuleSystem

#print axioms EIGS.RuleSystem.path_spectral_minimum_eigenpair_and_attainment
#print axioms EIGS.RuleSystem.path_spectral_minimum_normalized_iterate_limit
