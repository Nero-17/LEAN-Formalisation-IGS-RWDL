import RequestProject.Section31.EIGSUniformGeometricBounds
import RequestProject.Section31.EIGSOriginalDiameterGrowth
import RequestProject.Section2VertexGrowth
import RequestProject.Section2SpectralGrowth
import RequestProject.Section2StarSpectralVolume

/-! The all-colour, all-generation mass and distance clauses of the
manuscript's basic-properties lemma. The rates are the canonical actual
spectral radii. Finite initial generations are retained, not discarded. -/

namespace EIGS
noncomputable section
open Filter Topology Metric Set
open scoped Classical
variable {K : ℕ}

theorem xiReplanted_edge_card_spectral_bounds_all_generations (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ colour level,
      lower * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ level ≤
        (totalEdges {system.toRuleData with ι := colour} level : ℝ) ∧
      (totalEdges {system.toRuleData with ι := colour} level : ℝ) ≤
        upper * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ level := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  apply finite_family_uniform_geometric_bounds
    (fun colour level => (totalEdges {system.toRuleData with ι := colour} level : ℝ))
    (realMatrixSpectralRadius (massMatrixR system.toRuleData))
    (eigs_mass_spectral_growth system connected distancePositive).1
  intro colour
  exact (eigs_mass_spectral_growth {system with initCol := colour} connected distancePositive).2

theorem xiReplanted_vertex_card_spectral_bounds_all_generations (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ colour level,
      lower * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ level ≤
        (Fintype.card (XiVtx {system with initCol := colour} level) : ℝ) ∧
      (Fintype.card (XiVtx {system with initCol := colour} level) : ℝ) ≤
        upper * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ level := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  obtain ⟨upper, upperPositive, upperBound⟩ :=
    xiReplanted_vertex_card_spectral_upper system connected distancePositive
  have massPositive := (eigs_mass_spectral_growth system connected distancePositive).1
  apply finite_family_uniform_geometric_bounds
    (fun colour level => (Fintype.card (XiVtx {system with initCol := colour} level) : ℝ))
    (realMatrixSpectralRadius (massMatrixR system.toRuleData)) massPositive
  intro colour
  obtain ⟨_, lower, _, lowerPositive, _, massBound⟩ :=
    eigs_mass_spectral_growth {system with initCol := colour} connected distancePositive
  refine ⟨min 2 (lower / realMatrixSpectralRadius (massMatrixR system.toRuleData)), upper,
    lt_min (by norm_num) (div_pos lowerPositive massPositive), upperPositive, ?_⟩
  intro level
  refine ⟨?_, upperBound colour level⟩
  cases level with
  | zero =>
    simpa [XiVtx] using min_le_left (2 : ℝ)
      (lower / realMatrixSpectralRadius (massMatrixR system.toRuleData))
  | succ level =>
    calc
      min 2 (lower / realMatrixSpectralRadius (massMatrixR system.toRuleData)) *
          realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ (level + 1) ≤
        (lower / realMatrixSpectralRadius (massMatrixR system.toRuleData)) *
          realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ (level + 1) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_pos massPositive _).le
      _ = lower * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ level := by
        rw [pow_succ]
        field_simp [massPositive.ne']
      _ ≤ (totalEdges {system.toRuleData with ι := colour} level : ℝ) := (massBound level).1
      _ ≤ (Fintype.card (XiVtx {system with initCol := colour} (level + 1)) : ℝ) := by
        exact_mod_cast xiNetwork_edges_le_successor_vertices {system with initCol := colour}
          connected plantingNonadjacent level

theorem xiSimpleGraph_terminal_distance_spectral_bounds_all_generations (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ level,
      lower * system.distanceSpectralRadius connected ^ level ≤
        ((XiSimpleGraph system level).dist (xiPositiveTerminal system level) (xiNegativeTerminal system level) : ℝ) ∧
      ((XiSimpleGraph system level).dist (xiPositiveTerminal system level) (xiNegativeTerminal system level) : ℝ) ≤
        upper * system.distanceSpectralRadius connected ^ level := by
  obtain ⟨rateGreaterThanOne, limit, limitPositive, convergence⟩ :=
    xiSimpleGraph_terminal_distance_spectral_limit system connected loopless unique plantingNonadjacent distancePositive
  have ratePositive := zero_lt_one.trans rateGreaterThanOne
  apply geometric_bounds_all_generations_of_eventually _ _ ratePositive
  · intro level
    have different := xiTerminals_distinct system level
    have distancePositive : 0 < (XiSimpleGraph system level).dist
        (xiPositiveTerminal system level) (xiNegativeTerminal system level) := by
      apply Nat.pos_of_ne_zero
      intro zero
      exact different ((xiSimpleGraph_connected system connected level).dist_eq_zero_iff.mp zero)
    exact_mod_cast distancePositive
  · refine ⟨limit / 2, 2 * limit, by positivity, by positivity, ?_⟩
    have lower := convergence.eventually (lt_mem_nhds (by linarith : limit / 2 < limit))
    have upper := convergence.eventually (gt_mem_nhds (by linarith : limit < 2 * limit))
    filter_upwards [lower, upper] with level lowerBound upperBound
    exact ⟨((lt_div_iff₀ (pow_pos ratePositive level)).mp lowerBound).le,
      ((div_lt_iff₀ (pow_pos ratePositive level)).mp upperBound).le⟩

theorem xiSimpleGraph_terminal_distance_le_originalDiameter (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless) (level : ℕ) :
    ((XiSimpleGraph system level).dist (xiPositiveTerminal system level) (xiNegativeTerminal system level) : ℝ) ≤
      xiFiniteLevelDiameter system connected (fun _ => (1 : ℝ)⁻¹)
        (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level := by
  letI := xiLevelMetricSpace system connected (fun _ => (1 : ℝ)⁻¹)
    (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level
  have bound := Metric.dist_le_diam_of_mem (s := Set.univ) isCompact_univ.isBounded
    (Set.mem_univ (xiPositiveTerminal system level)) (Set.mem_univ (xiNegativeTerminal system level))
  have unitDistance :
      ((XiSimpleGraph system level).dist (xiPositiveTerminal system level) (xiNegativeTerminal system level) : ℝ) =
        dist (xiPositiveTerminal system level) (xiNegativeTerminal system level) := by
    change _ = (1 : ℝ)⁻¹ ^ level * (XiNetwork system level).weightedDistance (fun _ => (1 : ℝ)⁻¹)
      (xiPositiveTerminal system level) (xiNegativeTerminal system level)
    simp only [inv_one, one_pow, one_mul]
    exact ((XiNetwork system level).weightedDistance_unit_eq_graphDistance
      (xiSimpleGraph_connected system connected level) (xiNetwork_loopless system connected loopless level)
      (xiPositiveTerminal system level) (xiNegativeTerminal system level)).symm
  exact unitDistance.le.trans bound

theorem xiReplanted_distance_diameter_spectral_bounds_all_generations (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ colour level,
      lower * system.distanceSpectralRadius connected ^ level ≤
        ((XiSimpleGraph {system with initCol := colour} level).dist
          (xiPositiveTerminal {system with initCol := colour} level)
          (xiNegativeTerminal {system with initCol := colour} level) : ℝ) ∧
      ((XiSimpleGraph {system with initCol := colour} level).dist
          (xiPositiveTerminal {system with initCol := colour} level)
          (xiNegativeTerminal {system with initCol := colour} level) : ℝ) ≤
        xiFiniteLevelDiameter {system with initCol := colour} connected (fun _ => (1 : ℝ)⁻¹)
          (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level ∧
      xiFiniteLevelDiameter {system with initCol := colour} connected (fun _ => (1 : ℝ)⁻¹)
          (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level ≤
        upper * system.distanceSpectralRadius connected ^ level := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  have ratePositive : 0 < system.distanceSpectralRadius connected :=
    (by norm_num : (0 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  obtain ⟨lower, _, lowerPositive, _, distanceBound⟩ := finite_family_uniform_geometric_bounds
    (fun colour level => ((XiSimpleGraph {system with initCol := colour} level).dist
      (xiPositiveTerminal {system with initCol := colour} level)
      (xiNegativeTerminal {system with initCol := colour} level) : ℝ))
    (system.distanceSpectralRadius connected) ratePositive
    (fun colour => xiSimpleGraph_terminal_distance_spectral_bounds_all_generations
      {system with initCol := colour} connected loopless unique plantingNonadjacent distancePositive)
  have diameterBounds (colour : Fin K) : ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ level,
      lower * system.distanceSpectralRadius connected ^ level ≤
        xiFiniteLevelDiameter {system with initCol := colour} connected (fun _ => (1 : ℝ)⁻¹)
          (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level ∧
      xiFiniteLevelDiameter {system with initCol := colour} connected (fun _ => (1 : ℝ)⁻¹)
          (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level ≤
        upper * system.distanceSpectralRadius connected ^ level := by
    apply geometric_bounds_all_generations_of_eventually _ _ ratePositive
      (fun level => xiFiniteLevelDiameter_positive {system with initCol := colour} connected
        (fun _ => (1 : ℝ)⁻¹) (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level)
    exact xiOriginalDiameter_spectral_growth {system with initCol := colour}
      connected loopless unique plantingNonadjacent distancePositive
  obtain ⟨_, upper, _, upperPositive, diameterBound⟩ := finite_family_uniform_geometric_bounds
    (fun colour level => xiFiniteLevelDiameter {system with initCol := colour} connected (fun _ => (1 : ℝ)⁻¹)
      (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level)
    (system.distanceSpectralRadius connected) ratePositive diameterBounds
  exact ⟨lower, upper, lowerPositive, upperPositive, fun colour level =>
    ⟨(distanceBound colour level).1,
      xiSimpleGraph_terminal_distance_le_originalDiameter {system with initCol := colour} connected loopless level,
      (diameterBound colour level).2⟩⟩

end
end EIGS

#print axioms EIGS.xiReplanted_edge_card_spectral_bounds_all_generations
#print axioms EIGS.xiReplanted_vertex_card_spectral_bounds_all_generations
#print axioms EIGS.xiSimpleGraph_terminal_distance_spectral_bounds_all_generations
#print axioms EIGS.xiSimpleGraph_terminal_distance_le_originalDiameter
#print axioms EIGS.xiReplanted_distance_diameter_spectral_bounds_all_generations
