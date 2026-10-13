import RequestProject.Section2BallLower
import RequestProject.Section2MesoscopicVolumeUpper
import RequestProject.Section2ForwardComposition

/-! Two-sided birth-dependent volume of the actual original unit-distance
balls, for every fixed positive pair of radius comparison constants. -/

namespace EIGS

open scoped BigOperators Classical

theorem degree_le_finiteGraphBall_card {Vertex : Type*} [Fintype Vertex]
    [DecidableEq Vertex] (graph : SimpleGraph Vertex) (center : Vertex)
    {radius : ℝ} (radius_gt_one : 1 < radius) :
    graph.degree center ≤ (finiteGraphBall graph center radius).card := by
  change (graph.neighborFinset center).card ≤ _
  apply Finset.card_le_card
  intro vertex neighbor
  have adjacent : graph.Adj center vertex := by simpa only [SimpleGraph.mem_neighborFinset] using neighbor
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    simpa only [SimpleGraph.dist_eq_one_iff_adj.mpr adjacent, Nat.cast_one] using radius_gt_one⟩

variable {K : ℕ}

theorem xiSimpleGraph_mesoscopic_ball_birth_spectral_volume (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (primitive_degree : (degreeMatrix system).IsPrimitive)
    (radius_lower radius_upper : ℝ) (radius_lower_positive : 0 < radius_lower)
    (radius_upper_positive : 0 < radius_upper) :
    ∃ buffer : ℕ, ∀ initial_level (vertex : XiVtx system initial_level),
      ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ age depth (radius : ℝ),
        buffer ≤ age → 1 < radius →
        radius_lower * (system.distanceSpectralRadius rule_connected) ^ depth ≤ radius →
        radius ≤ radius_upper * (system.distanceSpectralRadius rule_connected) ^ depth →
        lower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age *
            realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ depth ≤
          ((finiteGraphBall (XiSimpleGraph system (initial_level + (age + depth)))
            (xiForward system initial_level (age + depth) vertex) radius).card : ℝ) ∧
        ((finiteGraphBall (XiSimpleGraph system (initial_level + (age + depth)))
            (xiForward system initial_level (age + depth) vertex) radius).card : ℝ) ≤
          upper * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age *
            realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ depth := by
  classical
  have distance_rate_ge_two := system.two_le_distanceSpectralRadius rule_connected rules_unique
    planting_nonadjacent distance_positive
  have distance_rate_gt_one : 1 < system.distanceSpectralRadius rule_connected := by linarith
  have distance_rate_positive := zero_lt_one.trans distance_rate_gt_one
  obtain ⟨mass_rate_positive, _⟩ := eigs_mass_spectral_growth system rule_connected distance_positive
  obtain ⟨degree_rate_positive, degree_growth⟩ :=
    degree_spectral_growth_from_primitive_rules system rule_connected primitive_degree
  obtain ⟨small_coefficient, small_coefficient_positive, upper_growth⟩ :=
    xiSimpleGraph_mesoscopic_ball_birth_spectral_upper system rule_connected rules_loopless
      rules_unique planting_nonadjacent distance_positive primitive_degree
  obtain ⟨large_coefficient, large_lower, large_coefficient_positive, large_lower_positive,
    lower_growth⟩ := xiSimpleGraph_large_ball_spectral_lower system rule_connected rules_loopless
      rules_unique planting_nonadjacent distance_positive
  obtain ⟨upper_shift, upper_shift_bound⟩ :=
    pow_unbounded_of_one_lt (radius_upper / small_coefficient) distance_rate_gt_one
  have upper_coefficient_bound : radius_upper ≤ small_coefficient *
      (system.distanceSpectralRadius rule_connected) ^ upper_shift := by
    exact ((div_lt_iff₀ small_coefficient_positive).mp upper_shift_bound).le.trans_eq (mul_comm _ _)
  obtain ⟨lower_shift, lower_shift_bound⟩ :=
    pow_unbounded_of_one_lt (large_coefficient / radius_lower) distance_rate_gt_one
  have lower_coefficient_bound : large_coefficient ≤ radius_lower *
      (system.distanceSpectralRadius rule_connected) ^ lower_shift := by
    exact ((div_lt_iff₀ radius_lower_positive).mp lower_shift_bound).le.trans_eq (mul_comm _ _)
  refine ⟨upper_shift, fun initial_level vertex => ?_⟩
  obtain ⟨degree_lower, _, degree_lower_positive, _, degree_bound⟩ := degree_growth initial_level vertex
  obtain ⟨original_upper, original_upper_positive, original_upper_bound⟩ := upper_growth initial_level vertex
  let finite_lower := (Finset.range (lower_shift + 1)).inf'
    (by simp) (fun depth => finiteRealMatrixSpectralRadius (degreeMatrix system) ^ depth /
      realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ depth)
  have finite_lower_positive : 0 < finite_lower := by
    exact (Finset.lt_inf'_iff _).mpr (fun depth _ =>
      div_pos (pow_pos degree_rate_positive depth) (pow_pos mass_rate_positive depth))
  let large_birth_lower := large_lower * degree_lower *
    finiteRealMatrixSpectralRadius (degreeMatrix system) ^ lower_shift /
      realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ (lower_shift + 1)
  have large_birth_lower_positive : 0 < large_birth_lower := by positivity
  let birth_lower := min large_birth_lower (degree_lower * finite_lower)
  let birth_upper := original_upper *
    realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ upper_shift /
      finiteRealMatrixSpectralRadius (degreeMatrix system) ^ upper_shift
  refine ⟨birth_lower, birth_upper,
    lt_min large_birth_lower_positive (mul_pos degree_lower_positive finite_lower_positive),
    by positivity, fun age depth radius age_buffer radius_gt_one radius_lower_bound radius_upper_bound => ?_⟩
  have actual_degree_bound : ∀ steps,
      degree_lower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ steps ≤
        ((XiSimpleGraph system (initial_level + steps)).degree
          (xiForward system initial_level steps vertex) : ℝ) := by
    intro steps
    rw [xiSimpleGraph_degree_eq_degree_state_sum system rule_connected rules_loopless rules_unique
      planting_nonadjacent]
    exact (degree_bound steps).1
  constructor
  · by_cases depth_large : lower_shift + 1 ≤ depth
    · have radius_bound : large_coefficient * (system.distanceSpectralRadius rule_connected) ^
          ((depth - (lower_shift + 1)) + 1) ≤ radius := by
        apply le_trans (mul_le_mul_of_nonneg_right lower_coefficient_bound
          (pow_nonneg distance_rate_positive.le _))
        have exponent_identity : lower_shift + ((depth - (lower_shift + 1)) + 1) = depth := by omega
        simpa only [mul_assoc, ← pow_add, exponent_identity] using radius_lower_bound
      have large_bound := lower_growth (initial_level + (age + lower_shift))
        (depth - (lower_shift + 1)) (xiForward system initial_level (age + lower_shift) vertex)
        radius radius_bound
      change large_lower * ((XiSimpleGraph system (initial_level + (age + lower_shift))).degree
        (xiForward system initial_level (age + lower_shift) vertex) : ℝ) *
        realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ (depth - (lower_shift + 1)) ≤
        ((finiteGraphBall (XiSimpleGraph system
          ((initial_level + (age + lower_shift)) + ((depth - (lower_shift + 1)) + 1)))
          (xiForward system (initial_level + (age + lower_shift))
            ((depth - (lower_shift + 1)) + 1)
            (xiForward system initial_level (age + lower_shift) vertex)) radius).card : ℝ) at large_bound
      have count_identity := xiForward_ball_card_trans system initial_level (age + lower_shift)
        ((depth - (lower_shift + 1)) + 1) vertex radius
      have level_identity : (age + lower_shift) + ((depth - (lower_shift + 1)) + 1) = age + depth := by omega
      rw [level_identity] at count_identity
      rw [count_identity] at large_bound
      have lower_degree := actual_degree_bound (age + lower_shift)
      have combined := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left lower_degree large_lower_positive.le)
        (pow_nonneg mass_rate_positive.le (depth - (lower_shift + 1)))
      have mass_decomposition : realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ depth =
          realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ (lower_shift + 1) *
            realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ (depth - (lower_shift + 1)) := by
        rw [← pow_add, Nat.add_sub_of_le depth_large]
      have scaling_identity : large_birth_lower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age *
          realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ depth =
        large_lower * (degree_lower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ (age + lower_shift)) *
          realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ (depth - (lower_shift + 1)) := by
        dsimp [large_birth_lower]
        rw [mass_decomposition, pow_add]
        field_simp [ne_of_gt mass_rate_positive, ne_of_gt degree_rate_positive]
        <;> ring
      apply (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg degree_rate_positive.le age))
        (pow_nonneg mass_rate_positive.le depth)).trans
      rw [scaling_identity]
      exact combined.trans large_bound
    · have depth_mem : depth ∈ Finset.range (lower_shift + 1) := Finset.mem_range.mpr (by omega)
      have finite_bound : finite_lower * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ depth ≤
          finiteRealMatrixSpectralRadius (degreeMatrix system) ^ depth := by
        exact (le_div_iff₀ (pow_pos mass_rate_positive depth)).mp
          (Finset.inf'_le _ depth_mem)
      have scaled_finite_bound := mul_le_mul_of_nonneg_left finite_bound
        (mul_nonneg degree_lower_positive.le (pow_nonneg degree_rate_positive.le age))
      have lower_degree := actual_degree_bound (age + depth)
      have neighbors_bound :
          ((XiSimpleGraph system (initial_level + (age + depth))).degree
            (xiForward system initial_level (age + depth) vertex) : ℝ) ≤
          ((finiteGraphBall (XiSimpleGraph system (initial_level + (age + depth)))
            (xiForward system initial_level (age + depth) vertex) radius).card : ℝ) := by
        exact_mod_cast degree_le_finiteGraphBall_card
          (XiSimpleGraph system (initial_level + (age + depth)))
          (xiForward system initial_level (age + depth) vertex) radius_gt_one
      apply (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg degree_rate_positive.le age))
        (pow_nonneg mass_rate_positive.le depth)).trans
      apply le_trans _ (lower_degree.trans neighbors_bound)
      simpa only [pow_add, mul_assoc, mul_left_comm, mul_comm] using scaled_finite_bound
  · have radius_bound : radius ≤ small_coefficient * (system.distanceSpectralRadius rule_connected) ^
        (upper_shift + depth) := by
      apply radius_upper_bound.trans
      have shifted := mul_le_mul_of_nonneg_right upper_coefficient_bound
        (pow_nonneg distance_rate_positive.le depth)
      simpa only [mul_assoc, ← pow_add] using shifted
    have upper_bound := original_upper_bound (age - upper_shift) (upper_shift + depth) radius
      (zero_lt_one.trans radius_gt_one) radius_bound
    rw [xiForward_ball_card_trans] at upper_bound
    have level_identity : (age - upper_shift) + (upper_shift + depth) = age + depth := by omega
    rw [level_identity] at upper_bound
    apply upper_bound.trans_eq
    have degree_decomposition : finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age =
        finiteRealMatrixSpectralRadius (degreeMatrix system) ^ (age - upper_shift) *
          finiteRealMatrixSpectralRadius (degreeMatrix system) ^ upper_shift := by
      rw [← pow_add, Nat.sub_add_cancel age_buffer]
    dsimp [birth_upper]
    rw [degree_decomposition, pow_add]
    field_simp [ne_of_gt mass_rate_positive, ne_of_gt degree_rate_positive]
    <;> ring

end EIGS

#print axioms EIGS.degree_le_finiteGraphBall_card
#print axioms EIGS.xiSimpleGraph_mesoscopic_ball_birth_spectral_volume
