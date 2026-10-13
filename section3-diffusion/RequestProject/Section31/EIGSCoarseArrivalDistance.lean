import RequestProject.Section31.EIGSInitialStarGeometry
import RequestProject.Section31.BoundedCoarseHittingStops

/-! The actual scanner count controls spatial displacement of every
adjacency-supported fine path. An artificial initial star is used only
until the first actual coarse arrival. Thereafter the retained center is
the actual scanner's last coarse point. Its position changes only when
the actual count increases. -/

namespace EIGS

open scoped Classical
open IGS.Sec31.DiscreteMarkov
noncomputable section
set_option maxHeartbeats 4000000
variable {K : ℕ}

theorem xiPathMetricData_star_or_adjacent_distance_le (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected)
    (rateGeTwo : 2 ≤ system.distanceSpectralRadius rulesConnected)
    (coarse steps : ℕ) (center : XiVtx system coarse)
    (vertex : XiVtx system (coarse + steps))
    (membership : xiIncidentStar system coarse center steps vertex ∨
      ∃ inside, xiIncidentStar system coarse center steps inside ∧
        (XiSimpleGraph system (coarse + steps)).Adj inside vertex) :
    dist (parameters.vertexEmbedding (coarse + steps) vertex) (parameters.vertexEmbedding coarse center) ≤
      (3 * xiRuleRadius system parameters.lengths + 1) *
        (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse := by
  rcases membership with inside | ⟨inside, inside_star, adjacent⟩
  · have bound := xiIncidentStar_completion_distance_le system rulesConnected parameters.lengths
      parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected) parameters.ratePositive
      parameters.eigenpair rateGeTwo coarse steps center vertex inside
    change dist (xiCompletionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair
      (coarse + steps) vertex) _ ≤ _
    exact bound.trans (by
      nlinarith [pow_nonneg (inv_nonneg.mpr parameters.ratePositive.le) coarse])
  · have bound := xiIncidentStar_adjacent_completion_distance_le system rulesConnected parameters.lengths
      parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected) parameters.ratePositive
      parameters.eigenpair rateGeTwo coarse steps center inside_star adjacent
    simpa only [parameters.normalized] using bound

/-- A geometric invariant of the actual count scanner, with an actual
coarse center rather than a postulated decomposition into excursions. -/
theorem xiCoarseArrivalState_center_invariant (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected)
    (rateGeTwo : 2 ≤ system.distanceSpectralRadius rulesConnected)
    (coarse steps : ℕ) (path : ℕ → XiVtx system (coarse + steps)) (time : ℕ)
    (adjacency : ∀ index, index < time →
      (XiSimpleGraph system (coarse + steps)).Adj (path index) (path (index + 1))) :
    ∃ center : XiVtx system coarse,
      xiIncidentStar system coarse center steps (path time) ∧
      ((coarseArrivalState (Finset.univ.image (xiForward system coarse steps)) path time).1 = none ∨
        (coarseArrivalState (Finset.univ.image (xiForward system coarse steps)) path time).1 =
          some (xiForward system coarse steps center)) ∧
      dist (parameters.vertexEmbedding coarse center)
          (parameters.vertexEmbedding (coarse + steps) (path 0)) ≤
        ((coarseArrivalState (Finset.univ.image (xiForward system coarse steps)) path time).2 + 1 : ℝ) *
          ((3 * xiRuleRadius system parameters.lengths + 1) *
            (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse) := by
  have radius_nonnegative : 0 ≤ (3 * xiRuleRadius system parameters.lengths + 1) *
      (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse := by
    have := xiRuleRadius_nonnegative system (fun colour => (parameters.lengthsPositive colour).le)
    have ratePositive := parameters.ratePositive
    positivity
  induction time with
  | zero =>
      by_cases starts_coarse : path 0 ∈ Finset.univ.image (xiForward system coarse steps)
      · obtain ⟨center, _, same⟩ := Finset.mem_image.mp starts_coarse
        refine ⟨center, ?_, ?_, ?_⟩
        · rw [← same]
          exact (xiIncidentStar_forward_iff system coarse steps center center).mpr rfl
        · exact Or.inr (by simp only [coarseArrivalState, if_pos starts_coarse, same])
        · have embedding_same : parameters.vertexEmbedding (coarse + steps) (path 0) =
              parameters.vertexEmbedding coarse center := by
            rw [← same]
            exact xiCompletionEmbedding_forward system rulesConnected parameters.lengths parameters.lengthsPositive
              (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair
              coarse steps center
          simp only [coarseArrivalState, if_pos starts_coarse, embedding_same, dist_self]
          positivity
      · obtain ⟨center, inside⟩ := xiIncidentStar_exists_center system coarse steps (path 0)
        refine ⟨center, inside, Or.inl (by simp only [coarseArrivalState, if_neg starts_coarse]), ?_⟩
        simpa only [coarseArrivalState, if_neg starts_coarse, Nat.cast_zero, zero_add, one_mul, dist_comm]
          using xiPathMetricData_star_or_adjacent_distance_le system rulesConnected parameters rateGeTwo
            coarse steps center (path 0) (Or.inl inside)
  | succ time induction_hypothesis =>
      obtain ⟨center, inside, last_center, center_bound⟩ :=
        induction_hypothesis (fun index before => adjacency index (before.trans (Nat.lt_succ_self time)))
      have adjacent := adjacency time (Nat.lt_succ_self time)
      by_cases arrives : path (time + 1) ∈ Finset.univ.image (xiForward system coarse steps) ∧
          (coarseArrivalState (Finset.univ.image (xiForward system coarse steps)) path time).1 ≠
            some (path (time + 1))
      · have next_state : coarseArrivalState (Finset.univ.image (xiForward system coarse steps)) path (time + 1) =
            (some (path (time + 1)),
              (coarseArrivalState (Finset.univ.image (xiForward system coarse steps)) path time).2 + 1) := by
          rw [coarseArrivalState, coarseArrivalUpdate, if_pos arrives]
        obtain ⟨next_center, _, same⟩ := Finset.mem_image.mp arrives.1
        have embedding_same : parameters.vertexEmbedding (coarse + steps) (path (time + 1)) =
            parameters.vertexEmbedding coarse next_center := by
          rw [← same]
          exact xiCompletionEmbedding_forward system rulesConnected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair
            coarse steps next_center
        refine ⟨next_center, ?_, Or.inr (by simp only [next_state, same]), ?_⟩
        · rw [← same]
          exact (xiIncidentStar_forward_iff system coarse steps next_center next_center).mpr rfl
        · have crossing_bound := xiPathMetricData_star_or_adjacent_distance_le system rulesConnected
            parameters rateGeTwo coarse steps center (path (time + 1)) (Or.inr ⟨path time, inside, adjacent⟩)
          rw [embedding_same] at crossing_bound
          simp only [next_state, Nat.cast_add, Nat.cast_one]
          calc
            _ ≤ dist (parameters.vertexEmbedding coarse next_center) (parameters.vertexEmbedding coarse center) +
                dist (parameters.vertexEmbedding coarse center)
                  (parameters.vertexEmbedding (coarse + steps) (path 0)) := dist_triangle _ _ _
            _ ≤ (3 * xiRuleRadius system parameters.lengths + 1) *
                  (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse +
                ((coarseArrivalState (Finset.univ.image (xiForward system coarse steps)) path time).2 + 1 : ℝ) *
                  ((3 * xiRuleRadius system parameters.lengths + 1) *
                    (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse) :=
              add_le_add crossing_bound center_bound
            _ = _ := by ring
      · have next_state : coarseArrivalState (Finset.univ.image (xiForward system coarse steps)) path (time + 1) =
            coarseArrivalState (Finset.univ.image (xiForward system coarse steps)) path time := by
          rw [coarseArrivalState, coarseArrivalUpdate, if_neg arrives]
        refine ⟨center, ?_, by simpa only [next_state] using last_center,
          by simpa only [next_state] using center_bound⟩
        by_cases next_coarse : path (time + 1) ∈ Finset.univ.image (xiForward system coarse steps)
        · have same_last : (coarseArrivalState (Finset.univ.image (xiForward system coarse steps)) path time).1 =
              some (path (time + 1)) := by
            by_contra different
            exact arrives ⟨next_coarse, different⟩
          rcases last_center with no_last | last_center
          · rw [same_last] at no_last
            cases no_last
          · have same : xiForward system coarse steps center = path (time + 1) :=
              Option.some.inj (last_center.symm.trans same_last)
            rw [← same]
            exact (xiIncidentStar_forward_iff system coarse steps center center).mpr rfl
        · by_contra outside
          obtain ⟨other, _, same⟩ := xiIncidentStarDomain_adj_outside system coarse steps center
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, inside⟩)
            (by intro member; exact outside (Finset.mem_filter.mp member).2) adjacent
          exact next_coarse (Finset.mem_image.mpr ⟨other, Finset.mem_univ _, same.symm⟩)

theorem xiCoarseArrivalState_distance_le (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected)
    (rateGeTwo : 2 ≤ system.distanceSpectralRadius rulesConnected)
    (coarse steps : ℕ) (path : ℕ → XiVtx system (coarse + steps)) (time : ℕ)
    (adjacency : ∀ index, index < time →
      (XiSimpleGraph system (coarse + steps)).Adj (path index) (path (index + 1))) :
    dist (parameters.vertexEmbedding (coarse + steps) (path time))
        (parameters.vertexEmbedding (coarse + steps) (path 0)) ≤
      ((coarseArrivalState (Finset.univ.image (xiForward system coarse steps)) path time).2 + 2 : ℝ) *
        ((3 * xiRuleRadius system parameters.lengths + 1) *
          (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse) := by
  obtain ⟨center, inside, _, center_bound⟩ := xiCoarseArrivalState_center_invariant system rulesConnected
    parameters rateGeTwo coarse steps path time adjacency
  have star_bound := xiPathMetricData_star_or_adjacent_distance_le system rulesConnected parameters
    rateGeTwo coarse steps center (path time) (Or.inl inside)
  calc
    _ ≤ dist (parameters.vertexEmbedding (coarse + steps) (path time)) (parameters.vertexEmbedding coarse center) +
        dist (parameters.vertexEmbedding coarse center)
          (parameters.vertexEmbedding (coarse + steps) (path 0)) := dist_triangle _ _ _
    _ ≤ (3 * xiRuleRadius system parameters.lengths + 1) *
          (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse +
        ((coarseArrivalState (Finset.univ.image (xiForward system coarse steps)) path time).2 + 1 : ℝ) *
          ((3 * xiRuleRadius system parameters.lengths + 1) *
            (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse) := add_le_add star_bound center_bound
    _ = _ := by ring

theorem xiCoarseArrivalState_prefix_distance_le (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected)
    (rateGeTwo : 2 ≤ system.distanceSpectralRadius rulesConnected)
    (coarse steps : ℕ) (path : ℕ → XiVtx system (coarse + steps)) (horizon count : ℕ)
    (adjacency : ∀ index, index < horizon →
      (XiSimpleGraph system (coarse + steps)).Adj (path index) (path (index + 1)))
    (count_bound : (coarseArrivalState (Finset.univ.image (xiForward system coarse steps)) path horizon).2 ≤ count) :
    ∀ time, time ≤ horizon →
      dist (parameters.vertexEmbedding (coarse + steps) (path time))
          (parameters.vertexEmbedding (coarse + steps) (path 0)) ≤
        (count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
          (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse) := by
  intro time before
  have bound := xiCoarseArrivalState_distance_le system rulesConnected parameters rateGeTwo coarse steps path time
    (fun index index_before => adjacency index (index_before.trans_le before))
  letI : MeasurableSpace (XiVtx system (coarse + steps)) := ⊤
  have count_le := (coarseArrivalState_count_monotone
    (Finset.univ.image (xiForward system coarse steps)) path before).trans count_bound
  have cast_count_le : ((coarseArrivalState (Finset.univ.image (xiForward system coarse steps)) path time).2 : ℝ) ≤
      (count : ℝ) := by exact_mod_cast count_le
  have radius_nonnegative : 0 ≤ (3 * xiRuleRadius system parameters.lengths + 1) *
      (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse := by
    have := xiRuleRadius_nonnegative system (fun colour => (parameters.lengthsPositive colour).le)
    have ratePositive := parameters.ratePositive
    positivity
  exact bound.trans (mul_le_mul_of_nonneg_right (by linarith) radius_nonnegative)

theorem xiCoarseArrivalState_count_gt_of_displacement (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected)
    (rateGeTwo : 2 ≤ system.distanceSpectralRadius rulesConnected)
    (coarse steps : ℕ) (path : ℕ → XiVtx system (coarse + steps)) (horizon count : ℕ)
    (adjacency : ∀ index, index < horizon →
      (XiSimpleGraph system (coarse + steps)).Adj (path index) (path (index + 1)))
    (displacement : ∃ time, time ≤ horizon ∧
      (count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
        (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse) <
      dist (parameters.vertexEmbedding (coarse + steps) (path time))
        (parameters.vertexEmbedding (coarse + steps) (path 0))) :
    count < (coarseArrivalState (Finset.univ.image (xiForward system coarse steps)) path horizon).2 := by
  by_contra not_more
  obtain ⟨time, before, farther⟩ := displacement
  exact (not_lt_of_ge (xiCoarseArrivalState_prefix_distance_le system rulesConnected parameters
    rateGeTwo coarse steps path horizon count adjacency (Nat.le_of_not_gt not_more) time before)) farther

/-- A displacement forces the actual scanner stop to complete by the
observed horizon. The cap is one step later, so completion is genuine. -/
theorem xiBoundedCoarseArrival_le_of_displacement (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected)
    (rateGeTwo : 2 ≤ system.distanceSpectralRadius rulesConnected)
    (coarse steps : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))]
    (path : ℕ → XiVtx system (coarse + steps)) (horizon count : ℕ)
    (adjacency : ∀ index, index < horizon →
      (XiSimpleGraph system (coarse + steps)).Adj (path index) (path (index + 1)))
    (displacement : ∃ time, time ≤ horizon ∧
      (count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
        (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse) <
      dist (parameters.vertexEmbedding (coarse + steps) (path time))
        (parameters.vertexEmbedding (coarse + steps) (path 0))) :
    ((boundedCoarseArrival (Finset.univ.image (xiForward system coarse steps)) count (horizon + 1)).time path).val ≤
      horizon := by
  apply boundedCoarseArrival_le_of_count
  exact Nat.succ_le_of_lt (xiCoarseArrivalState_count_gt_of_displacement system rulesConnected
    parameters rateGeTwo coarse steps path horizon count adjacency displacement)

theorem xiCanonicalCoarseArrival_prefix_mesh_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ coarse steps
      (path : ℕ → XiVtx system (coarse + steps)) (horizon count : ℕ),
      (∀ index, index < horizon →
        (XiSimpleGraph system (coarse + steps)).Adj (path index) (path (index + 1))) →
      (coarseArrivalState (Finset.univ.image (xiForward system coarse steps)) path horizon).2 ≤ count →
      ∀ time, time ≤ horizon →
        dist (parameters.vertexEmbedding (coarse + steps) (path time))
            (parameters.vertexEmbedding (coarse + steps) (path 0)) ≤
          coefficient * (count + 2 : ℝ) * (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse := by
  intro parameters
  have radius_nonnegative := xiRuleRadius_nonnegative system
    (fun colour => (parameters.lengthsPositive colour).le)
  refine ⟨3 * xiRuleRadius system parameters.lengths + 1, by positivity, ?_⟩
  intro coarse steps path horizon count adjacency count_bound time before
  have rateGeTwo := system.two_le_distanceSpectralRadius rulesConnected rulesUnique
    plantingNonadjacent distancePositive
  have bound := xiCoarseArrivalState_prefix_distance_le system rulesConnected parameters rateGeTwo
    coarse steps path horizon count adjacency count_bound time before
  convert bound using 1 <;> ring

end
end EIGS

#print axioms EIGS.xiPathMetricData_star_or_adjacent_distance_le
#print axioms EIGS.xiCoarseArrivalState_center_invariant
#print axioms EIGS.xiCoarseArrivalState_distance_le
#print axioms EIGS.xiCoarseArrivalState_prefix_distance_le
#print axioms EIGS.xiCoarseArrivalState_count_gt_of_displacement
#print axioms EIGS.xiBoundedCoarseArrival_le_of_displacement
#print axioms EIGS.xiCanonicalCoarseArrival_prefix_mesh_of_rules
