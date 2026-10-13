import RequestProject.Section31.EIGSIncidentStarCompletionMesh
import RequestProject.Section31.EIGSIncidentStarTrajectoryExit

/-! Every actual fine vertex belongs to a coarse incident star. A graph
trajectory starting there remains in that star before its first coarse
arrival; the arrival itself is in the star or one adjacent step outside.
The resulting initial-segment mesh is in the same canonical completion.
No star-cover or mesh assumption is introduced. -/

namespace EIGS

open scoped Classical
noncomputable section
variable {K : ℕ}

theorem xiIncidentStar_exists_center (system : EIGSData K) (coarse steps : ℕ)
    (vertex : XiVtx system (coarse + steps)) :
    ∃ center : XiVtx system coarse, xiIncidentStar system coarse center steps vertex := by
  induction steps with
  | zero => exact ⟨vertex, rfl⟩
  | succ steps induction_hypothesis =>
      cases vertex with
      | inl old_vertex => exact induction_hypothesis old_vertex
      | inr private_vertex =>
          obtain ⟨edge, interior⟩ := private_vertex
          obtain ⟨center, inside⟩ := induction_hypothesis (XiTail system (coarse + steps) edge)
          exact ⟨center, Or.inl inside⟩

theorem xiIncidentStarDomain_exists_center (system : EIGSData K) (coarse steps : ℕ)
    (vertex : XiVtx system (coarse + steps)) :
    ∃ center : XiVtx system coarse, vertex ∈ xiIncidentStarDomain system coarse steps center := by
  obtain ⟨center, inside⟩ := xiIncidentStar_exists_center system coarse steps vertex
  exact ⟨center, Finset.mem_filter.mpr ⟨Finset.mem_univ _, inside⟩⟩

/-- The starting point may be any vertex of the actual star. -/
theorem xiIncidentStarDomain_trajectory_mem_of_start_mem (system : EIGSData K)
    (coarse steps : ℕ) (center : XiVtx system coarse)
    (trajectory : ℕ → XiVtx system (coarse + steps)) (time : ℕ)
    (start : trajectory 0 ∈ xiIncidentStarDomain system coarse steps center)
    (adjacency : ∀ index, index < time →
      (XiSimpleGraph system (coarse + steps)).Adj (trajectory index) (trajectory (index + 1)))
    (avoids : ∀ index, index ≤ time → ∀ other : XiVtx system coarse, other ≠ center →
      trajectory index ≠ xiForward system coarse steps other) :
    ∀ index, index ≤ time → trajectory index ∈ xiIncidentStarDomain system coarse steps center := by
  intro index
  induction index with
  | zero => exact fun _ => start
  | succ index induction_hypothesis =>
      intro before
      have previous := induction_hypothesis ((Nat.le_succ index).trans before)
      by_contra outside
      obtain ⟨other, different, same⟩ := xiIncidentStarDomain_adj_outside system coarse steps center
        previous outside (adjacency index ((Nat.lt_succ_self index).trans_le before))
      exact avoids (index + 1) before other different same

theorem xiInitialStar_trajectory_mem_before_coarse (system : EIGSData K)
    (coarse steps : ℕ) (center : XiVtx system coarse)
    (trajectory : ℕ → XiVtx system (coarse + steps)) (time : ℕ)
    (start : trajectory 0 ∈ xiIncidentStarDomain system coarse steps center)
    (adjacency : ∀ index, index < time →
      (XiSimpleGraph system (coarse + steps)).Adj (trajectory index) (trajectory (index + 1)))
    (avoids : ∀ index, index < time → ∀ other : XiVtx system coarse,
      trajectory index ≠ xiForward system coarse steps other) :
    ∀ index, index < time → trajectory index ∈ xiIncidentStarDomain system coarse steps center := by
  intro index before
  exact xiIncidentStarDomain_trajectory_mem_of_start_mem system coarse steps center trajectory index start
    (fun earlier earlier_before => adjacency earlier (earlier_before.trans before))
    (fun earlier earlier_before other _ => avoids earlier (earlier_before.trans_lt before) other)
    index (le_refl index)

/-- At the first coarse arrival, include the genuine adjacent boundary
point. The statement also covers a coarse starting point with time zero. -/
theorem xiInitialStar_trajectory_mem_or_adjacent (system : EIGSData K)
    (coarse steps : ℕ) (trajectory : ℕ → XiVtx system (coarse + steps)) (time : ℕ)
    (adjacency : ∀ index, index < time →
      (XiSimpleGraph system (coarse + steps)).Adj (trajectory index) (trajectory (index + 1)))
    (avoids : ∀ index, index < time → ∀ other : XiVtx system coarse,
      trajectory index ≠ xiForward system coarse steps other) :
    ∃ center : XiVtx system coarse,
      xiIncidentStar system coarse center steps (trajectory 0) ∧
      ∀ index, index ≤ time →
        (xiIncidentStar system coarse center steps (trajectory index) ∨
          ∃ inside, xiIncidentStar system coarse center steps inside ∧
            (XiSimpleGraph system (coarse + steps)).Adj inside (trajectory index)) := by
  obtain ⟨center, start⟩ := xiIncidentStarDomain_exists_center system coarse steps (trajectory 0)
  have start_star := (Finset.mem_filter.mp start).2
  refine ⟨center, start_star, ?_⟩
  intro index before
  by_cases strictly_before : index < time
  · exact Or.inl ((Finset.mem_filter.mp (xiInitialStar_trajectory_mem_before_coarse
      system coarse steps center trajectory time start adjacency avoids index strictly_before)).2)
  · have same : index = time := Nat.le_antisymm before (Nat.le_of_not_gt strictly_before)
    subst index
    cases time with
    | zero => exact Or.inl start_star
    | succ previous =>
        exact Or.inr ⟨trajectory previous,
          (Finset.mem_filter.mp (xiInitialStar_trajectory_mem_before_coarse system coarse steps center
            trajectory (previous + 1) start adjacency avoids previous (Nat.lt_succ_self previous))).2,
          adjacency previous (Nat.lt_succ_self previous)⟩

theorem xiCanonicalInitialSegment_completion_mesh_of_rules (system : EIGSData K)
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
      (trajectory : ℕ → XiVtx system (coarse + steps)) (time : ℕ),
      (∀ index, index < time →
        (XiSimpleGraph system (coarse + steps)).Adj (trajectory index) (trajectory (index + 1))) →
      (∀ index, index < time → ∀ other : XiVtx system coarse,
        trajectory index ≠ xiForward system coarse steps other) →
      ∀ index, index ≤ time →
        dist (parameters.vertexEmbedding (coarse + steps) (trajectory index))
            (parameters.vertexEmbedding (coarse + steps) (trajectory 0)) ≤
          coefficient * (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse := by
  intro parameters
  obtain ⟨coefficient, positive, mesh⟩ := xiCanonicalIncidentStar_completion_mesh_of_rules
    system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  refine ⟨2 * coefficient, by positivity, ?_⟩
  intro coarse steps trajectory time adjacency avoids index before
  obtain ⟨center, start, confinement⟩ := xiInitialStar_trajectory_mem_or_adjacent
    system coarse steps trajectory time adjacency avoids
  have first_bound := mesh coarse steps center (trajectory index) (confinement index before)
  have start_bound := mesh coarse steps center (trajectory 0) (Or.inl start)
  calc
    _ ≤ dist (parameters.vertexEmbedding (coarse + steps) (trajectory index))
          (parameters.vertexEmbedding coarse center) +
        dist (parameters.vertexEmbedding coarse center)
          (parameters.vertexEmbedding (coarse + steps) (trajectory 0)) := dist_triangle _ _ _
    _ ≤ coefficient * (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse +
        coefficient * (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse := by
      exact add_le_add first_bound (by simpa only [dist_comm] using start_bound)
    _ = _ := by ring

end
end EIGS

#print axioms EIGS.xiIncidentStar_exists_center
#print axioms EIGS.xiIncidentStarDomain_exists_center
#print axioms EIGS.xiIncidentStarDomain_trajectory_mem_of_start_mem
#print axioms EIGS.xiInitialStar_trajectory_mem_before_coarse
#print axioms EIGS.xiInitialStar_trajectory_mem_or_adjacent
#print axioms EIGS.xiCanonicalInitialSegment_completion_mesh_of_rules
