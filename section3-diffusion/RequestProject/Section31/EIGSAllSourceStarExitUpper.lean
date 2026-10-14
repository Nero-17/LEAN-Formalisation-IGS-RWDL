import RequestProject.Section31.EIGSAllCoarseSkeletonReachUpper
import RequestProject.Section31.TraceDistinctDecomposition
import RequestProject.Section31.EIGSSkeletonTraceTransport
import RequestProject.Section31.EIGSAddressSupport

/-! Genuine finite expected exit upper bounds for every fine starting vertex,
uniformly over all actual incident stars. First reaching the coarse skeleton
costs the cell terminal bound; one distinct skeleton jump costs its proved
duration. This does not yet assert continuous mean exit. Candidate source. -/

namespace IGS.Sec31
open scoped Classical BigOperators
variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]

theorem partialHit_except_singleton_le_one (chain : FinChain Vertex) (center : Vertex)
    (noSelfLoop : chain.P center center = 0) :
    ∀ time vertex, partialHit chain (Finset.univ.erase center) time vertex ≤ (1 : ℝ) := by
  let value : Vertex → ℝ := fun vertex => if vertex = center then 1 else 0
  have valueNonnegative : ∀ vertex, 0 ≤ value vertex := by intro vertex; simp only [value]; split <;> norm_num
  have supersolution : ∀ vertex ∉ Finset.univ.erase center,
      1 + ∑ target, chain.P vertex target * value target ≤ value vertex := by
    intro vertex outside
    have equality : vertex = center := by simpa only [Finset.mem_erase, Finset.mem_univ,
      and_true, not_not] using outside
    subst vertex
    simp [value, mul_ite, noSelfLoop]
  intro time vertex
  apply (partialHit_le_of_supersolution chain (Finset.univ.erase center)
    valueNonnegative supersolution time vertex).trans
  dsimp only [value]
  split <;> norm_num

end IGS.Sec31

namespace EIGS
open IGS.Sec31 Filter Topology
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 6000000
variable {K : ℕ}

theorem xiCoarseGroundedDomain_allSource_expExit_spectral_upper (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ upper : ℝ, 0 < upper ∧ ∀ coarse steps (center : XiVtx system coarse)
      (source : XiVtx system (coarse + steps)),
      expExit (XiSimpleGraph system (coarse + steps))
        (xiCoarseGroundedDomain system coarse steps center) source ≤
        upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps := by
  obtain ⟨reachUpper, reachPositive, reachBounds⟩ := xiAllCoarseSkeleton_partialHit_spectral_upper
    system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  obtain ⟨durationUpper, durationPositive, durationBounds⟩ := xiSkeletonDistinctDuration_spectral_upper
    system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  have timePositive : 0 < realMatrixSpectralRadius (massMatrixR system.toRuleData) *
      system.resistanceSpectralRadius rulesConnected distancePositive :=
    mul_pos (eigs_mass_spectral_growth system rulesConnected distancePositive).1
      (system.resistanceSpectralRadius_positive_eigenpair rulesConnected distancePositive).1
  refine ⟨reachUpper + durationUpper, add_pos reachPositive durationPositive, ?_⟩
  intro coarse steps center source
  let boundary := (Finset.univ.erase center).image (xiForward system coarse steps)
  have boundaryNonempty : boundary.Nonempty := by
    obtain ⟨other, otherDistinct⟩ := exists_ne center
    exact ⟨xiForward system coarse steps other,
      Finset.mem_image.mpr ⟨other, Finset.mem_erase.mpr ⟨otherDistinct, Finset.mem_univ _⟩, rfl⟩⟩
  have hitBound := exit_time_le_distinct_skeleton_add_cost
    (xiGraphWalkChain system rulesConnected (coarse + steps))
    (Finset.univ.image (xiForward system coarse steps)) boundary
    (xiGraphWalk_hits_skeleton system rulesConnected coarse steps)
    (reachBounds coarse steps)
    (xiSkeletonTrace_departure_positive system rulesConnected coarse steps rulesLoopless rulesUnique plantingNonadjacent)
    (mul_nonneg durationPositive.le (pow_nonneg timePositive.le steps))
    (by norm_num : (0 : ℝ) ≤ 1) (duration_bound := durationUpper *
      (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps)
    (jump_bound := 1)
    (by
      intro target
      obtain ⟨vertex, rfl⟩ := (xiSkeletonVertexEquiv system coarse steps).surjective target
      change excursionTime (xiGraphWalkChain system rulesConnected (coarse + steps))
        (Finset.univ.image (xiForward system coarse steps)) (xiSkeletonVertexEquiv system coarse steps vertex) /
        (1 - (xiSkeletonTraceChain system rulesConnected coarse steps).P
          (xiSkeletonVertexEquiv system coarse steps vertex) (xiSkeletonVertexEquiv system coarse steps vertex)) ≤ _
      rw [xiSkeletonTrace_duration, xiSkeletonTrace_transition]
      exact durationBounds coarse steps vertex)
    (by
      intro time target
      obtain ⟨vertex, rfl⟩ := (xiSkeletonVertexEquiv system coarse steps).surjective target
      change partialHit (xiSkeletonTraceDistinctChain system rulesConnected coarse steps rulesLoopless
        rulesUnique plantingNonadjacent)
        (termIn (Finset.univ.image (xiForward system coarse steps))
          ((Finset.univ.erase center).image (xiForward system coarse steps))) time
        (xiSkeletonVertexEquiv system coarse steps vertex) ≤ 1
      rw [xiSkeletonTrace_distinct_partialHit]
      exact partialHit_except_singleton_le_one
        (distinctJumpChain (xiSkeletonReturnChain system rulesConnected coarse steps)
          (xiSkeletonReturnChain_departure_positive system rulesConnected rulesLoopless rulesUnique
            plantingNonadjacent coarse steps)) center (by simp [distinctJumpChain]) time vertex)
    source
  have meanEquality := graphWalkChain_hitTime (XiSimpleGraph system (coarse + steps))
    (xiSimpleGraph_connected system rulesConnected (coarse + steps))
    (fun vertex => by exact_mod_cast xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex)
    boundary boundaryNonempty source
  change hitTime (xiGraphWalkChain system rulesConnected (coarse + steps)) boundary source =
    expExit (XiSimpleGraph system (coarse + steps)) boundaryᶜ source at meanEquality
  rw [meanEquality] at hitBound
  have domainEquality : boundaryᶜ = xiCoarseGroundedDomain system coarse steps center := by
    rw [Finset.compl_eq_univ_sdiff]
    rfl
  rw [domainEquality] at hitBound
  simpa only [mul_one, add_mul] using hitBound

theorem xiIncidentStarDomain_allSource_expExit_spectral_upper (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ upper : ℝ, 0 < upper ∧ ∀ coarse steps (center : XiVtx system coarse)
      (source : XiVtx system (coarse + steps)),
      expExit (XiSimpleGraph system (coarse + steps))
        (xiIncidentStarDomain system coarse steps center) source ≤
        upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps := by
  obtain ⟨upper, upperPositive, groundedBounds⟩ := xiCoarseGroundedDomain_allSource_expExit_spectral_upper
    system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  refine ⟨upper, upperPositive, ?_⟩
  intro coarse steps center source
  apply (expExit_mono_domain (xiSimpleGraph_connected system rulesConnected (coarse + steps))
    _ (xiCoarseGroundedDomain_complement_nonempty system coarse steps center) source).trans
    (groundedBounds coarse steps center source)
  intro vertex member
  exact xiIncidentStar_subset_coarseGroundedDomain system coarse steps center
    (Finset.mem_filter.mp member).2

end
end EIGS

#print axioms IGS.Sec31.partialHit_except_singleton_le_one
#print axioms EIGS.xiCoarseGroundedDomain_allSource_expExit_spectral_upper
#print axioms EIGS.xiIncidentStarDomain_allSource_expExit_spectral_upper
