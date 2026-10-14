import RequestProject.Section31.EIGSAllCoarseSkeletonReachUpper
import RequestProject.Section31.EIGSTwoPointSkeletonJumpBound
import RequestProject.Section31.TraceDistinctDecomposition
import RequestProject.Section31.EIGSSkeletonTraceTransport

/-! Actual two-endpoint grounded domains and the union of their incident
stars have a uniform expected exit upper bound from every fine source.
The original-rule conductance and neighbour proofs fill the jump bound.
Candidate source; continuous ball expectation is still a subsequent bridge. -/

namespace EIGS
open IGS.Sec31 Filter Topology
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 7000000
variable {K : ℕ}

def xiTwoPointCoarseGroundedDomain (system : EIGSData K) (coarse steps : ℕ)
    (first second : XiVtx system coarse) : Finset (XiVtx system (coarse + steps)) :=
  Finset.univ \ (({first, second} : Finset (XiVtx system coarse))ᶜ.image (xiForward system coarse steps))

theorem xiTwoIncidentStars_subset_grounded_pair (system : EIGSData K)
    (coarse steps : ℕ) (first second : XiVtx system coarse) :
    xiIncidentStarDomain system coarse steps first ∪ xiIncidentStarDomain system coarse steps second ⊆
      xiTwoPointCoarseGroundedDomain system coarse steps first second := by
  intro vertex inStars
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro inBoundary
  obtain ⟨other, outsidePair, rfl⟩ := Finset.mem_image.mp inBoundary
  rcases Finset.mem_union.mp inStars with firstStar | secondStar
  · have equality := (xiIncidentStar_forward_iff system coarse steps first other).mp
      (Finset.mem_filter.mp firstStar).2
    exact Finset.mem_compl.mp outsidePair (by simp [equality])
  · have equality := (xiIncidentStar_forward_iff system coarse steps second other).mp
      (Finset.mem_filter.mp secondStar).2
    exact Finset.mem_compl.mp outsidePair (by simp [equality])

theorem xiTwoPointCoarseGroundedDomain_allSource_expExit_spectral_upper (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ upper : ℝ, 0 < upper ∧ ∀ coarse, 1 ≤ coarse →
      ∀ steps (first second : XiVtx system coarse), (XiSimpleGraph system coarse).Adj first second →
      ∀ source : XiVtx system (coarse + steps),
        expExit (XiSimpleGraph system (coarse + steps))
          (xiTwoPointCoarseGroundedDomain system coarse steps first second) source ≤
          upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
            system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps := by
  obtain ⟨reachUpper, reachPositive, reachBounds⟩ := xiAllCoarseSkeleton_partialHit_spectral_upper
    system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  obtain ⟨durationUpper, durationPositive, durationBounds⟩ := xiSkeletonDistinctDuration_spectral_upper
    system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  obtain ⟨jumpUpper, jumpPositive, jumpBounds⟩ := exists_xiTwoPointSkeleton_uniform_jumps
    system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  have timePositive : 0 < realMatrixSpectralRadius (massMatrixR system.toRuleData) *
      system.resistanceSpectralRadius rulesConnected distancePositive :=
    mul_pos (eigs_mass_spectral_growth system rulesConnected distancePositive).1
      (system.resistanceSpectralRadius_positive_eigenpair rulesConnected distancePositive).1
  refine ⟨reachUpper + durationUpper * jumpUpper, by positivity, ?_⟩
  intro coarse coarsePositive steps first second adjacent source
  let boundary := ({first, second} : Finset (XiVtx system coarse))ᶜ.image (xiForward system coarse steps)
  obtain ⟨endpoint, exterior, _, exteriorFirst, exteriorSecond, _⟩ :=
    xiPositiveCoarse_pair_has_exterior_neighbor system rulesConnected plantingNonadjacent
      coarse coarsePositive first second
  have boundaryNonempty : boundary.Nonempty :=
    ⟨xiForward system coarse steps exterior,
      Finset.mem_image.mpr ⟨exterior, by simp [exteriorFirst, exteriorSecond], rfl⟩⟩
  have hitBound := exit_time_le_distinct_skeleton_add_cost
    (xiGraphWalkChain system rulesConnected (coarse + steps))
    (Finset.univ.image (xiForward system coarse steps)) boundary
    (xiGraphWalk_hits_skeleton system rulesConnected coarse steps) (reachBounds coarse steps)
    (xiSkeletonTrace_departure_positive system rulesConnected coarse steps rulesLoopless rulesUnique plantingNonadjacent)
    (mul_nonneg durationPositive.le (pow_nonneg timePositive.le steps)) jumpPositive.le
    (duration_bound := durationUpper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
      system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps) (jump_bound := jumpUpper)
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
          (({first, second} : Finset (XiVtx system coarse))ᶜ.image (xiForward system coarse steps))) time
        (xiSkeletonVertexEquiv system coarse steps vertex) ≤ jumpUpper
      rw [xiSkeletonTrace_distinct_partialHit]
      exact jumpBounds coarse coarsePositive steps first second adjacent time vertex)
    source
  have meanEquality := graphWalkChain_hitTime (XiSimpleGraph system (coarse + steps))
    (xiSimpleGraph_connected system rulesConnected (coarse + steps))
    (fun vertex => by exact_mod_cast xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex)
    boundary boundaryNonempty source
  change hitTime (xiGraphWalkChain system rulesConnected (coarse + steps)) boundary source =
    expExit (XiSimpleGraph system (coarse + steps)) boundaryᶜ source at meanEquality
  rw [meanEquality] at hitBound
  have domainEquality : boundaryᶜ = xiTwoPointCoarseGroundedDomain system coarse steps first second := by
    rw [Finset.compl_eq_univ_sdiff]
    rfl
  rw [domainEquality] at hitBound
  exact hitBound.trans_eq (by ring)

end
end EIGS

#print axioms EIGS.xiTwoIncidentStars_subset_grounded_pair
#print axioms EIGS.xiTwoPointCoarseGroundedDomain_allSource_expExit_spectral_upper
