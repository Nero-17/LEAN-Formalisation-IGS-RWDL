import RequestProject.Section31.TwoVertexConductanceExitBound
import RequestProject.Section31.EIGSSkeletonConductanceUniformEdgeBounds
import RequestProject.Section31.EIGSCoarsePairExteriorNeighbor

/-! The actual distinct coarse trace leaves the two endpoints of every
coarse edge in a uniformly bounded expected number of jumps. Original rules
fill both exterior-neighbour geometry and normalized conductance bounds.
No exit-probability estimate is assumed. Candidate source. -/

namespace EIGS
open IGS.Sec31
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 7000000
variable {K : ℕ}

theorem exists_xiTwoPointSkeleton_uniform_jumps (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ jumpBound : ℝ, 0 < jumpBound ∧ ∀ coarse, 1 ≤ coarse →
      ∀ steps (first second : XiVtx system coarse), (XiSimpleGraph system coarse).Adj first second →
      ∀ time source,
        partialHit (distinctJumpChain (xiSkeletonReturnChain system rulesConnected coarse steps)
          (xiSkeletonReturnChain_departure_positive system rulesConnected rulesLoopless rulesUnique
            plantingNonadjacent coarse steps)) ({first, second} : Finset (XiVtx system coarse))ᶜ time source ≤
          jumpBound := by
  obtain ⟨lower, upper, lowerPositive, upperPositive, entryUpper, edgeLower⟩ :=
    exists_xiNormalizedSkeletonConductance_edge_bounds system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  let probability := lower / (upper + lower)
  have probabilityPositive : 0 < probability := div_pos lowerPositive (add_pos upperPositive lowerPositive)
  have probabilityAtMostOne : probability ≤ 1 := by
    apply (div_le_one (add_pos upperPositive lowerPositive)).mpr
    linarith
  have ratePositive := (system.resistanceSpectralRadius_positive_eigenpair rulesConnected distancePositive).1
  refine ⟨2 / probability, div_pos (by norm_num) probabilityPositive, ?_⟩
  intro coarse coarsePositive steps first second adjacent time source
  let conductance := xiNormalizedSkeletonConductance system rulesConnected distancePositive coarse steps
  have conductanceNonnegative : ∀ left right, 0 ≤ conductance left right :=
    fun left right => mul_nonneg (pow_nonneg ratePositive.le steps)
      (xiSkeletonConductance_nonnegative system rulesConnected coarse steps left right)
  have conductanceRowPositive : ∀ left, 0 < ∑ right, conductance left right := by
    intro left
    change 0 < ∑ right, (system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps *
      xiSkeletonConductance system rulesConnected coarse steps left right
    rw [← Finset.mul_sum]
    exact mul_pos (pow_pos ratePositive steps) (xiSkeletonConductance_row_positive system rulesConnected coarse steps left)
  let chain := condChain conductance conductanceNonnegative conductanceRowPositive
  have chainEquality : chain = distinctJumpChain (xiSkeletonReturnChain system rulesConnected coarse steps)
      (xiSkeletonReturnChain_departure_positive system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent coarse steps) := by
    rw [xiSkeleton_distinctJumpChain_eq_conductance system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent coarse steps]
    exact condChain_scale (xiSkeletonConductance system rulesConnected coarse steps)
      (xiSkeletonConductance_nonnegative system rulesConnected coarse steps)
      (xiSkeletonConductance_row_positive system rulesConnected coarse steps)
      ((system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps) (pow_pos ratePositive steps)
  have noSelfLoop (vertex : XiVtx system coarse) : chain.P vertex vertex = 0 := by
    change ((system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps *
      xiSkeletonConductance system rulesConnected coarse steps vertex vertex) /
      (∑ target, conductance vertex target) = 0
    rw [xiSkeletonConductance_diagonal system rulesConnected rulesLoopless]
    simp
  obtain ⟨endpoint, exterior, atEndpoint, exteriorFirst, exteriorSecond, exteriorAdjacent⟩ :=
    xiPositiveCoarse_pair_has_exterior_neighbor system rulesConnected plantingNonadjacent
      coarse coarsePositive first second
  rcases atEndpoint with rfl | rfl
  · have escape := conductance_one_exterior_edge_escape conductance conductanceNonnegative conductanceRowPositive
      first second exterior exteriorSecond lower upper lowerPositive upperPositive
      (entryUpper coarse steps first second) (edgeLower coarse steps first exterior exteriorAdjacent)
    have bound := two_vertex_partialHit_le chain first second adjacent.ne (noSelfLoop first) (noSelfLoop second)
      probability probabilityPositive probabilityAtMostOne escape time source
    rw [chainEquality] at bound
    exact bound
  · have escape := conductance_one_exterior_edge_escape conductance conductanceNonnegative conductanceRowPositive
      second first exterior exteriorFirst lower upper lowerPositive upperPositive
      (entryUpper coarse steps second first) (edgeLower coarse steps second exterior exteriorAdjacent)
    have bound := two_vertex_partialHit_le chain second first adjacent.ne.symm (noSelfLoop second) (noSelfLoop first)
      probability probabilityPositive probabilityAtMostOne escape time source
    rw [chainEquality] at bound
    simpa only [Finset.pair_comm second first] using bound

end
end EIGS

#print axioms EIGS.exists_xiTwoPointSkeleton_uniform_jumps
