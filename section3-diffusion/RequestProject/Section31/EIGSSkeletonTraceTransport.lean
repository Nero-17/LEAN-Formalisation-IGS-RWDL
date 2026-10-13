import RequestProject.Section31.EIGSCellExitRecursion
import RequestProject.Section31.KilledChainEmbeddingTransport

/-! The actual coarse vertex carrier and the actual finite skeleton subtype
describe the same return chain, durations, distinct jumps and killed costs.
Every probabilistic identification is proved; no exit estimate is an input. -/

namespace EIGS

open IGS.Sec31 Filter Topology
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 3000000

variable {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarse steps : ℕ)

def xiSkeletonVertexEquiv : XiVtx system coarse ≃
    {vertex : XiVtx system (coarse + steps) //
      vertex ∈ Finset.univ.image (xiForward system coarse steps)} :=
  Equiv.ofBijective (fun vertex => ⟨xiForward system coarse steps vertex,
    Finset.mem_image.mpr ⟨vertex, Finset.mem_univ _, rfl⟩⟩) (by
    constructor
    · intro first second equality
      exact xiForward_injective system coarse steps (congrArg Subtype.val equality)
    · intro vertex
      obtain ⟨preimage, _, equality⟩ := Finset.mem_image.mp vertex.property
      exact ⟨preimage, Subtype.ext equality⟩)

theorem xiGraphWalk_hits_skeleton (vertex : XiVtx system (coarse + steps)) :
    Tendsto (fun time => notHit (xiGraphWalkChain system rulesConnected (coarse + steps))
      (Finset.univ.image (xiForward system coarse steps)) time vertex) atTop (nhds 0) := by
  have nonempty : (Finset.univ.image (xiForward system coarse steps)).Nonempty :=
    Finset.image_nonempty.mpr ⟨xiPositiveTerminal system coarse, Finset.mem_univ _⟩
  have summable := expExit_summable (xiSimpleGraph_connected system rulesConnected (coarse + steps))
    (show ((Finset.univ.image (xiForward system coarse steps))ᶜ)ᶜ.Nonempty by
      simpa using nonempty) vertex
  simpa only [xiGraphWalkChain, graphWalkChain_notHit] using summable.tendsto_atTop_zero

def xiSkeletonTraceChain :=
  traceChain (xiGraphWalkChain system rulesConnected (coarse + steps))
    (Finset.univ.image (xiForward system coarse steps))
    (xiGraphWalk_hits_skeleton system rulesConnected coarse steps)

theorem xiSkeletonTrace_transition (source target : XiVtx system coarse) :
    (xiSkeletonTraceChain system rulesConnected coarse steps).P
      (xiSkeletonVertexEquiv system coarse steps source)
      (xiSkeletonVertexEquiv system coarse steps target) =
        (xiSkeletonReturnChain system rulesConnected coarse steps).P source target := rfl

theorem xiSkeletonTrace_boundary_iff (boundary : Finset (XiVtx system coarse))
    (source : XiVtx system coarse) :
    xiSkeletonVertexEquiv system coarse steps source ∈
      termIn (Finset.univ.image (xiForward system coarse steps))
        (boundary.image (xiForward system coarse steps)) ↔ source ∈ boundary := by
  rw [mem_termIn]
  change xiForward system coarse steps source ∈ boundary.image (xiForward system coarse steps) ↔ _
  constructor
  · intro membership
    obtain ⟨preimage, inside, equality⟩ := Finset.mem_image.mp membership
    exact (xiForward_injective system coarse steps equality) ▸ inside
  · intro membership
    exact Finset.mem_image.mpr ⟨source, membership, rfl⟩

theorem xiSkeletonTrace_duration (source : XiVtx system coarse) :
    excursionTime (xiGraphWalkChain system rulesConnected (coarse + steps))
      (Finset.univ.image (xiForward system coarse steps))
      (xiSkeletonVertexEquiv system coarse steps source) =
        xiSkeletonReturnDuration system coarse steps source :=
  (xiSkeletonReturnDuration_eq_excursionTime system rulesConnected coarse steps source).symm

theorem xiSkeletonTrace_raw_cost (boundary : Finset (XiVtx system coarse))
    (time : ℕ) (source : XiVtx system coarse) :
    cost (xiSkeletonTraceChain system rulesConnected coarse steps)
      (termIn (Finset.univ.image (xiForward system coarse steps))
        (boundary.image (xiForward system coarse steps)))
      (excursionTime (xiGraphWalkChain system rulesConnected (coarse + steps))
        (Finset.univ.image (xiForward system coarse steps))) time
      (xiSkeletonVertexEquiv system coarse steps source) =
    cost (xiSkeletonReturnChain system rulesConnected coarse steps) boundary
      (xiSkeletonReturnDuration system coarse steps) time source := by
  apply killedEmbedding_cost (xiSkeletonReturnChain system rulesConnected coarse steps)
    (xiSkeletonTraceChain system rulesConnected coarse steps)
    (xiSkeletonVertexEquiv system coarse steps).toEmbedding boundary _
    (xiSkeletonTrace_boundary_iff system coarse steps boundary)
    (fun first _ second => xiSkeletonTrace_transition system rulesConnected coarse steps first second)
    (fun _ _ target outside => False.elim
      (outside ((xiSkeletonVertexEquiv system coarse steps).surjective target)))
    (xiSkeletonReturnDuration system coarse steps) _
    (fun target _ => xiSkeletonTrace_duration system rulesConnected coarse steps target)

theorem xiSkeletonTrace_raw_costLim (boundary : Finset (XiVtx system coarse))
    (source : XiVtx system coarse) :
    costLim (xiSkeletonTraceChain system rulesConnected coarse steps)
      (termIn (Finset.univ.image (xiForward system coarse steps))
        (boundary.image (xiForward system coarse steps)))
      (excursionTime (xiGraphWalkChain system rulesConnected (coarse + steps))
        (Finset.univ.image (xiForward system coarse steps)))
      (xiSkeletonVertexEquiv system coarse steps source) =
    costLim (xiSkeletonReturnChain system rulesConnected coarse steps) boundary
      (xiSkeletonReturnDuration system coarse steps) source := by
  unfold costLim
  congr 1
  funext time
  exact xiSkeletonTrace_raw_cost system rulesConnected coarse steps boundary time source

variable (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))

include rulesLoopless rulesUnique plantingNonadjacent

theorem xiSkeletonTrace_departure_positive :
    ∀ vertex, 0 < 1 - (xiSkeletonTraceChain system rulesConnected coarse steps).P vertex vertex := by
  intro vertex
  obtain ⟨source, rfl⟩ := (xiSkeletonVertexEquiv system coarse steps).surjective vertex
  rw [xiSkeletonTrace_transition]
  exact xiSkeletonReturnChain_departure_positive system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent coarse steps source

def xiSkeletonTraceDistinctChain :=
  distinctJumpChain (xiSkeletonTraceChain system rulesConnected coarse steps)
    (xiSkeletonTrace_departure_positive system rulesConnected coarse steps rulesLoopless
      rulesUnique plantingNonadjacent)

theorem xiSkeletonTrace_distinct_transition (source target : XiVtx system coarse) :
    (xiSkeletonTraceDistinctChain system rulesConnected coarse steps rulesLoopless rulesUnique
      plantingNonadjacent).P (xiSkeletonVertexEquiv system coarse steps source)
        (xiSkeletonVertexEquiv system coarse steps target) =
    (distinctJumpChain (xiSkeletonReturnChain system rulesConnected coarse steps)
      (xiSkeletonReturnChain_departure_positive system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent coarse steps)).P source target := by
  change (if xiSkeletonVertexEquiv system coarse steps source =
      xiSkeletonVertexEquiv system coarse steps target then 0 else
      (xiSkeletonTraceChain system rulesConnected coarse steps).P
        (xiSkeletonVertexEquiv system coarse steps source)
        (xiSkeletonVertexEquiv system coarse steps target)) /
      (1 - (xiSkeletonTraceChain system rulesConnected coarse steps).P
        (xiSkeletonVertexEquiv system coarse steps source)
        (xiSkeletonVertexEquiv system coarse steps source)) = _
  rw [xiSkeletonTrace_transition, xiSkeletonTrace_transition]
  change (if xiSkeletonVertexEquiv system coarse steps source =
      xiSkeletonVertexEquiv system coarse steps target then 0 else
        (xiSkeletonReturnChain system rulesConnected coarse steps).P source target) /
      (1 - (xiSkeletonReturnChain system rulesConnected coarse steps).P source source) =
    (if source = target then 0 else
        (xiSkeletonReturnChain system rulesConnected coarse steps).P source target) /
      (1 - (xiSkeletonReturnChain system rulesConnected coarse steps).P source source)
  by_cases equal : source = target
  · subst target
    simp
  · simp only [if_neg equal, if_neg ((xiSkeletonVertexEquiv system coarse steps).injective.ne equal)]

theorem xiSkeletonTrace_distinct_partialHit (boundary : Finset (XiVtx system coarse))
    (time : ℕ) (source : XiVtx system coarse) :
    partialHit (xiSkeletonTraceDistinctChain system rulesConnected coarse steps rulesLoopless
      rulesUnique plantingNonadjacent)
      (termIn (Finset.univ.image (xiForward system coarse steps))
        (boundary.image (xiForward system coarse steps))) time
      (xiSkeletonVertexEquiv system coarse steps source) =
    partialHit (distinctJumpChain (xiSkeletonReturnChain system rulesConnected coarse steps)
      (xiSkeletonReturnChain_departure_positive system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent coarse steps)) boundary time source := by
  apply killedEmbedding_partialHit
    (distinctJumpChain (xiSkeletonReturnChain system rulesConnected coarse steps)
      (xiSkeletonReturnChain_departure_positive system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent coarse steps))
    (xiSkeletonTraceDistinctChain system rulesConnected coarse steps rulesLoopless rulesUnique
      plantingNonadjacent) (xiSkeletonVertexEquiv system coarse steps).toEmbedding boundary _
    (xiSkeletonTrace_boundary_iff system coarse steps boundary)
    (fun first _ second => xiSkeletonTrace_distinct_transition system rulesConnected coarse steps
      rulesLoopless rulesUnique plantingNonadjacent first second)
    (fun _ _ target outside => False.elim
      (outside ((xiSkeletonVertexEquiv system coarse steps).surjective target)))

theorem xiSkeletonTrace_distinct_cost (boundary : Finset (XiVtx system coarse))
    (time : ℕ) (source : XiVtx system coarse) :
    cost (xiSkeletonTraceDistinctChain system rulesConnected coarse steps rulesLoopless rulesUnique
      plantingNonadjacent)
      (termIn (Finset.univ.image (xiForward system coarse steps))
        (boundary.image (xiForward system coarse steps)))
      (fun vertex => excursionTime (xiGraphWalkChain system rulesConnected (coarse + steps))
          (Finset.univ.image (xiForward system coarse steps)) vertex /
        (1 - (xiSkeletonTraceChain system rulesConnected coarse steps).P vertex vertex)) time
      (xiSkeletonVertexEquiv system coarse steps source) =
    cost (distinctJumpChain (xiSkeletonReturnChain system rulesConnected coarse steps)
      (xiSkeletonReturnChain_departure_positive system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent coarse steps)) boundary
      (fun vertex => xiSkeletonReturnDuration system coarse steps vertex /
        (1 - (xiSkeletonReturnChain system rulesConnected coarse steps).P vertex vertex)) time source := by
  apply killedEmbedding_cost
    (distinctJumpChain (xiSkeletonReturnChain system rulesConnected coarse steps)
      (xiSkeletonReturnChain_departure_positive system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent coarse steps))
    (xiSkeletonTraceDistinctChain system rulesConnected coarse steps rulesLoopless rulesUnique
      plantingNonadjacent) (xiSkeletonVertexEquiv system coarse steps).toEmbedding boundary _
    (xiSkeletonTrace_boundary_iff system coarse steps boundary)
    (fun first _ second => xiSkeletonTrace_distinct_transition system rulesConnected coarse steps
      rulesLoopless rulesUnique plantingNonadjacent first second)
    (fun _ _ target outside => False.elim
      (outside ((xiSkeletonVertexEquiv system coarse steps).surjective target)))
  intro target _
  change excursionTime (xiGraphWalkChain system rulesConnected (coarse + steps))
      (Finset.univ.image (xiForward system coarse steps))
      (xiSkeletonVertexEquiv system coarse steps target) /
      (1 - (xiSkeletonTraceChain system rulesConnected coarse steps).P
        (xiSkeletonVertexEquiv system coarse steps target)
        (xiSkeletonVertexEquiv system coarse steps target)) = _
  rw [xiSkeletonTrace_duration, xiSkeletonTrace_transition]

theorem xiSkeletonTrace_distinct_costLim (boundary : Finset (XiVtx system coarse))
    (source : XiVtx system coarse) :
    costLim (xiSkeletonTraceDistinctChain system rulesConnected coarse steps rulesLoopless rulesUnique
      plantingNonadjacent)
      (termIn (Finset.univ.image (xiForward system coarse steps))
        (boundary.image (xiForward system coarse steps)))
      (fun vertex => excursionTime (xiGraphWalkChain system rulesConnected (coarse + steps))
          (Finset.univ.image (xiForward system coarse steps)) vertex /
        (1 - (xiSkeletonTraceChain system rulesConnected coarse steps).P vertex vertex))
      (xiSkeletonVertexEquiv system coarse steps source) =
    costLim (distinctJumpChain (xiSkeletonReturnChain system rulesConnected coarse steps)
      (xiSkeletonReturnChain_departure_positive system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent coarse steps)) boundary
      (fun vertex => xiSkeletonReturnDuration system coarse steps vertex /
        (1 - (xiSkeletonReturnChain system rulesConnected coarse steps).P vertex vertex)) source := by
  unfold costLim
  congr 1
  funext time
  exact xiSkeletonTrace_distinct_cost system rulesConnected coarse steps rulesLoopless rulesUnique
    plantingNonadjacent boundary time source

end
end EIGS

#print axioms EIGS.xiSkeletonVertexEquiv
#print axioms EIGS.xiGraphWalk_hits_skeleton
#print axioms EIGS.xiSkeletonTrace_transition
#print axioms EIGS.xiSkeletonTrace_boundary_iff
#print axioms EIGS.xiSkeletonTrace_duration
#print axioms EIGS.xiSkeletonTrace_raw_cost
#print axioms EIGS.xiSkeletonTrace_raw_costLim
#print axioms EIGS.xiSkeletonTrace_departure_positive
#print axioms EIGS.xiSkeletonTrace_distinct_transition
#print axioms EIGS.xiSkeletonTrace_distinct_partialHit
#print axioms EIGS.xiSkeletonTrace_distinct_cost
#print axioms EIGS.xiSkeletonTrace_distinct_costLim
