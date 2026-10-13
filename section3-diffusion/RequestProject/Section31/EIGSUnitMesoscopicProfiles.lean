import RequestProject.Section31.EIGSMesoscopicTrace

/-! Actual original-unit fine minimizers at fixed mesoscopic boundaries.
The full fine minimizer is identified by proved finite Dirichlet uniqueness,
so the existing profile continuity applies to its actual restrictions. -/

namespace EIGS

open IGS.Sec31 Filter Topology

set_option maxHeartbeats 1800000

variable {K : ℕ}

noncomputable def xiMesoscopicBoundary (system : EIGSData K) (coarseLevel middleLevel : ℕ)
    (levelsOrdered : coarseLevel ≤ middleLevel) : Finset (XiVtx system middleLevel) :=
  Finset.univ.image (xiVertexInclusion system coarseLevel middleLevel levelsOrdered)

theorem xiMesoscopicBoundary_nonempty (system : EIGSData K) (coarseLevel middleLevel : ℕ)
    (levelsOrdered : coarseLevel ≤ middleLevel) :
    (xiMesoscopicBoundary system coarseLevel middleLevel levelsOrdered).Nonempty := by
  classical
  exact ⟨xiVertexInclusion system coarseLevel middleLevel levelsOrdered (xiPositiveTerminal system coarseLevel), by simp [xiMesoscopicBoundary]⟩

theorem xiUnitPotentialAt_eq_mesoscopic_boundaryProfile (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarseLevel middleLevel offset : ℕ) (levelsOrdered : coarseLevel ≤ middleLevel)
    (oldValues : XiVtx system coarseLevel → ℝ) (middleBoundaryValues : XiVtx system middleLevel → ℝ)
    (boundaryAgreement : ∀ vertex,
      middleBoundaryValues (xiVertexInclusion system coarseLevel middleLevel levelsOrdered vertex) = oldValues vertex) :
    xiUnitPotentialAt system rulesConnected coarseLevel (middleLevel + offset)
        (levelsOrdered.trans (Nat.le_add_right _ _)) oldValues =
      xiUnitBoundaryProfile system rulesConnected middleLevel offset
        (xiMesoscopicBoundary system coarseLevel middleLevel levelsOrdered)
        (xiMesoscopicBoundary_nonempty system coarseLevel middleLevel levelsOrdered) middleBoundaryValues := by
  classical
  apply (XiNetwork system (middleLevel + offset)).potential_minimum_unique (fun _ => 1) (fun _ => by norm_num)
    (xiSimpleGraph_connected system rulesConnected (middleLevel + offset))
    (Finset.univ.image (xiVertexInclusion system coarseLevel (middleLevel + offset) (levelsOrdered.trans (Nat.le_add_right _ _))))
    ⟨xiVertexInclusion system coarseLevel (middleLevel + offset) (levelsOrdered.trans (Nat.le_add_right _ _))
      (xiPositiveTerminal system coarseLevel), by simp⟩
    (xiUnitPotentialAt system rulesConnected coarseLevel (middleLevel + offset)
      (levelsOrdered.trans (Nat.le_add_right _ _)) oldValues)
  · intro _ _; rfl
  · intro vertex membership
    obtain ⟨coarseVertex, _, rfl⟩ := Finset.mem_image.1 membership
    rw [← xiVertexInclusion_comp system coarseLevel middleLevel (middleLevel + offset) levelsOrdered (Nat.le_add_right _ _),
      xiVertexInclusion_eq_forward, xiUnitBoundaryProfile_boundary]
    · have fineBoundary := xiUnitPotentialAt_boundary system rulesConnected coarseLevel (middleLevel + offset)
        (levelsOrdered.trans (Nat.le_add_right _ _)) oldValues coarseVertex
      rw [← xiVertexInclusion_comp system coarseLevel middleLevel (middleLevel + offset) levelsOrdered (Nat.le_add_right _ _),
        xiVertexInclusion_eq_forward] at fineBoundary
      exact (boundaryAgreement coarseVertex).trans fineBoundary.symm
    · simp [xiMesoscopicBoundary]
  · intro competitor competitorBoundary
    apply xiUnitPotentialAt_minimal system rulesConnected coarseLevel (middleLevel + offset)
      (levelsOrdered.trans (Nat.le_add_right _ _)) oldValues competitor
    intro vertex
    exact (competitorBoundary _ (by simp)).trans
      (xiUnitPotentialAt_boundary system rulesConnected coarseLevel (middleLevel + offset)
        (levelsOrdered.trans (Nat.le_add_right _ _)) oldValues vertex)
  · intro competitor competitorBoundary
    apply xiUnitBoundaryProfile_minimal system rulesConnected middleLevel offset
      (xiMesoscopicBoundary system coarseLevel middleLevel levelsOrdered)
      (xiMesoscopicBoundary_nonempty system coarseLevel middleLevel levelsOrdered) middleBoundaryValues competitor
    intro vertex membership
    obtain ⟨coarseVertex, _, rfl⟩ := Finset.mem_image.1 membership
    rw [← xiVertexInclusion_eq_forward system middleLevel offset,
      xiVertexInclusion_comp, competitorBoundary _ (by simp), xiUnitPotentialAt_boundary, boundaryAgreement]

theorem xiUnitPotentialAt_mesoscopic_restriction_tendsto (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate normalization : ℝ) (ratePositive : 0 < resistanceRate)
    (normalizationPositive : 0 < normalization) (resistanceVector : Fin K → ℝ)
    (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector)))
    (coarseLevel middleLevel : ℕ) (levelsOrdered : coarseLevel ≤ middleLevel)
    (oldValues : XiVtx system coarseLevel → ℝ) (middleBoundaryValues : XiVtx system middleLevel → ℝ)
    (boundaryAgreement : ∀ vertex,
      middleBoundaryValues (xiVertexInclusion system coarseLevel middleLevel levelsOrdered vertex) = oldValues vertex) :
    Tendsto (fun offset => ‖(fun vertex : XiVtx system middleLevel =>
        xiUnitPotentialAt system rulesConnected coarseLevel (middleLevel + offset)
          (levelsOrdered.trans (Nat.le_add_right _ _)) oldValues
          (xiVertexInclusion system middleLevel (middleLevel + offset) (Nat.le_add_right _ _) vertex)) -
      (fun vertex : XiVtx system middleLevel => (XiNetwork system middleLevel).boundaryPotentialProfile resistanceVector vectorPositive
        (xiSimpleGraph_connected system rulesConnected middleLevel)
        (xiMesoscopicBoundary system coarseLevel middleLevel levelsOrdered)
        (xiMesoscopicBoundary_nonempty system coarseLevel middleLevel levelsOrdered) middleBoundaryValues vertex)‖)
      atTop (nhds 0) := by
  have convergence := xiUnitBoundaryProfile_restriction_tendsto system rulesConnected resistanceRate normalization
    ratePositive normalizationPositive resistanceVector vectorPositive normalizedConvergence middleLevel
    (xiMesoscopicBoundary system coarseLevel middleLevel levelsOrdered)
    (xiMesoscopicBoundary_nonempty system coarseLevel middleLevel levelsOrdered) middleBoundaryValues
  apply convergence.congr
  intro offset
  rw [xiUnitPotentialAt_eq_mesoscopic_boundaryProfile system rulesConnected coarseLevel middleLevel offset levelsOrdered
    oldValues middleBoundaryValues boundaryAgreement]
  simp only [xiVertexInclusion_eq_forward]

end EIGS
