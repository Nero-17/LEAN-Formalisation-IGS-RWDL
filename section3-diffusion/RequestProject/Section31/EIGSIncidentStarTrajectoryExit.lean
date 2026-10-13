import RequestProject.Section31.EIGSIncidentStarBoundaryLocalization
import RequestProject.Section31.EIGSCellStarExit

/-! Deterministic finite-trajectory identities on actual fine graphs.
Leaving a star for the first time is precisely the first visit to another
coarse vertex. The positive-transition version uses the actual graph walk.
No harmonic-law or stopping-time equivalence is assumed. -/

namespace EIGS

open scoped Classical
variable {K : ℕ}

def xiTrajectoryFirstStarExit (system : EIGSData K) (coarse steps : ℕ)
    (center : XiVtx system coarse) (trajectory : ℕ → XiVtx system (coarse + steps))
    (time : ℕ) : Prop :=
  trajectory time ∉ xiIncidentStarDomain system coarse steps center ∧
    ∀ earlier, earlier < time → trajectory earlier ∈ xiIncidentStarDomain system coarse steps center

def xiTrajectoryFirstDistinctCoarseHit (system : EIGSData K) (coarse steps : ℕ)
    (center : XiVtx system coarse) (trajectory : ℕ → XiVtx system (coarse + steps))
    (time : ℕ) : Prop :=
  (∃ other : XiVtx system coarse, other ≠ center ∧ trajectory time = xiForward system coarse steps other) ∧
    ∀ earlier, earlier < time → ∀ other : XiVtx system coarse, other ≠ center →
      trajectory earlier ≠ xiForward system coarse steps other

theorem xiIncidentStarDomain_trajectory_mem_of_avoids (system : EIGSData K) (coarse steps : ℕ)
    (center : XiVtx system coarse) (trajectory : ℕ → XiVtx system (coarse + steps))
    (time : ℕ) (start : trajectory 0 = xiForward system coarse steps center)
    (adjacency : ∀ index, index < time →
      (XiSimpleGraph system (coarse + steps)).Adj (trajectory index) (trajectory (index + 1)))
    (avoids : ∀ index, index ≤ time → ∀ other : XiVtx system coarse, other ≠ center →
      trajectory index ≠ xiForward system coarse steps other) :
    ∀ index, index ≤ time → trajectory index ∈ xiIncidentStarDomain system coarse steps center := by
  intro index
  induction index with
  | zero =>
      intro _
      simpa only [start] using xiIncidentStarDomain_center_mem system coarse steps center
  | succ index induction_hypothesis =>
      intro before
      have previous := induction_hypothesis ((Nat.le_succ index).trans before)
      by_contra outside
      obtain ⟨other, different, same⟩ := xiIncidentStarDomain_adj_outside system coarse steps center
        previous outside (adjacency index ((Nat.lt_succ_self index).trans_le before))
      exact avoids (index + 1) before other different same

theorem xiIncidentStarDomain_first_exit_iff_first_distinct_hit (system : EIGSData K)
    (coarse steps : ℕ) (center : XiVtx system coarse)
    (trajectory : ℕ → XiVtx system (coarse + steps)) (time : ℕ)
    (start : trajectory 0 = xiForward system coarse steps center)
    (adjacency : ∀ index, index < time →
      (XiSimpleGraph system (coarse + steps)).Adj (trajectory index) (trajectory (index + 1))) :
    xiTrajectoryFirstStarExit system coarse steps center trajectory time ↔
      xiTrajectoryFirstDistinctCoarseHit system coarse steps center trajectory time := by
  unfold xiTrajectoryFirstStarExit xiTrajectoryFirstDistinctCoarseHit
  constructor
  · rintro ⟨outside, earlier_inside⟩
    cases time with
    | zero =>
        exact (outside (by
          simpa only [start] using xiIncidentStarDomain_center_mem system coarse steps center)).elim
    | succ previous =>
        refine ⟨xiIncidentStarDomain_adj_outside system coarse steps center
          (earlier_inside previous (Nat.lt_succ_self previous)) outside
          (adjacency previous (Nat.lt_succ_self previous)), ?_⟩
        intro earlier before other different same
        have inside := earlier_inside earlier before
        rw [same] at inside
        exact different ((xiIncidentStarDomain_forward_mem_iff system coarse steps center other).mp inside)
  · rintro ⟨⟨other, different, same⟩, earlier_avoids⟩
    constructor
    · intro inside
      rw [same] at inside
      exact different ((xiIncidentStarDomain_forward_mem_iff system coarse steps center other).mp inside)
    · intro earlier before
      apply xiIncidentStarDomain_trajectory_mem_of_avoids system coarse steps center trajectory earlier
        start (fun index index_before => adjacency index (index_before.trans before))
        (fun index index_before => earlier_avoids index (index_before.trans_lt before))
        earlier (le_refl earlier)

/-- The same exact event identity for every finite trajectory supported by
positive transitions of the genuine simple random walk. -/
theorem xiGraphWalk_first_star_exit_iff_first_distinct_hit (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarse steps : ℕ) (center : XiVtx system coarse)
    (trajectory : ℕ → XiVtx system (coarse + steps)) (time : ℕ)
    (start : trajectory 0 = xiForward system coarse steps center)
    (support : ∀ index, index < time →
      0 < (xiGraphWalkChain system rulesConnected (coarse + steps)).P
        (trajectory index) (trajectory (index + 1))) :
    xiTrajectoryFirstStarExit system coarse steps center trajectory time ↔
      xiTrajectoryFirstDistinctCoarseHit system coarse steps center trajectory time := by
  apply xiIncidentStarDomain_first_exit_iff_first_distinct_hit system coarse steps center trajectory time start
  intro index before
  by_contra nonadjacent
  have positive := support index before
  change 0 < transProb (XiSimpleGraph system (coarse + steps))
    (trajectory index) (trajectory (index + 1)) at positive
  simp [transProb, nonadjacent] at positive

end EIGS

#print axioms EIGS.xiIncidentStarDomain_trajectory_mem_of_avoids
#print axioms EIGS.xiIncidentStarDomain_first_exit_iff_first_distinct_hit
#print axioms EIGS.xiGraphWalk_first_star_exit_iff_first_distinct_hit
