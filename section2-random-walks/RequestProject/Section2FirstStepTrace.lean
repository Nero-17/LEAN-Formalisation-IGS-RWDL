import RequestProject.Section31.EIGSMesoscopicTrace

/-! Actual first-generation restriction of a unit fine-network minimizer.
The remaining-depth resistance is the actual Psi iterate, with no stationary
or trace-compatibility premise. -/

namespace EIGS

open scoped Classical

variable {K : ℕ}

theorem xiUnitPotentialAt_first_restriction (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (coarse depth : ℕ) (old_values : XiVtx system coarse → ℝ) :
    (fun vertex : XiVtx system (coarse + 1) =>
      xiUnitPotentialAt system rule_connected coarse ((coarse + 1) + depth)
        (by omega) old_values (xiVertexInclusion system (coarse + 1) ((coarse + 1) + depth)
          (Nat.le_add_right _ _) vertex)) =
      xiPotentialStep system rule_connected ((system.ruleFamily rule_connected).Psi^[depth] (fun _ => 1))
        (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) depth)
        coarse old_values := by
  classical
  let restricted := fun vertex : XiVtx system (coarse + 1) =>
    xiUnitPotentialAt system rule_connected coarse ((coarse + 1) + depth) (by omega) old_values
      (xiVertexInclusion system (coarse + 1) ((coarse + 1) + depth) (Nat.le_add_right _ _) vertex)
  have restricted_old : ∀ vertex, restricted (Sum.inl vertex) = old_values vertex := by
    intro vertex
    have first_inclusion : xiVertexInclusion system coarse (coarse + 1) (Nat.le_add_right _ _) vertex =
        Sum.inl vertex := by rw [xiVertexInclusion_eq_forward]; rfl
    dsimp [restricted]
    rw [← first_inclusion, xiVertexInclusion_comp, xiUnitPotentialAt_boundary]
  change restricted = _
  apply (XiNetwork system (coarse + 1)).potential_minimum_unique
    ((system.ruleFamily rule_connected).Psi^[depth] (fun _ => 1))
    (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) depth)
    (xiSimpleGraph_connected system rule_connected _) (Finset.univ.image Sum.inl)
    ⟨Sum.inl (xiPositiveTerminal system coarse), by simp⟩ restricted
  · intro _ _; rfl
  · intro vertex membership
    obtain ⟨old_vertex, _, rfl⟩ := Finset.mem_image.mp membership
    exact (xiPotentialStep_old system rule_connected _ _ coarse old_values old_vertex).trans
      (restricted_old old_vertex).symm
  · intro competitor competitor_boundary
    have competitor_old : ∀ vertex, competitor (xiVertexInclusion system coarse (coarse + 1)
        (Nat.le_add_right _ _) vertex) = old_values vertex := by
      intro vertex
      rw [xiVertexInclusion_eq_forward]
      exact (competitor_boundary (Sum.inl vertex) (by simp)).trans (restricted_old vertex)
    simpa only [Nat.add_sub_cancel_left] using xiUnitPotentialAt_mesoscopic_minimal system rule_connected
      coarse (coarse + 1) ((coarse + 1) + depth) (Nat.le_add_right _ _) (Nat.le_add_right _ _)
      old_values competitor competitor_old
  · intro competitor competitor_boundary
    apply xiPotentialStep_minimal system rule_connected _ _ coarse old_values competitor
    intro vertex
    exact (competitor_boundary (Sum.inl vertex) (by simp)).trans (restricted_old vertex)

end EIGS

#print axioms EIGS.xiUnitPotentialAt_first_restriction
