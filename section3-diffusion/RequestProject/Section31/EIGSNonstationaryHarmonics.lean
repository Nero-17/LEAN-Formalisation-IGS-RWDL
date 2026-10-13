import RequestProject.Section31.EIGSDiscreteTraceGram
import RequestProject.Section31.EIGSCellOscillation
import RequestProject.Section31.HarmonicProfileContinuity

/-! Constructive harmonic traces for arbitrary positive colour resistances.
The intermediate resistance changes by Psi at each reverse substitution step.
No resistance eigenpair or stationary harmonic profile is assumed. -/

namespace EIGS

open IGS.Sec31

set_option maxHeartbeats 1600000

variable {K : ℕ}

section Connected

variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)

noncomputable def xiPotentialStep (resistances : Fin K → ℝ)
    (resistancesPositive : ∀ colour, 0 < resistances colour)
    (level : ℕ) (oldValues : XiVtx system level → ℝ) : XiVtx system (level + 1) → ℝ :=
  Classical.choose (exists_xiPotential_succ_trace system rulesConnected resistances resistancesPositive level oldValues)

theorem xiPotentialStep_old (resistances : Fin K → ℝ)
    (resistancesPositive : ∀ colour, 0 < resistances colour)
    (level : ℕ) (oldValues : XiVtx system level → ℝ) (vertex : XiVtx system level) :
    xiPotentialStep system rulesConnected resistances resistancesPositive level oldValues (Sum.inl vertex) = oldValues vertex :=
  (Classical.choose_spec (exists_xiPotential_succ_trace system rulesConnected resistances resistancesPositive level oldValues)).1 vertex

theorem xiPotentialStep_energy (resistances : Fin K → ℝ)
    (resistancesPositive : ∀ colour, 0 < resistances colour)
    (level : ℕ) (oldValues : XiVtx system level → ℝ) :
    ((XiNetwork system (level + 1)).potentialNetwork resistances resistancesPositive).energy
      (xiPotentialStep system rulesConnected resistances resistancesPositive level oldValues) =
      ((XiNetwork system level).potentialNetwork ((system.ruleFamily rulesConnected).Psi resistances)
        (ruleFamily_Psi_positive system rulesConnected resistances resistancesPositive)).energy oldValues :=
  (Classical.choose_spec (exists_xiPotential_succ_trace system rulesConnected resistances resistancesPositive level oldValues)).2.1

theorem xiPotentialStep_minimal (resistances : Fin K → ℝ)
    (resistancesPositive : ∀ colour, 0 < resistances colour)
    (level : ℕ) (oldValues : XiVtx system level → ℝ) (competitor : XiVtx system (level + 1) → ℝ)
    (competitorOld : ∀ vertex, competitor (Sum.inl vertex) = oldValues vertex) :
    ((XiNetwork system (level + 1)).potentialNetwork resistances resistancesPositive).energy
      (xiPotentialStep system rulesConnected resistances resistancesPositive level oldValues) ≤
      ((XiNetwork system (level + 1)).potentialNetwork resistances resistancesPositive).energy competitor := by
  rw [xiPotentialStep_energy]
  exact (Classical.choose_spec (exists_xiPotential_succ_trace system rulesConnected resistances resistancesPositive
    level oldValues)).2.2 competitor competitorOld

theorem xiPotentialStep_eq_affine_profiles (resistances : Fin K → ℝ)
    (resistancesPositive : ∀ colour, 0 < resistances colour)
    (profiles : ∀ colour, (system.rule colour).V → ℝ)
    (profilesPlus : ∀ colour, profiles colour (system.plantPlus colour) = 1)
    (profilesMinus : ∀ colour, profiles colour (system.plantMinus colour) = 0)
    (profilesMinimal : ∀ colour (competitor : (system.rule colour).V → ℝ),
      competitor (system.plantPlus colour) = 1 → competitor (system.plantMinus colour) = 0 →
      ((system.ruleNetwork colour).potentialNetwork resistances resistancesPositive).energy (profiles colour) ≤
        ((system.ruleNetwork colour).potentialNetwork resistances resistancesPositive).energy competitor)
    (level : ℕ) (oldValues : XiVtx system level → ℝ) :
    xiPotentialStep system rulesConnected resistances resistancesPositive level oldValues =
      (XiNetwork system level).substAffineProfiles (system.ruleFamily rulesConnected) profiles oldValues := by
  classical
  apply (XiNetwork system (level + 1)).potential_minimum_unique resistances resistancesPositive
    (xiSimpleGraph_connected system rulesConnected (level + 1)) (Finset.univ.image Sum.inl)
    ⟨Sum.inl (xiPositiveTerminal system level), by simp⟩
    (fun vertex => match vertex with
      | Sum.inl oldVertex => oldValues oldVertex
      | Sum.inr _ => 0)
  · intro vertex membership
    obtain ⟨oldVertex, _, rfl⟩ := Finset.mem_image.1 membership
    exact xiPotentialStep_old system rulesConnected resistances resistancesPositive level oldValues oldVertex
  · intro vertex membership
    obtain ⟨oldVertex, _, rfl⟩ := Finset.mem_image.1 membership
    rfl
  · intro competitor competitorBoundary
    exact xiPotentialStep_minimal system rulesConnected resistances resistancesPositive level oldValues
      competitor (fun vertex => competitorBoundary (Sum.inl vertex) (by simp))
  · intro competitor competitorBoundary
    simpa only [xiPotentialEnergy_succ_eq_substituted system rulesConnected] using
      (XiNetwork system level).substAffineProfiles_minimal (system.ruleFamily rulesConnected)
        resistances resistancesPositive profiles profilesPlus profilesMinus profilesMinimal oldValues competitor
        (fun vertex => competitorBoundary (Sum.inl vertex) (by simp))

theorem xiPotentialStep_rule_vertex_range (resistances : Fin K → ℝ)
    (resistancesPositive : ∀ colour, 0 < resistances colour)
    (level : ℕ) (oldValues : XiVtx system level → ℝ)
    (edge : XiEdge system.toRuleData level)
    (vertex : (system.rule (XiCol system.toRuleData level edge)).V) :
    min (oldValues (XiTail system level edge)) (oldValues (XiHead system level edge)) ≤
        xiPotentialStep system rulesConnected resistances resistancesPositive level oldValues
          (embedRuleVtx system level edge (XiTail system level edge) (XiHead system level edge) vertex) ∧
      xiPotentialStep system rulesConnected resistances resistancesPositive level oldValues
          (embedRuleVtx system level edge (XiTail system level edge) (XiHead system level edge) vertex) ≤
        max (oldValues (XiTail system level edge)) (oldValues (XiHead system level edge)) := by
  classical
  have profilesExist := fun colour =>
    (system.ruleNetwork colour).exists_minimum_potential_energy_eq_inverse_effRes resistances
      resistancesPositive (rulesConnected colour) (system.plantPlus colour) (system.plantMinus colour)
        (system.plant_ne colour)
  choose profiles profilesPlus profilesMinus profilesMinimal profilesEnergy using profilesExist
  have profileRange := (system.ruleNetwork (XiCol system.toRuleData level edge)).unit_potential_minimum_range
    resistances resistancesPositive (rulesConnected _) _ _ (profiles _)
      (profilesPlus _) (profilesMinus _) (profilesMinimal _) vertex
  rw [xiPotentialStep_eq_affine_profiles system rulesConnected resistances resistancesPositive profiles
    profilesPlus profilesMinus profilesMinimal]
  change min (oldValues (XiTail system level edge)) (oldValues (XiHead system level edge)) ≤
      (XiNetwork system level).substAffineProfiles (system.ruleFamily rulesConnected) profiles oldValues
        ((XiNetwork system level).substEmbed (system.ruleFamily rulesConnected) edge vertex) ∧
    (XiNetwork system level).substAffineProfiles (system.ruleFamily rulesConnected) profiles oldValues
        ((XiNetwork system level).substEmbed (system.ruleFamily rulesConnected) edge vertex) ≤
      max (oldValues (XiTail system level edge)) (oldValues (XiHead system level edge))
  rw [(XiNetwork system level).substAffineProfiles_restrict (system.ruleFamily rulesConnected)
    profiles profilesPlus profilesMinus]
  change min (oldValues (XiTail system level edge)) (oldValues (XiHead system level edge)) ≤
      oldValues (XiHead system level edge) +
        (oldValues (XiTail system level edge) - oldValues (XiHead system level edge)) *
          profiles (XiCol system.toRuleData level edge) vertex ∧
    oldValues (XiHead system level edge) +
        (oldValues (XiTail system level edge) - oldValues (XiHead system level edge)) *
          profiles (XiCol system.toRuleData level edge) vertex ≤
      max (oldValues (XiTail system level edge)) (oldValues (XiHead system level edge))
  by_cases endpointsOrdered : oldValues (XiTail system level edge) ≤ oldValues (XiHead system level edge)
  · rw [min_eq_left endpointsOrdered, max_eq_right endpointsOrdered]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 endpointsOrdered) (sub_nonneg.2 profileRange.2)]
    · nlinarith [mul_nonneg (sub_nonneg.2 endpointsOrdered) profileRange.1]
  · have reverseOrder := le_of_not_ge endpointsOrdered
    rw [min_eq_right reverseOrder, max_eq_left reverseOrder]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 reverseOrder) profileRange.1]
    · nlinarith [mul_nonneg (sub_nonneg.2 reverseOrder) (sub_nonneg.2 profileRange.2)]

noncomputable def xiPotentialValues (initialLevel : ℕ) :
    (offset : ℕ) → (resistances : Fin K → ℝ) →
      (∀ colour, 0 < resistances colour) → (XiVtx system initialLevel → ℝ) →
        (XiVtx system (initialLevel + offset) → ℝ)
  | 0, _, _, initialValues => initialValues
  | offset + 1, resistances, resistancesPositive, initialValues =>
      xiPotentialStep system rulesConnected resistances resistancesPositive (initialLevel + offset)
        (xiPotentialValues initialLevel offset ((system.ruleFamily rulesConnected).Psi resistances)
          (ruleFamily_Psi_positive system rulesConnected resistances resistancesPositive) initialValues)

theorem xiPotentialValues_boundary (initialLevel offset : ℕ)
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (initialValues : XiVtx system initialLevel → ℝ) (vertex : XiVtx system initialLevel) :
    xiPotentialValues system rulesConnected initialLevel offset resistances resistancesPositive initialValues
      (xiForward system initialLevel offset vertex) = initialValues vertex := by
  induction offset generalizing resistances with
  | zero => rfl
  | succ offset induction =>
      exact (xiPotentialStep_old system rulesConnected resistances resistancesPositive (initialLevel + offset)
        _ (xiForward system initialLevel offset vertex)).trans
          (induction _ (ruleFamily_Psi_positive system rulesConnected resistances resistancesPositive))

theorem xiPotentialValues_energy (initialLevel offset : ℕ)
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (initialValues : XiVtx system initialLevel → ℝ) :
    ((XiNetwork system (initialLevel + offset)).potentialNetwork resistances resistancesPositive).energy
      (xiPotentialValues system rulesConnected initialLevel offset resistances resistancesPositive initialValues) =
      ((XiNetwork system initialLevel).potentialNetwork ((system.ruleFamily rulesConnected).Psi^[offset] resistances)
        (ruleFamily_Psi_iterate_positive system rulesConnected resistances resistancesPositive offset)).energy initialValues := by
  induction offset generalizing resistances with
  | zero => rfl
  | succ offset induction =>
      exact (xiPotentialStep_energy system rulesConnected resistances resistancesPositive (initialLevel + offset) _).trans
        (by simpa only [Function.iterate_succ_apply] using
          induction _ (ruleFamily_Psi_positive system rulesConnected resistances resistancesPositive))

theorem xiPotentialValues_minimal (initialLevel offset : ℕ)
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (initialValues : XiVtx system initialLevel → ℝ) (competitor : XiVtx system (initialLevel + offset) → ℝ)
    (competitorBoundary : ∀ vertex, competitor (xiForward system initialLevel offset vertex) = initialValues vertex) :
    ((XiNetwork system (initialLevel + offset)).potentialNetwork resistances resistancesPositive).energy
      (xiPotentialValues system rulesConnected initialLevel offset resistances resistancesPositive initialValues) ≤
      ((XiNetwork system (initialLevel + offset)).potentialNetwork resistances resistancesPositive).energy competitor := by
  rw [xiPotentialValues_energy]
  exact (Classical.choose_spec (exists_xiPotential_iterated_trace system rulesConnected initialLevel offset
    resistances resistancesPositive initialValues)).2.2 competitor competitorBoundary

theorem xiPotentialValues_descendant_endpoint_range (initialLevel : ℕ)
    (initialValues : XiVtx system initialLevel → ℝ) :
    ∀ offset (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
      (edge : XiEdge system.toRuleData (initialLevel + offset)),
      (min (initialValues (XiTail system initialLevel (xiAncestorEdge system initialLevel offset edge)))
          (initialValues (XiHead system initialLevel (xiAncestorEdge system initialLevel offset edge))) ≤
        xiPotentialValues system rulesConnected initialLevel offset resistances resistancesPositive initialValues
          (XiTail system (initialLevel + offset) edge) ∧
       xiPotentialValues system rulesConnected initialLevel offset resistances resistancesPositive initialValues
          (XiTail system (initialLevel + offset) edge) ≤
        max (initialValues (XiTail system initialLevel (xiAncestorEdge system initialLevel offset edge)))
          (initialValues (XiHead system initialLevel (xiAncestorEdge system initialLevel offset edge)))) ∧
      (min (initialValues (XiTail system initialLevel (xiAncestorEdge system initialLevel offset edge)))
          (initialValues (XiHead system initialLevel (xiAncestorEdge system initialLevel offset edge))) ≤
        xiPotentialValues system rulesConnected initialLevel offset resistances resistancesPositive initialValues
          (XiHead system (initialLevel + offset) edge) ∧
       xiPotentialValues system rulesConnected initialLevel offset resistances resistancesPositive initialValues
          (XiHead system (initialLevel + offset) edge) ≤
        max (initialValues (XiTail system initialLevel (xiAncestorEdge system initialLevel offset edge)))
          (initialValues (XiHead system initialLevel (xiAncestorEdge system initialLevel offset edge)))) := by
  intro offset
  induction offset with
  | zero =>
      intro resistances resistancesPositive edge
      exact ⟨⟨min_le_left _ _, le_max_left _ _⟩, ⟨min_le_right _ _, le_max_right _ _⟩⟩
  | succ offset induction =>
      intro resistances resistancesPositive edge
      have parentRange := induction ((system.ruleFamily rulesConnected).Psi resistances)
        (ruleFamily_Psi_positive system rulesConnected resistances resistancesPositive) edge.1
      have tailRange := xiPotentialStep_rule_vertex_range system rulesConnected resistances resistancesPositive
        (initialLevel + offset)
        (xiPotentialValues system rulesConnected initialLevel offset ((system.ruleFamily rulesConnected).Psi resistances)
          (ruleFamily_Psi_positive system rulesConnected resistances resistancesPositive) initialValues)
        edge.1 ((system.rule _).tail edge.2)
      have headRange := xiPotentialStep_rule_vertex_range system rulesConnected resistances resistancesPositive
        (initialLevel + offset)
        (xiPotentialValues system rulesConnected initialLevel offset ((system.ruleFamily rulesConnected).Psi resistances)
          (ruleFamily_Psi_positive system rulesConnected resistances resistancesPositive) initialValues)
        edge.1 ((system.rule _).head edge.2)
      exact ⟨⟨(le_min parentRange.1.1 parentRange.2.1).trans tailRange.1,
          tailRange.2.trans (max_le parentRange.1.2 parentRange.2.2)⟩,
        ⟨(le_min parentRange.1.1 parentRange.2.1).trans headRange.1,
          headRange.2.trans (max_le parentRange.1.2 parentRange.2.2)⟩⟩

theorem xiPotentialValues_unique (initialLevel offset : ℕ)
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (initialValues : XiVtx system initialLevel → ℝ) (candidate : XiVtx system (initialLevel + offset) → ℝ)
    (candidateBoundary : ∀ vertex, candidate (xiForward system initialLevel offset vertex) = initialValues vertex)
    (candidateMinimal : ∀ competitor : XiVtx system (initialLevel + offset) → ℝ,
      (∀ vertex, competitor (xiForward system initialLevel offset vertex) = initialValues vertex) →
      ((XiNetwork system (initialLevel + offset)).potentialNetwork resistances resistancesPositive).energy candidate ≤
        ((XiNetwork system (initialLevel + offset)).potentialNetwork resistances resistancesPositive).energy competitor) :
    candidate = xiPotentialValues system rulesConnected initialLevel offset resistances resistancesPositive initialValues := by
  classical
  apply (XiNetwork system (initialLevel + offset)).potential_minimum_unique resistances resistancesPositive
    (xiSimpleGraph_connected system rulesConnected (initialLevel + offset))
    (Finset.univ.image (xiForward system initialLevel offset))
    ⟨xiForward system initialLevel offset (xiPositiveTerminal system initialLevel), by simp⟩ candidate
  · intro _ _; rfl
  · intro vertex membership
    obtain ⟨coarseVertex, _, rfl⟩ := Finset.mem_image.1 membership
    exact (xiPotentialValues_boundary system rulesConnected initialLevel offset resistances resistancesPositive
      initialValues coarseVertex).trans (candidateBoundary coarseVertex).symm
  · intro competitor competitorBoundary
    apply candidateMinimal competitor
    intro vertex
    exact (competitorBoundary _ (by simp)).trans (candidateBoundary vertex)
  · intro competitor competitorBoundary
    apply xiPotentialValues_minimal system rulesConnected initialLevel offset resistances resistancesPositive initialValues competitor
    intro vertex
    exact (competitorBoundary _ (by simp)).trans (candidateBoundary vertex)

theorem xiUnitTraceExtension_eq_potentialValues (initialLevel offset : ℕ)
    (initialValues : XiVtx system initialLevel → ℝ) :
    xiUnitTraceExtension system rulesConnected initialLevel offset initialValues =
      xiPotentialValues system rulesConnected initialLevel offset (fun _ => 1) (fun _ => by norm_num) initialValues :=
  xiPotentialValues_unique system rulesConnected initialLevel offset (fun _ => 1) (fun _ => by norm_num)
    initialValues (xiUnitTraceExtension system rulesConnected initialLevel offset initialValues)
    (xiUnitTraceExtension_boundary system rulesConnected initialLevel offset initialValues)
    (xiUnitTraceExtension_minimal system rulesConnected initialLevel offset initialValues)

end Connected

end EIGS
