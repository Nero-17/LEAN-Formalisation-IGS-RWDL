import RequestProject.Section31.EIGSWeightedTrace

/-! Actual multiscale potential traces. Repeated attained one-step minima give
the trace on every fixed coarse Xi vertex set, with colour resistances equal
to the corresponding nonlinear renormalization iterate. -/

namespace EIGS

open IGS.Sec31

variable {K : ℕ}

theorem ruleFamily_Psi_positive (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour) :
    ∀ colour, 0 < (system.ruleFamily rulesConnected).Psi resistances colour := by
  intro colour
  obtain ⟨profile, profileSource, profileSink, profileMinimum, profileEnergy⟩ :=
    (system.ruleNetwork colour).exists_minimum_potential_energy_eq_inverse_effRes resistances
      resistancesPositive (rulesConnected colour) (system.plantPlus colour) (system.plantMinus colour)
        (system.plant_ne colour)
  have energyPositive := (system.ruleNetwork colour).potential_energy_pos_of_boundary_unit resistances
    resistancesPositive (system.plantPlus colour) (system.plantMinus colour) (system.plant_ne colour)
      ((system.ruleFamily rulesConnected).connected colour) profile profileSource profileSink
  rw [profileEnergy] at energyPositive
  exact inv_pos.1 energyPositive

theorem ruleFamily_Psi_iterate_positive (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (offset : ℕ) :
    ∀ colour, 0 < (system.ruleFamily rulesConnected).Psi^[offset] resistances colour := by
  induction offset generalizing resistances with
  | zero => exact resistancesPositive
  | succ offset induction =>
      rw [Function.iterate_succ_apply]
      exact induction _ (ruleFamily_Psi_positive system rulesConnected resistances resistancesPositive)

theorem exists_xiPotential_succ_trace (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (level : ℕ) (oldValues : XiVtx system level → ℝ) :
    ∃ extension : XiVtx system (level + 1) → ℝ,
      (∀ vertex, extension (Sum.inl vertex) = oldValues vertex) ∧
      ((XiNetwork system (level + 1)).potentialNetwork resistances resistancesPositive).energy extension =
        ((XiNetwork system level).potentialNetwork ((system.ruleFamily rulesConnected).Psi resistances)
          (ruleFamily_Psi_positive system rulesConnected resistances resistancesPositive)).energy oldValues ∧
      ∀ competitor : XiVtx system (level + 1) → ℝ,
        (∀ vertex, competitor (Sum.inl vertex) = oldValues vertex) →
        ((XiNetwork system level).potentialNetwork ((system.ruleFamily rulesConnected).Psi resistances)
          (ruleFamily_Psi_positive system rulesConnected resistances resistancesPositive)).energy oldValues ≤
        ((XiNetwork system (level + 1)).potentialNetwork resistances resistancesPositive).energy competitor := by
  obtain ⟨extension, extensionOld, extensionEnergy, lowerBound⟩ :=
    (XiNetwork system level).exists_substituted_potential_trace (system.ruleFamily rulesConnected)
      resistances resistancesPositive rulesConnected oldValues
  have traceValue : (∑ edge : (XiNetwork system level).E,
      (oldValues ((XiNetwork system level).tail edge) - oldValues ((XiNetwork system level).head edge)) ^ 2 *
        ((system.ruleFamily rulesConnected).Psi resistances ((XiNetwork system level).color edge))⁻¹) =
      ((XiNetwork system level).potentialNetwork ((system.ruleFamily rulesConnected).Psi resistances)
        (ruleFamily_Psi_positive system rulesConnected resistances resistancesPositive)).energy oldValues := by
    simp only [FiniteNetwork.energy, Network.potentialNetwork]
    apply Finset.sum_congr rfl
    intro edge _
    ring
  refine ⟨extension, extensionOld, ?_, ?_⟩
  · exact extensionEnergy.trans traceValue
  · intro competitor competitorOld
    rw [← traceValue]
    exact lowerBound competitor competitorOld

theorem xiPotential_succ_restriction_le (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (level : ℕ) (values : XiVtx system (level + 1) → ℝ) :
    ((XiNetwork system level).potentialNetwork ((system.ruleFamily rulesConnected).Psi resistances)
      (ruleFamily_Psi_positive system rulesConnected resistances resistancesPositive)).energy
        (fun vertex => values (Sum.inl vertex)) ≤
      ((XiNetwork system (level + 1)).potentialNetwork resistances resistancesPositive).energy values := by
  obtain ⟨extension, extensionOld, extensionEnergy, lowerBound⟩ :=
    exists_xiPotential_succ_trace system rulesConnected resistances resistancesPositive level
      (fun vertex => values (Sum.inl vertex))
  exact lowerBound values (fun _ => rfl)

theorem exists_xiPotential_iterated_trace (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarseLevel offset : ℕ) (resistances : Fin K → ℝ)
    (resistancesPositive : ∀ colour, 0 < resistances colour)
    (oldValues : XiVtx system coarseLevel → ℝ) :
    ∃ extension : XiVtx system (coarseLevel + offset) → ℝ,
      (∀ vertex, extension (xiForward system coarseLevel offset vertex) = oldValues vertex) ∧
      ((XiNetwork system (coarseLevel + offset)).potentialNetwork resistances resistancesPositive).energy extension =
        ((XiNetwork system coarseLevel).potentialNetwork ((system.ruleFamily rulesConnected).Psi^[offset] resistances)
          (ruleFamily_Psi_iterate_positive system rulesConnected resistances resistancesPositive offset)).energy oldValues ∧
      ∀ competitor : XiVtx system (coarseLevel + offset) → ℝ,
        (∀ vertex, competitor (xiForward system coarseLevel offset vertex) = oldValues vertex) →
        ((XiNetwork system coarseLevel).potentialNetwork ((system.ruleFamily rulesConnected).Psi^[offset] resistances)
          (ruleFamily_Psi_iterate_positive system rulesConnected resistances resistancesPositive offset)).energy oldValues ≤
        ((XiNetwork system (coarseLevel + offset)).potentialNetwork resistances resistancesPositive).energy competitor := by
  induction offset generalizing resistances with
  | zero =>
      refine ⟨oldValues, fun _ => rfl, rfl, ?_⟩
      intro competitor competitorOld
      have competitorEquality : competitor = oldValues := funext competitorOld
      rw [competitorEquality]
      exact le_rfl
  | succ offset induction =>
      obtain ⟨middleValues, middleBoundary, middleEnergy, middleLowerBound⟩ :=
        induction ((system.ruleFamily rulesConnected).Psi resistances)
          (ruleFamily_Psi_positive system rulesConnected resistances resistancesPositive)
      obtain ⟨extension, extensionMiddle, extensionEnergy, extensionLowerBound⟩ :=
        exists_xiPotential_succ_trace system rulesConnected resistances resistancesPositive
          (coarseLevel + offset) middleValues
      refine ⟨extension, ?_, ?_, ?_⟩
      · intro vertex
        exact (extensionMiddle (xiForward system coarseLevel offset vertex)).trans (middleBoundary vertex)
      · calc
          _ = ((XiNetwork system (coarseLevel + offset)).potentialNetwork
              ((system.ruleFamily rulesConnected).Psi resistances)
                (ruleFamily_Psi_positive system rulesConnected resistances resistancesPositive)).energy middleValues :=
            extensionEnergy
          _ = _ := by simpa only [Function.iterate_succ_apply] using middleEnergy
      · intro competitor competitorOld
        have middleComparison := middleLowerBound (fun vertex => competitor (Sum.inl vertex))
          (fun vertex => competitorOld vertex)
        have fineComparison := xiPotential_succ_restriction_le system rulesConnected resistances resistancesPositive
          (coarseLevel + offset) competitor
        simpa only [Function.iterate_succ_apply] using middleComparison.trans fineComparison

theorem exists_xiUnit_iterated_trace (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarseLevel offset : ℕ) (oldValues : XiVtx system coarseLevel → ℝ) :
    ∃ extension : XiVtx system (coarseLevel + offset) → ℝ,
      (∀ vertex, extension (xiForward system coarseLevel offset vertex) = oldValues vertex) ∧
      ((XiNetwork system (coarseLevel + offset)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy extension =
        ((XiNetwork system coarseLevel).potentialNetwork ((system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1))
          (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1) (fun _ => by norm_num) offset)).energy oldValues ∧
      ∀ competitor : XiVtx system (coarseLevel + offset) → ℝ,
        (∀ vertex, competitor (xiForward system coarseLevel offset vertex) = oldValues vertex) →
        ((XiNetwork system coarseLevel).potentialNetwork ((system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1))
          (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1) (fun _ => by norm_num) offset)).energy oldValues ≤
        ((XiNetwork system (coarseLevel + offset)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy competitor :=
  exists_xiPotential_iterated_trace system rulesConnected coarseLevel offset (fun _ => 1) (fun _ => by norm_num) oldValues

theorem xiPotential_iterated_restriction_le (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarseLevel offset : ℕ) (resistances : Fin K → ℝ)
    (resistancesPositive : ∀ colour, 0 < resistances colour)
    (values : XiVtx system (coarseLevel + offset) → ℝ) :
    ((XiNetwork system coarseLevel).potentialNetwork ((system.ruleFamily rulesConnected).Psi^[offset] resistances)
      (ruleFamily_Psi_iterate_positive system rulesConnected resistances resistancesPositive offset)).energy
        (fun vertex => values (xiForward system coarseLevel offset vertex)) ≤
      ((XiNetwork system (coarseLevel + offset)).potentialNetwork resistances resistancesPositive).energy values := by
  obtain ⟨extension, extensionBoundary, extensionEnergy, lowerBound⟩ :=
    exists_xiPotential_iterated_trace system rulesConnected coarseLevel offset resistances resistancesPositive
      (fun vertex => values (xiForward system coarseLevel offset vertex))
  exact lowerBound values (fun _ => rfl)

end EIGS
