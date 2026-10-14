import RequestProject.Section31.EIGSOneStepCellEnergy
import RequestProject.Section31.EIGSAddressSupport
import RequestProject.Section31.EIGSHarmonicContraction
import RequestProject.Section31.EnergyOrthogonality

/-! Uniform one-step deviation from actual weighted harmonic interpolation.
This is a finite-network estimate. Summing its geometric square roots when
resistanceRate > 1 will construct the continuous extension of every bounded
trace-energy function, rather than assume resistance-form continuity. -/

namespace EIGS

open IGS.Sec31
noncomputable section
variable {K : ℕ}

theorem exists_xiStep_zero_boundary_sup_energy_bound
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ level (resistances : Fin K → ℝ)
      (resistancesPositive : ∀ colour, 0 < resistances colour) (upper : ℝ),
      (∀ colour, resistances colour ≤ upper) →
      ∀ values : XiVtx system (level + 1) → ℝ,
      (∀ vertex : XiVtx system level, values (Sum.inl vertex) = 0) →
      ∀ vertex, (values vertex) ^ 2 ≤ constant * upper *
        ((XiNetwork system (level + 1)).potentialNetwork resistances resistancesPositive).energy values := by
  classical
  obtain ⟨constant, positive, control⟩ := exists_xiStep_endpoint_energy_bound system rulesConnected
  refine ⟨constant, positive, ?_⟩
  intro level resistances resistancesPositive upper upperBound values oldZero vertex
  obtain ⟨edge, incident⟩ := xiVertex_has_incident_edge system rulesConnected (level + 1) vertex
  have singleBound : (values (XiTail system (level + 1) edge)) ^ 2 +
      (values (XiHead system (level + 1) edge)) ^ 2 ≤
      ∑ other : XiEdge system.toRuleData (level + 1),
        ((values (XiTail system (level + 1) other)) ^ 2 +
          (values (XiHead system (level + 1) other)) ^ 2) :=
    Finset.single_le_sum (fun other _ => add_nonneg
      (sq_nonneg (values (XiTail system (level + 1) other)))
      (sq_nonneg (values (XiHead system (level + 1) other))))
      (Finset.mem_univ edge)
  have pointBound : (values vertex) ^ 2 ≤
      (values (XiTail system (level + 1) edge)) ^ 2 +
        (values (XiHead system (level + 1) edge)) ^ 2 := by
    rcases incident with tail | head
    · rw [tail]
      exact le_add_of_nonneg_right (sq_nonneg _)
    · rw [head]
      exact le_add_of_nonneg_left (sq_nonneg _)
  exact pointBound.trans (singleBound.trans
    (control level resistances resistancesPositive upper upperBound values oldZero))

theorem exists_xiHarmonicStep_deviation_sup_energy_bound
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
        (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
        (renormalizationEigenpair : ∀ colour,
          (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
        (upper : ℝ), (∀ colour, resistanceVector colour ≤ upper) →
      ∀ level (values : XiVtx system (level + 1) → ℝ) vertex,
        (values vertex - xiHarmonicStep system rulesConnected resistanceRate ratePositive
          resistanceVector vectorPositive renormalizationEigenpair level
            (fun old => values (Sum.inl old)) vertex) ^ 2 ≤
          constant * upper / resistanceRate ^ (level + 1) *
            (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive
              (level + 1)).energy values := by
  obtain ⟨constant, positive, control⟩ := exists_xiStep_zero_boundary_sup_energy_bound system rulesConnected
  refine ⟨constant, positive, ?_⟩
  intro resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair upper upperBound
    level values vertex
  let harmonic := xiHarmonicStep system rulesConnected resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair level (fun old => values (Sum.inl old))
  let network := (XiNetwork system (level + 1)).potentialNetwork resistanceVector vectorPositive
  have harmonicBoundary : ∀ point ∈ Set.range (Sum.inl : XiVtx system level → XiVtx system (level + 1)),
      harmonic point = values point := by
    rintro point ⟨old, rfl⟩
    exact xiHarmonicStep_old system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive renormalizationEigenpair level (fun old => values (Sum.inl old)) old
  have harmonicMinimal : ∀ competitor : XiVtx system (level + 1) → ℝ,
      (∀ point ∈ Set.range (Sum.inl : XiVtx system level → XiVtx system (level + 1)),
        competitor point = values point) → network.energy harmonic ≤ network.energy competitor := by
    intro competitor boundary
    exact xiHarmonicStep_potential_minimal system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive renormalizationEigenpair level (fun old => values (Sum.inl old)) competitor
        (fun old => boundary (Sum.inl old) ⟨old, rfl⟩)
  have decomposition := network.energy_sub_of_min
    (Set.range (Sum.inl : XiVtx system level → XiVtx system (level + 1)))
      values harmonic harmonicBoundary harmonicMinimal values (fun _ _ => rfl)
  have differenceBound : network.energy (values - harmonic) ≤ network.energy values := by
    linarith [network.energy_nonneg harmonic]
  have oldZero : ∀ old : XiVtx system level, (values - harmonic) (Sum.inl old) = 0 := by
    intro old
    change values (Sum.inl old) - harmonic (Sum.inl old) = 0
    rw [harmonicBoundary _ ⟨old, rfl⟩, sub_self]
  have pointBound := control level resistanceVector vectorPositive upper upperBound (values - harmonic) oldZero vertex
  have upperPositive : 0 < upper := (vectorPositive system.initCol).trans_le (upperBound system.initCol)
  have enlarged := pointBound.trans (mul_le_mul_of_nonneg_left differenceBound
    (mul_pos positive upperPositive).le)
  rw [xiWeightedFiniteNetwork_energy_eq_potential]
  have equality : constant * upper / resistanceRate ^ (level + 1) *
      (resistanceRate ^ (level + 1) * network.energy values) = constant * upper * network.energy values := by
    field_simp
  rw [equality]
  exact enlarged

end
end EIGS

#print axioms EIGS.exists_xiStep_zero_boundary_sup_energy_bound
#print axioms EIGS.exists_xiHarmonicStep_deviation_sup_energy_bound
