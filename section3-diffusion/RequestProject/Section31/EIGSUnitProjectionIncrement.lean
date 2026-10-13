import RequestProject.Section31.EIGSUnitProjectionAlgebra
import RequestProject.Section31.EIGSOneStepCellEnergy

/-! Adjacent actual energy projections have a harmonic, old-boundary-zero
difference. The native norm estimate is applied to that concrete difference. -/

namespace EIGS

variable {K : ℕ}

noncomputable section

variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)

theorem xiUnitEnergyProjection_eq_potentialValues (initialLevel offset : ℕ)
    (values : XiVtx system (initialLevel + offset) → ℝ) :
    xiUnitEnergyProjection system rulesConnected initialLevel (initialLevel + offset) (Nat.le_add_right _ _) values =
    xiPotentialValues system rulesConnected initialLevel offset (fun _ => 1) (fun _ => by norm_num)
      (fun vertex => values (xiForward system initialLevel offset vertex)) := by
  apply xiPotentialValues_unique system rulesConnected initialLevel offset (fun _ => 1) (fun _ => by norm_num)
  · intro vertex
    simpa only [xiVertexInclusion_eq_forward] using
      xiUnitEnergyProjection_boundary system rulesConnected initialLevel (initialLevel + offset) (Nat.le_add_right _ _) values vertex
  · intro competitor competitorBoundary
    apply xiUnitEnergyProjection_minimal system rulesConnected initialLevel (initialLevel + offset) (Nat.le_add_right _ _) values competitor
    intro vertex
    simpa only [xiVertexInclusion_eq_forward] using competitorBoundary vertex

def xiUnitProjectionIncrement (level offset : ℕ)
    (values : XiVtx system (level + 1 + offset) → ℝ) : XiVtx system (level + 1 + offset) → ℝ :=
  xiUnitEnergyProjection system rulesConnected (level + 1) (level + 1 + offset) (by omega) values -
    xiUnitEnergyProjection system rulesConnected level (level + 1 + offset) (by omega) values

theorem xiUnitProjectionIncrement_fixed (level offset : ℕ)
    (values : XiVtx system (level + 1 + offset) → ℝ) :
    xiUnitEnergyProjection system rulesConnected (level + 1) (level + 1 + offset) (by omega)
      (xiUnitProjectionIncrement system rulesConnected level offset values) =
      xiUnitProjectionIncrement system rulesConnected level offset values := by
  unfold xiUnitProjectionIncrement
  have linear := xiUnitEnergyProjection_linear system rulesConnected (level + 1) (level + 1 + offset) (by omega)
    (xiUnitEnergyProjection system rulesConnected (level + 1) (level + 1 + offset) (by omega) values)
    (xiUnitEnergyProjection system rulesConnected level (level + 1 + offset) (by omega) values) 1 (-1)
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at linear
  rw [xiUnitEnergyProjection_finer_fixed system rulesConnected (level + 1) (level + 1) (level + 1 + offset) le_rfl (by omega),
    xiUnitEnergyProjection_finer_fixed system rulesConnected level (level + 1) (level + 1 + offset) (by omega) (by omega)] at linear
  exact linear

theorem xiUnitProjectionIncrement_harmonic (level offset : ℕ)
    (values : XiVtx system (level + 1 + offset) → ℝ) :
    xiUnitProjectionIncrement system rulesConnected level offset values =
      xiPotentialValues system rulesConnected (level + 1) offset (fun _ => 1) (fun _ => by norm_num)
        (fun vertex => xiUnitProjectionIncrement system rulesConnected level offset values
          (xiForward system (level + 1) offset vertex)) := by
  rw [← xiUnitEnergyProjection_eq_potentialValues, xiUnitProjectionIncrement_fixed]

theorem xiUnitProjectionIncrement_old_zero (level offset : ℕ)
    (values : XiVtx system (level + 1 + offset) → ℝ) (vertex : XiVtx system level) :
    xiUnitProjectionIncrement system rulesConnected level offset values
      (xiForward system (level + 1) offset (Sum.inl vertex)) = 0 := by
  have inclusionSucc : xiVertexInclusion system level (level + 1) (by omega) vertex = Sum.inl vertex := by
    rw [xiVertexInclusion_eq_forward]
    rfl
  have inclusionComp := xiVertexInclusion_comp system level (level + 1) (level + 1 + offset) (by omega) (by omega) vertex
  rw [inclusionSucc, xiVertexInclusion_eq_forward] at inclusionComp
  rw [inclusionComp]
  exact xiUnitEnergyProjection_increment_zero system rulesConnected level (level + 1) (level + 1 + offset) (by omega) (by omega) values vertex

theorem xiUnitProjectionIncrement_energy_le (level offset : ℕ)
    (values : XiVtx system (level + 1 + offset) → ℝ) :
    ((XiNetwork system (level + 1 + offset)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy
      (xiUnitProjectionIncrement system rulesConnected level offset values) ≤
    ((XiNetwork system (level + 1 + offset)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy values :=
  xiUnitEnergyProjection_increment_energy_le system rulesConnected level (level + 1) (level + 1 + offset) (by omega) (by omega) values

theorem exists_xiUnitProjectionIncrement_native_bound (mass : XiMassParameters system) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ level offset (upper : ℝ),
      (∀ colour, (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour ≤ upper) →
      ∀ values : XiVtx system (level + 1 + offset) → ℝ,
      ‖xiFiniteSpeedL2 system mass (level + 1 + offset)
        (xiUnitProjectionIncrement system rulesConnected level offset values)‖ ^ 2 ≤
      constant / mass.rate ^ (level + 1) * upper *
        ((XiNetwork system (level + 1 + offset)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy values := by
  obtain ⟨constant, constantPositive, harmonicBound⟩ := exists_xiStep_harmonic_native_energy_bound system rulesConnected mass
  refine ⟨constant, constantPositive, ?_⟩
  intro level offset upper resistancesBounded values
  have upperPositive : 0 < upper :=
    (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1) (fun _ => by norm_num) offset system.initCol).trans_le
      (resistancesBounded system.initCol)
  have comparison := harmonicBound level offset (fun _ => 1) (fun _ => by norm_num) upper resistancesBounded
    (fun vertex => xiUnitProjectionIncrement system rulesConnected level offset values (xiForward system (level + 1) offset vertex))
    (xiUnitProjectionIncrement_old_zero system rulesConnected level offset values)
  rw [← xiUnitProjectionIncrement_harmonic] at comparison
  exact comparison.trans (mul_le_mul_of_nonneg_left
    (xiUnitProjectionIncrement_energy_le system rulesConnected level offset values)
    (mul_pos (div_pos constantPositive (pow_pos mass.rate_positive _)) upperPositive).le)

end

end EIGS
