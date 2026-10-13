import RequestProject.Section31.EIGSDiscreteTraceConvergence
import RequestProject.Section31.EIGSDiscreteTraceProfileAlgebra

set_option maxHeartbeats 800000

/-! Actual unit-resistance fine-graph harmonic extensions from a fixed coarse
boundary. Their coarse restrictions are exactly the finite minimizers for the
proved iterated trace resistances. Normalized Perron convergence therefore
gives convergence of these actual harmonic restrictions. -/

namespace EIGS

open IGS.Sec31 Filter Topology

variable {K : ℕ}

noncomputable def xiUnitBoundaryProfile (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarseLevel offset : ℕ) (boundary : Finset (XiVtx system coarseLevel))
    (boundaryNonempty : boundary.Nonempty) (boundaryValues : XiVtx system coarseLevel → ℝ) :
    XiVtx system (coarseLevel + offset) → ℝ :=
  Classical.choose (exists_xiUnit_iterated_trace system rulesConnected coarseLevel offset
    ((XiNetwork system coarseLevel).boundaryPotentialProfile
      ((system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1))
      (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1) (fun _ => by norm_num) offset)
      (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty boundaryValues))

theorem xiUnitBoundaryProfile_restriction (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarseLevel offset : ℕ) (boundary : Finset (XiVtx system coarseLevel))
    (boundaryNonempty : boundary.Nonempty) (boundaryValues : XiVtx system coarseLevel → ℝ)
    (vertex : XiVtx system coarseLevel) :
    xiUnitBoundaryProfile system rulesConnected coarseLevel offset boundary boundaryNonempty boundaryValues
        (xiForward system coarseLevel offset vertex) =
      (XiNetwork system coarseLevel).boundaryPotentialProfile
        ((system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1))
        (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1) (fun _ => by norm_num) offset)
        (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty boundaryValues vertex :=
  (Classical.choose_spec (exists_xiUnit_iterated_trace system rulesConnected coarseLevel offset
    ((XiNetwork system coarseLevel).boundaryPotentialProfile
      ((system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1))
      (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1) (fun _ => by norm_num) offset)
      (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty boundaryValues))).1 vertex

theorem xiUnitBoundaryProfile_boundary (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarseLevel offset : ℕ) (boundary : Finset (XiVtx system coarseLevel))
    (boundaryNonempty : boundary.Nonempty) (boundaryValues : XiVtx system coarseLevel → ℝ)
    (vertex : XiVtx system coarseLevel) (membership : vertex ∈ boundary) :
    xiUnitBoundaryProfile system rulesConnected coarseLevel offset boundary boundaryNonempty boundaryValues
        (xiForward system coarseLevel offset vertex) = boundaryValues vertex := by
  rw [xiUnitBoundaryProfile_restriction]
  exact (XiNetwork system coarseLevel).boundaryPotentialProfile_boundary _ _
    (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty boundaryValues vertex membership

theorem xiUnitBoundaryProfile_energy (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarseLevel offset : ℕ) (boundary : Finset (XiVtx system coarseLevel))
    (boundaryNonempty : boundary.Nonempty) (boundaryValues : XiVtx system coarseLevel → ℝ) :
    ((XiNetwork system (coarseLevel + offset)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy
        (xiUnitBoundaryProfile system rulesConnected coarseLevel offset boundary boundaryNonempty boundaryValues) =
      ((XiNetwork system coarseLevel).potentialNetwork ((system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1))
        (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1) (fun _ => by norm_num) offset)).energy
        ((XiNetwork system coarseLevel).boundaryPotentialProfile
          ((system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1))
          (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1) (fun _ => by norm_num) offset)
          (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty boundaryValues) :=
  (Classical.choose_spec (exists_xiUnit_iterated_trace system rulesConnected coarseLevel offset
    ((XiNetwork system coarseLevel).boundaryPotentialProfile
      ((system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1))
      (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1) (fun _ => by norm_num) offset)
      (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty boundaryValues))).2.1

theorem xiUnitBoundaryProfile_minimal (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarseLevel offset : ℕ) (boundary : Finset (XiVtx system coarseLevel))
    (boundaryNonempty : boundary.Nonempty) (boundaryValues : XiVtx system coarseLevel → ℝ)
    (competitor : XiVtx system (coarseLevel + offset) → ℝ)
    (competitorBoundary : ∀ vertex ∈ boundary,
      competitor (xiForward system coarseLevel offset vertex) = boundaryValues vertex) :
    ((XiNetwork system (coarseLevel + offset)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy
        (xiUnitBoundaryProfile system rulesConnected coarseLevel offset boundary boundaryNonempty boundaryValues) ≤
      ((XiNetwork system (coarseLevel + offset)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy competitor := by
  rw [xiUnitBoundaryProfile_energy]
  exact ((XiNetwork system coarseLevel).boundaryPotentialProfile_minimal _ _
    (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty boundaryValues
    (fun vertex => competitor (xiForward system coarseLevel offset vertex)) competitorBoundary).trans
      (xiPotential_iterated_restriction_le system rulesConnected coarseLevel offset (fun _ => 1)
        (fun _ => by norm_num) competitor)

noncomputable def xiNormalizedTraceResistances (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate normalization : ℝ) (offset : ℕ) : Fin K → ℝ :=
  fun colour => (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour /
    (normalization * resistanceRate ^ offset)

theorem xiNormalizedTraceResistances_positive (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate normalization : ℝ) (ratePositive : 0 < resistanceRate)
    (normalizationPositive : 0 < normalization) (offset : ℕ) :
    ∀ colour, 0 < xiNormalizedTraceResistances system rulesConnected resistanceRate normalization offset colour := by
  intro colour
  exact div_pos (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1)
    (fun _ => by norm_num) offset colour) (mul_pos normalizationPositive (pow_pos ratePositive offset))

theorem xiNormalizedTraceResistances_tendsto (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate normalization : ℝ) (normalizationPositive : 0 < normalization)
    (resistanceVector : Fin K → ℝ)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (𝓝 (normalization • resistanceVector))) (colour : Fin K) :
    Tendsto (fun offset => xiNormalizedTraceResistances system rulesConnected resistanceRate normalization offset colour)
      atTop (𝓝 (resistanceVector colour)) := by
  have coordinateConvergence := ((tendsto_pi_nhds.1 normalizedConvergence) colour).div_const normalization
  have limitEquality : (normalization • resistanceVector) colour / normalization = resistanceVector colour := by
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [normalizationPositive.ne']
  rw [limitEquality] at coordinateConvergence
  apply coordinateConvergence.congr
  intro offset
  simp only [xiNormalizedTraceResistances, div_eq_mul_inv, mul_inv_rev]
  ring

theorem xiUnitBoundaryProfile_restriction_normalized (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate normalization : ℝ) (ratePositive : 0 < resistanceRate)
    (normalizationPositive : 0 < normalization)
    (coarseLevel offset : ℕ) (boundary : Finset (XiVtx system coarseLevel))
    (boundaryNonempty : boundary.Nonempty) (boundaryValues : XiVtx system coarseLevel → ℝ)
    (vertex : XiVtx system coarseLevel) :
    xiUnitBoundaryProfile system rulesConnected coarseLevel offset boundary boundaryNonempty boundaryValues
        (xiForward system coarseLevel offset vertex) =
      (XiNetwork system coarseLevel).boundaryPotentialProfile
        (xiNormalizedTraceResistances system rulesConnected resistanceRate normalization offset)
        (xiNormalizedTraceResistances_positive system rulesConnected resistanceRate normalization ratePositive normalizationPositive offset)
        (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty boundaryValues vertex := by
  rw [xiUnitBoundaryProfile_restriction]
  have resistanceEquality : (fun colour => (normalization * resistanceRate ^ offset) *
      xiNormalizedTraceResistances system rulesConnected resistanceRate normalization offset colour) =
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) := by
    funext colour
    dsimp [xiNormalizedTraceResistances]
    exact mul_div_cancel₀ _ (mul_pos normalizationPositive (pow_pos ratePositive offset)).ne'
  have profileEquality := (XiNetwork system coarseLevel).boundaryPotentialProfile_resistance_mul
    (xiNormalizedTraceResistances system rulesConnected resistanceRate normalization offset)
    (xiNormalizedTraceResistances_positive system rulesConnected resistanceRate normalization ratePositive normalizationPositive offset)
    (normalization * resistanceRate ^ offset) (mul_pos normalizationPositive (pow_pos ratePositive offset))
    (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty boundaryValues
  simpa only [resistanceEquality] using congrFun profileEquality vertex

theorem xiUnitBoundaryProfile_restriction_tendsto (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate normalization : ℝ) (ratePositive : 0 < resistanceRate)
    (normalizationPositive : 0 < normalization) (resistanceVector : Fin K → ℝ)
    (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (𝓝 (normalization • resistanceVector)))
    (coarseLevel : ℕ) (boundary : Finset (XiVtx system coarseLevel))
    (boundaryNonempty : boundary.Nonempty) (boundaryValues : XiVtx system coarseLevel → ℝ) :
    Tendsto (fun offset => ‖(fun vertex : XiVtx system coarseLevel =>
        xiUnitBoundaryProfile system rulesConnected coarseLevel offset boundary boundaryNonempty boundaryValues
          (xiForward system coarseLevel offset vertex)) -
      (fun vertex : XiVtx system coarseLevel =>
        (XiNetwork system coarseLevel).boundaryPotentialProfile resistanceVector vectorPositive
          (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty boundaryValues vertex)‖)
      atTop (𝓝 0) := by
  have profileConvergence := (XiNetwork system coarseLevel).boundaryPotentialProfile_norm_sub_tendsto_zero
    resistanceVector vectorPositive (xiNormalizedTraceResistances system rulesConnected resistanceRate normalization)
    (xiNormalizedTraceResistances_positive system rulesConnected resistanceRate normalization ratePositive normalizationPositive)
    (xiNormalizedTraceResistances_tendsto system rulesConnected resistanceRate normalization normalizationPositive
      resistanceVector normalizedConvergence)
    (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty boundaryValues
  apply profileConvergence.congr
  intro offset
  congr 1
  funext vertex
  simp only [Pi.sub_apply, xiUnitBoundaryProfile_restriction_normalized system rulesConnected resistanceRate normalization
    ratePositive normalizationPositive]

theorem exists_xiUnitBoundaryProfile_convergence (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ resistanceRate normalization : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ ratePositive : 0 < resistanceRate, ∃ normalizationPositive : 0 < normalization,
      ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector = resistanceRate • resistanceVector ∧
      ∀ (coarseLevel : ℕ) (boundary : Finset (XiVtx system coarseLevel))
        (boundaryNonempty : boundary.Nonempty) (boundaryValues : XiVtx system coarseLevel → ℝ),
        Tendsto (fun offset => ‖(fun vertex : XiVtx system coarseLevel =>
            xiUnitBoundaryProfile system rulesConnected coarseLevel offset boundary boundaryNonempty boundaryValues
              (xiForward system coarseLevel offset vertex)) -
          (fun vertex : XiVtx system coarseLevel =>
            (XiNetwork system coarseLevel).boundaryPotentialProfile resistanceVector vectorPositive
              (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty boundaryValues vertex)‖)
          atTop (𝓝 0) := by
  have coloursPositive : 0 < K := lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt
  obtain ⟨resistanceRate, normalization, resistanceVector, ratePositive, normalizationPositive,
      vectorPositive, normalized, eigenpair, normalizedConvergence⟩ :=
    (system.connectedRuleSystem rulesConnected).distance_positive_normalized_iterate_limit coloursPositive distancePositive
  exact ⟨resistanceRate, normalization, resistanceVector, ratePositive, normalizationPositive, vectorPositive,
    eigenpair, xiUnitBoundaryProfile_restriction_tendsto system rulesConnected resistanceRate normalization
      ratePositive normalizationPositive resistanceVector vectorPositive normalizedConvergence⟩

end EIGS
