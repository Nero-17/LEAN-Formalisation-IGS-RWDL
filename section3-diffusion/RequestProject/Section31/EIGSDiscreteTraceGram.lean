import RequestProject.Section31.EIGSDiscreteTraceHarmonics

set_option maxHeartbeats 1200000

/-! Exact bilinear trace and convergence of the actual energy Gram matrices.
These are edge-energy scalar products; convergence of L² Gram matrices on the
completed space additionally uses the speed measures and uniform splines. -/

namespace EIGS

open IGS.Sec31 Filter Topology

variable {K : ℕ}

noncomputable def xiUnitTraceExtension (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarseLevel offset : ℕ) (values : XiVtx system coarseLevel → ℝ) :
    XiVtx system (coarseLevel + offset) → ℝ :=
  Classical.choose (exists_xiUnit_iterated_trace system rulesConnected coarseLevel offset values)

theorem xiUnitTraceExtension_boundary (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarseLevel offset : ℕ) (values : XiVtx system coarseLevel → ℝ) (vertex : XiVtx system coarseLevel) :
    xiUnitTraceExtension system rulesConnected coarseLevel offset values
      (xiForward system coarseLevel offset vertex) = values vertex :=
  (Classical.choose_spec (exists_xiUnit_iterated_trace system rulesConnected coarseLevel offset values)).1 vertex

theorem xiUnitTraceExtension_energy (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarseLevel offset : ℕ) (values : XiVtx system coarseLevel → ℝ) :
    ((XiNetwork system (coarseLevel + offset)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy
        (xiUnitTraceExtension system rulesConnected coarseLevel offset values) =
      ((XiNetwork system coarseLevel).potentialNetwork ((system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1))
        (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1) (fun _ => by norm_num) offset)).energy values :=
  (Classical.choose_spec (exists_xiUnit_iterated_trace system rulesConnected coarseLevel offset values)).2.1

theorem xiUnitTraceExtension_minimal (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarseLevel offset : ℕ) (values : XiVtx system coarseLevel → ℝ)
    (competitor : XiVtx system (coarseLevel + offset) → ℝ)
    (competitorBoundary : ∀ vertex, competitor (xiForward system coarseLevel offset vertex) = values vertex) :
    ((XiNetwork system (coarseLevel + offset)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy
        (xiUnitTraceExtension system rulesConnected coarseLevel offset values) ≤
      ((XiNetwork system (coarseLevel + offset)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy competitor := by
  rw [xiUnitTraceExtension_energy]
  exact (Classical.choose_spec (exists_xiUnit_iterated_trace system rulesConnected coarseLevel offset values)).2.2
    competitor competitorBoundary

theorem xiUnitTraceExtension_energyInner (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarseLevel offset : ℕ) (firstValues secondValues : XiVtx system coarseLevel → ℝ) :
    ((XiNetwork system (coarseLevel + offset)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energyInner
        (xiUnitTraceExtension system rulesConnected coarseLevel offset firstValues)
        (xiUnitTraceExtension system rulesConnected coarseLevel offset secondValues) =
      ((XiNetwork system coarseLevel).potentialNetwork ((system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1))
        (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1) (fun _ => by norm_num) offset)).energyInner
          firstValues secondValues := by
  let fineNetwork := (XiNetwork system (coarseLevel + offset)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)
  let first := xiUnitTraceExtension system rulesConnected coarseLevel offset firstValues
  let second := xiUnitTraceExtension system rulesConnected coarseLevel offset secondValues
  let boundary : Set (XiVtx system (coarseLevel + offset)) := Set.range (xiForward system coarseLevel offset)
  have firstMinimal : ∀ competitor : XiVtx system (coarseLevel + offset) → ℝ,
      (∀ vertex ∈ boundary, competitor vertex = first vertex) → fineNetwork.energy first ≤ fineNetwork.energy competitor := by
    intro competitor competitorBoundary
    apply xiUnitTraceExtension_minimal system rulesConnected coarseLevel offset firstValues competitor
    intro vertex
    exact (competitorBoundary _ ⟨vertex, rfl⟩).trans
      (xiUnitTraceExtension_boundary system rulesConnected coarseLevel offset firstValues vertex)
  have secondMinimal : ∀ competitor : XiVtx system (coarseLevel + offset) → ℝ,
      (∀ vertex ∈ boundary, competitor vertex = second vertex) → fineNetwork.energy second ≤ fineNetwork.energy competitor := by
    intro competitor competitorBoundary
    apply xiUnitTraceExtension_minimal system rulesConnected coarseLevel offset secondValues competitor
    intro vertex
    exact (competitorBoundary _ ⟨vertex, rfl⟩).trans
      (xiUnitTraceExtension_boundary system rulesConnected coarseLevel offset secondValues vertex)
  have sumMinimal : ∀ competitor : XiVtx system (coarseLevel + offset) → ℝ,
      (∀ vertex ∈ boundary, competitor vertex = (first + second) vertex) →
        fineNetwork.energy (first + second) ≤ fineNetwork.energy competitor := by
    apply fineNetwork.minimum_of_energyInner_vanishes boundary (first + second) (first + second) (fun _ _ => rfl)
    intro perturbation perturbationBoundary
    have firstOrthogonality := fineNetwork.energyInner_eq_zero_of_min boundary first first (fun _ _ => rfl)
      firstMinimal perturbation perturbationBoundary
    have secondOrthogonality := fineNetwork.energyInner_eq_zero_of_min boundary second second (fun _ _ => rfl)
      secondMinimal perturbation perturbationBoundary
    simpa only [one_mul, firstOrthogonality, secondOrthogonality, add_zero] using
      fineNetwork.energyInner_linear_first first second perturbation 1 1
  have sumEnergy : fineNetwork.energy (first + second) =
      ((XiNetwork system coarseLevel).potentialNetwork ((system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1))
        (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1) (fun _ => by norm_num) offset)).energy
          (firstValues + secondValues) := by
    apply le_antisymm
    · have sumComparison := sumMinimal (xiUnitTraceExtension system rulesConnected coarseLevel offset (firstValues + secondValues))
        (by
          rintro _ ⟨vertex, rfl⟩
          simp only [Pi.add_apply, first, second, xiUnitTraceExtension_boundary])
      exact sumComparison.trans_eq (xiUnitTraceExtension_energy system rulesConnected coarseLevel offset _)
    · simpa only [Pi.add_apply, first, second, xiUnitTraceExtension_boundary] using
        xiPotential_iterated_restriction_le system rulesConnected coarseLevel offset (fun _ => 1)
          (fun _ => by norm_num) (first + second)
  have fineExpansion := fineNetwork.energy_line first second 1
  have coarseExpansion := ((XiNetwork system coarseLevel).potentialNetwork
    ((system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1))
    (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1) (fun _ => by norm_num) offset)).energy_line
      firstValues secondValues 1
  simp only [one_mul, one_pow] at fineExpansion coarseExpansion
  have firstEnergy := xiUnitTraceExtension_energy system rulesConnected coarseLevel offset firstValues
  have secondEnergy := xiUnitTraceExtension_energy system rulesConnected coarseLevel offset secondValues
  change fineNetwork.energy first = _ at firstEnergy
  change fineNetwork.energy second = _ at secondEnergy
  change fineNetwork.energy (first + second) = _ at fineExpansion
  change ((XiNetwork system coarseLevel).potentialNetwork
    ((system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1))
    (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1) (fun _ => by norm_num) offset)).energy
      (firstValues + secondValues) = _ at coarseExpansion
  rw [sumEnergy, firstEnergy, secondEnergy] at fineExpansion
  change fineNetwork.energyInner first second = _
  linarith

theorem xiScaledUnitTraceInner_tendsto_of_pointwise (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate normalization : ℝ) (ratePositive : 0 < resistanceRate)
    (normalizationPositive : 0 < normalization) (resistanceVector : Fin K → ℝ)
    (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (𝓝 (normalization • resistanceVector)))
    (coarseLevel : ℕ) (firstSequence secondSequence : ℕ → XiVtx system coarseLevel → ℝ)
    (firstValues secondValues : XiVtx system coarseLevel → ℝ)
    (firstConvergence : ∀ vertex, Tendsto (fun offset => firstSequence offset vertex) atTop (𝓝 (firstValues vertex)))
    (secondConvergence : ∀ vertex, Tendsto (fun offset => secondSequence offset vertex) atTop (𝓝 (secondValues vertex))) :
    Tendsto (fun offset => normalization * resistanceRate ^ (coarseLevel + offset) *
      ((XiNetwork system (coarseLevel + offset)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energyInner
        (xiUnitTraceExtension system rulesConnected coarseLevel offset (firstSequence offset))
        (xiUnitTraceExtension system rulesConnected coarseLevel offset (secondSequence offset))) atTop
      (𝓝 ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive coarseLevel).energyInner
        firstValues secondValues)) := by
  have sumConvergence := tendsto_finset_sum Finset.univ (fun edge _ =>
    ((xiTraced_conductance_tendsto_of_normalized_iterate system rulesConnected resistanceRate normalization ratePositive
      normalizationPositive resistanceVector vectorPositive normalizedConvergence coarseLevel
        (XiCol system.toRuleData coarseLevel edge)).mul
      ((firstConvergence (XiTail system coarseLevel edge)).sub (firstConvergence (XiHead system coarseLevel edge)))).mul
      ((secondConvergence (XiTail system coarseLevel edge)).sub (secondConvergence (XiHead system coarseLevel edge))))
  have traceEquality : (fun offset => normalization * resistanceRate ^ (coarseLevel + offset) *
      ((XiNetwork system (coarseLevel + offset)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energyInner
        (xiUnitTraceExtension system rulesConnected coarseLevel offset (firstSequence offset))
        (xiUnitTraceExtension system rulesConnected coarseLevel offset (secondSequence offset))) =
      (fun offset => normalization * resistanceRate ^ (coarseLevel + offset) *
        ((XiNetwork system coarseLevel).potentialNetwork ((system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1))
          (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1) (fun _ => by norm_num) offset)).energyInner
          (firstSequence offset) (secondSequence offset)) := by
    funext offset
    rw [xiUnitTraceExtension_energyInner system rulesConnected coarseLevel offset]
  rw [traceEquality]
  simpa only [FiniteNetwork.energyInner, Network.potentialNetwork,
    xiWeightedFiniteNetwork, XiNetwork, XiEnds, Finset.mul_sum, mul_assoc] using sumConvergence

theorem xiUnitBoundaryProfile_energyInner_tendsto (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate normalization : ℝ) (ratePositive : 0 < resistanceRate)
    (normalizationPositive : 0 < normalization) (resistanceVector : Fin K → ℝ)
    (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (𝓝 (normalization • resistanceVector)))
    (coarseLevel : ℕ) (boundary : Finset (XiVtx system coarseLevel))
    (boundaryNonempty : boundary.Nonempty) (firstValues secondValues : XiVtx system coarseLevel → ℝ) :
    Tendsto (fun offset => normalization * resistanceRate ^ (coarseLevel + offset) *
      ((XiNetwork system (coarseLevel + offset)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energyInner
        (xiUnitBoundaryProfile system rulesConnected coarseLevel offset boundary boundaryNonempty firstValues)
        (xiUnitBoundaryProfile system rulesConnected coarseLevel offset boundary boundaryNonempty secondValues)) atTop
      (𝓝 ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive coarseLevel).energyInner
        ((XiNetwork system coarseLevel).boundaryPotentialProfile resistanceVector vectorPositive
          (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty firstValues)
        ((XiNetwork system coarseLevel).boundaryPotentialProfile resistanceVector vectorPositive
          (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty secondValues))) := by
  have coordinateConvergence (values : XiVtx system coarseLevel → ℝ) (vertex : XiVtx system coarseLevel) :
      Tendsto (fun offset => (XiNetwork system coarseLevel).boundaryPotentialProfile
        ((system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1))
        (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1) (fun _ => by norm_num) offset)
        (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty values vertex) atTop
      (𝓝 ((XiNetwork system coarseLevel).boundaryPotentialProfile resistanceVector vectorPositive
        (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty values vertex)) := by
    have restrictionConvergence := tendsto_iff_norm_sub_tendsto_zero.2
      (xiUnitBoundaryProfile_restriction_tendsto system rulesConnected resistanceRate normalization ratePositive
        normalizationPositive resistanceVector vectorPositive normalizedConvergence coarseLevel boundary boundaryNonempty values)
    simpa only [xiUnitBoundaryProfile_restriction] using (tendsto_pi_nhds.1 restrictionConvergence) vertex
  simpa only [xiUnitBoundaryProfile, xiUnitTraceExtension] using
    xiScaledUnitTraceInner_tendsto_of_pointwise system rulesConnected resistanceRate normalization ratePositive
      normalizationPositive resistanceVector vectorPositive normalizedConvergence coarseLevel
      (fun offset => (XiNetwork system coarseLevel).boundaryPotentialProfile
        ((system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1))
        (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1) (fun _ => by norm_num) offset)
        (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty firstValues)
      (fun offset => (XiNetwork system coarseLevel).boundaryPotentialProfile
        ((system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1))
        (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1) (fun _ => by norm_num) offset)
        (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty secondValues)
      ((XiNetwork system coarseLevel).boundaryPotentialProfile resistanceVector vectorPositive
        (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty firstValues)
      ((XiNetwork system coarseLevel).boundaryPotentialProfile resistanceVector vectorPositive
        (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty secondValues)
      (coordinateConvergence firstValues) (coordinateConvergence secondValues)

theorem exists_xiUnitBoundaryProfile_energyGram_convergence (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ resistanceRate normalization : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ ratePositive : 0 < resistanceRate, ∃ normalizationPositive : 0 < normalization,
      ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector = resistanceRate • resistanceVector ∧
      ∀ (coarseLevel : ℕ) (boundary : Finset (XiVtx system coarseLevel))
        (boundaryNonempty : boundary.Nonempty) (firstValues secondValues : XiVtx system coarseLevel → ℝ),
        Tendsto (fun offset => normalization * resistanceRate ^ (coarseLevel + offset) *
          ((XiNetwork system (coarseLevel + offset)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energyInner
            (xiUnitBoundaryProfile system rulesConnected coarseLevel offset boundary boundaryNonempty firstValues)
            (xiUnitBoundaryProfile system rulesConnected coarseLevel offset boundary boundaryNonempty secondValues)) atTop
          (𝓝 ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive coarseLevel).energyInner
            ((XiNetwork system coarseLevel).boundaryPotentialProfile resistanceVector vectorPositive
              (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty firstValues)
            ((XiNetwork system coarseLevel).boundaryPotentialProfile resistanceVector vectorPositive
              (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty secondValues))) := by
  have coloursPositive : 0 < K := lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt
  obtain ⟨resistanceRate, normalization, resistanceVector, ratePositive, normalizationPositive,
      vectorPositive, normalized, eigenpair, normalizedConvergence⟩ :=
    (system.connectedRuleSystem rulesConnected).distance_positive_normalized_iterate_limit coloursPositive distancePositive
  exact ⟨resistanceRate, normalization, resistanceVector, ratePositive, normalizationPositive, vectorPositive,
    eigenpair, xiUnitBoundaryProfile_energyInner_tendsto system rulesConnected resistanceRate normalization
      ratePositive normalizationPositive resistanceVector vectorPositive normalizedConvergence⟩

theorem xiUnitBoundaryProfile_scaled_energy_tendsto (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate normalization : ℝ) (ratePositive : 0 < resistanceRate)
    (normalizationPositive : 0 < normalization) (resistanceVector : Fin K → ℝ)
    (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (𝓝 (normalization • resistanceVector)))
    (coarseLevel : ℕ) (boundary : Finset (XiVtx system coarseLevel))
    (boundaryNonempty : boundary.Nonempty) (boundaryValues : XiVtx system coarseLevel → ℝ) :
    Tendsto (fun offset => xiScaledUnitEnergy system resistanceRate normalization (coarseLevel + offset)
      (xiUnitBoundaryProfile system rulesConnected coarseLevel offset boundary boundaryNonempty boundaryValues)) atTop
      (𝓝 ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive coarseLevel).energy
        ((XiNetwork system coarseLevel).boundaryPotentialProfile resistanceVector vectorPositive
          (xiSimpleGraph_connected system rulesConnected coarseLevel) boundary boundaryNonempty boundaryValues))) := by
  simpa only [xiScaledUnitEnergy, FiniteNetwork.energyInner, FiniteNetwork.energy, pow_two, mul_assoc] using
    xiUnitBoundaryProfile_energyInner_tendsto system rulesConnected resistanceRate normalization ratePositive
      normalizationPositive resistanceVector vectorPositive normalizedConvergence coarseLevel boundary boundaryNonempty
      boundaryValues boundaryValues

end EIGS
