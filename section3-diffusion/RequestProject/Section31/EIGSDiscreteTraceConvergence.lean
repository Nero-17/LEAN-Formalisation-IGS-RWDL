import RequestProject.Section31.EIGSDiscreteTrace
import RequestProject.Section31.HarmonicProfileContinuity

/-! Actual renormalized unit-resistance traces converge on every fixed coarse
Xi graph. The normalization, rate and positive limiting vector are constructed
by the proved nonlinear Perron convergence theorem for the original rules. -/

namespace EIGS

open IGS.Sec31 Filter Topology

variable {K : ℕ}

noncomputable def xiScaledUnitEnergy (system : EIGSData K)
    (resistanceRate normalization : ℝ) (level : ℕ) (values : XiVtx system level → ℝ) : ℝ :=
  normalization * resistanceRate ^ level *
    ((XiNetwork system level).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy values

noncomputable def xiScaledUnitTraceEnergy (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate normalization : ℝ) (coarseLevel offset : ℕ)
    (values : XiVtx system coarseLevel → ℝ) : ℝ :=
  normalization * resistanceRate ^ (coarseLevel + offset) *
    ((XiNetwork system coarseLevel).potentialNetwork ((system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1))
      (ruleFamily_Psi_iterate_positive system rulesConnected (fun _ => 1) (fun _ => by norm_num) offset)).energy values

theorem exists_xiScaledUnit_iterated_trace (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate normalization : ℝ) (ratePositive : 0 < resistanceRate)
    (normalizationPositive : 0 < normalization)
    (coarseLevel offset : ℕ) (oldValues : XiVtx system coarseLevel → ℝ) :
    ∃ extension : XiVtx system (coarseLevel + offset) → ℝ,
      (∀ vertex, extension (xiForward system coarseLevel offset vertex) = oldValues vertex) ∧
      xiScaledUnitEnergy system resistanceRate normalization (coarseLevel + offset) extension =
        xiScaledUnitTraceEnergy system rulesConnected resistanceRate normalization coarseLevel offset oldValues ∧
      ∀ competitor : XiVtx system (coarseLevel + offset) → ℝ,
        (∀ vertex, competitor (xiForward system coarseLevel offset vertex) = oldValues vertex) →
        xiScaledUnitTraceEnergy system rulesConnected resistanceRate normalization coarseLevel offset oldValues ≤
          xiScaledUnitEnergy system resistanceRate normalization (coarseLevel + offset) competitor := by
  obtain ⟨extension, extensionBoundary, extensionEnergy, lowerBound⟩ :=
    exists_xiUnit_iterated_trace system rulesConnected coarseLevel offset oldValues
  refine ⟨extension, extensionBoundary, ?_, ?_⟩
  · exact congrArg (fun energy => normalization * resistanceRate ^ (coarseLevel + offset) * energy) extensionEnergy
  · intro competitor competitorBoundary
    exact mul_le_mul_of_nonneg_left (lowerBound competitor competitorBoundary)
      (mul_nonneg normalizationPositive.le (pow_pos ratePositive _).le)

theorem xiTraced_conductance_tendsto_of_normalized_iterate
    (system : EIGSData K) (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate normalization : ℝ) (ratePositive : 0 < resistanceRate)
    (normalizationPositive : 0 < normalization) (resistanceVector : Fin K → ℝ)
    (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (𝓝 (normalization • resistanceVector)))
    (coarseLevel : ℕ) (colour : Fin K) :
    Tendsto (fun offset => normalization * resistanceRate ^ (coarseLevel + offset) *
      ((system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour)⁻¹) atTop
      (𝓝 (resistanceRate ^ coarseLevel * (resistanceVector colour)⁻¹)) := by
  have coordinateConvergence := (tendsto_pi_nhds.1 normalizedConvergence) colour
  have inverseConvergence := coordinateConvergence.inv₀ (mul_pos normalizationPositive (vectorPositive colour)).ne'
  have scaledConvergence := inverseConvergence.const_mul (normalization * resistanceRate ^ coarseLevel)
  have limitEquality : (normalization * resistanceRate ^ coarseLevel) *
      ((normalization • resistanceVector) colour)⁻¹ =
      resistanceRate ^ coarseLevel * (resistanceVector colour)⁻¹ := by
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [normalizationPositive.ne', (vectorPositive colour).ne']
  rw [limitEquality] at scaledConvergence
  apply scaledConvergence.congr
  intro offset
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, pow_add]
  ring

theorem xiScaledUnitTraceEnergy_tendsto_of_normalized_iterate
    (system : EIGSData K) (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate normalization : ℝ) (ratePositive : 0 < resistanceRate)
    (normalizationPositive : 0 < normalization) (resistanceVector : Fin K → ℝ)
    (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (𝓝 (normalization • resistanceVector)))
    (coarseLevel : ℕ) (values : XiVtx system coarseLevel → ℝ) :
    Tendsto (fun offset => xiScaledUnitTraceEnergy system rulesConnected resistanceRate normalization
        coarseLevel offset values) atTop
      (𝓝 ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive
        coarseLevel).energy values)) := by
  have sumConvergence := tendsto_finset_sum Finset.univ (fun edge _ =>
    (xiTraced_conductance_tendsto_of_normalized_iterate system rulesConnected resistanceRate normalization
      ratePositive normalizationPositive resistanceVector vectorPositive normalizedConvergence coarseLevel
        (XiCol system.toRuleData coarseLevel edge)).mul_const
          ((values (XiTail system coarseLevel edge) - values (XiHead system coarseLevel edge)) ^ 2))
  simpa only [xiScaledUnitTraceEnergy, FiniteNetwork.energy, Network.potentialNetwork,
    xiWeightedFiniteNetwork, XiNetwork, Finset.mul_sum, mul_assoc] using sumConvergence

theorem exists_xiScaledUnitTraceEnergy_convergence (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ resistanceRate normalization : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ ratePositive : 0 < resistanceRate, ∃ normalizationPositive : 0 < normalization,
      ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector = resistanceRate • resistanceVector ∧
      (∀ coarseLevel (values : XiVtx system coarseLevel → ℝ),
        Tendsto (fun offset => xiScaledUnitTraceEnergy system rulesConnected resistanceRate normalization
            coarseLevel offset values) atTop
          (𝓝 ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive
            coarseLevel).energy values))) ∧
      ∀ coarseLevel offset (oldValues : XiVtx system coarseLevel → ℝ),
        ∃ extension : XiVtx system (coarseLevel + offset) → ℝ,
          (∀ vertex, extension (xiForward system coarseLevel offset vertex) = oldValues vertex) ∧
          xiScaledUnitEnergy system resistanceRate normalization (coarseLevel + offset) extension =
            xiScaledUnitTraceEnergy system rulesConnected resistanceRate normalization coarseLevel offset oldValues ∧
          ∀ competitor : XiVtx system (coarseLevel + offset) → ℝ,
            (∀ vertex, competitor (xiForward system coarseLevel offset vertex) = oldValues vertex) →
            xiScaledUnitTraceEnergy system rulesConnected resistanceRate normalization coarseLevel offset oldValues ≤
              xiScaledUnitEnergy system resistanceRate normalization (coarseLevel + offset) competitor := by
  have coloursPositive : 0 < K := lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt
  obtain ⟨resistanceRate, normalization, resistanceVector, ratePositive, normalizationPositive,
      vectorPositive, normalized, eigenpair, normalizedConvergence⟩ :=
    (system.connectedRuleSystem rulesConnected).distance_positive_normalized_iterate_limit coloursPositive distancePositive
  refine ⟨resistanceRate, normalization, resistanceVector, ratePositive, normalizationPositive, vectorPositive,
    eigenpair, ?_, ?_⟩
  · exact xiScaledUnitTraceEnergy_tendsto_of_normalized_iterate system rulesConnected resistanceRate normalization
      ratePositive normalizationPositive resistanceVector vectorPositive normalizedConvergence
  · exact exists_xiScaledUnit_iterated_trace system rulesConnected resistanceRate normalization ratePositive
      normalizationPositive

end EIGS
