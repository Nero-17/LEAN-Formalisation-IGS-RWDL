import RequestProject.Section31.EIGSHarmonicExtension
import RequestProject.Section31.EIGSRuleOscillation
import RequestProject.Section31.AffineProfileExtension

/-! The constructed actual successor harmonic step equals the explicit affine
rule profile extension, and hence contracts each child edge oscillation. -/

namespace EIGS

open IGS.Sec31

variable {K : ℕ}

section Eigenpair

variable (system : EIGSData K)
  (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
  (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
  (resistanceVector : Fin K → ℝ)
  (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
  (renormalizationEigenpair : ∀ colour,
    (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)

theorem xiHarmonicStep_potential_minimal (level : ℕ) (oldValues : XiVtx system level → ℝ)
    (competitor : XiVtx system (level + 1) → ℝ)
    (competitorOld : ∀ vertex, competitor (Sum.inl vertex) = oldValues vertex) :
    ((XiNetwork system (level + 1)).potentialNetwork resistanceVector resistanceVectorPositive).energy
        (xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair level oldValues) ≤
      ((XiNetwork system (level + 1)).potentialNetwork resistanceVector resistanceVectorPositive).energy competitor := by
  have comparison :=
    (Classical.choose_spec (exists_xiWeighted_trace_of_eigenpair system rulesConnected resistanceRate
      resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair level oldValues)).2.2
      competitor competitorOld
  rw [← (xiHarmonicStep_energy system rulesConnected resistanceRate resistanceRatePositive resistanceVector
    resistanceVectorPositive renormalizationEigenpair level oldValues)] at comparison
  rw [xiWeightedFiniteNetwork_energy_eq_potential, xiWeightedFiniteNetwork_energy_eq_potential] at comparison
  exact (mul_le_mul_iff_right₀ (pow_pos resistanceRatePositive (level + 1))).1 comparison

theorem xiHarmonicStep_eq_affine_profiles
    (profiles : ∀ colour, (system.rule colour).V → ℝ)
    (profilesPlus : ∀ colour, profiles colour (system.plantPlus colour) = 1)
    (profilesMinus : ∀ colour, profiles colour (system.plantMinus colour) = 0)
    (profilesMinimal : ∀ colour (competitor : (system.rule colour).V → ℝ),
      competitor (system.plantPlus colour) = 1 → competitor (system.plantMinus colour) = 0 →
      ((system.ruleNetwork colour).potentialNetwork resistanceVector resistanceVectorPositive).energy
          (profiles colour) ≤
        ((system.ruleNetwork colour).potentialNetwork resistanceVector resistanceVectorPositive).energy competitor)
    (level : ℕ) (oldValues : XiVtx system level → ℝ) :
    xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair level oldValues =
      (XiNetwork system level).substAffineProfiles (system.ruleFamily rulesConnected) profiles oldValues := by
  classical
  have fineConnected : (XiNetwork system (level + 1)).toSimpleGraph.Connected :=
    xiSimpleGraph_connected system rulesConnected (level + 1)
  apply (XiNetwork system (level + 1)).potential_minimum_unique resistanceVector resistanceVectorPositive
    fineConnected (Finset.univ.image Sum.inl)
    ⟨Sum.inl (xiPositiveTerminal system level), by simp⟩
    (fun vertex => match vertex with
      | Sum.inl oldVertex => oldValues oldVertex
      | Sum.inr _ => 0)
  · intro vertex membership
    obtain ⟨oldVertex, _, rfl⟩ := Finset.mem_image.1 membership
    exact xiHarmonicStep_old system rulesConnected resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive renormalizationEigenpair level oldValues oldVertex
  · intro vertex membership
    obtain ⟨oldVertex, _, rfl⟩ := Finset.mem_image.1 membership
    rfl
  · intro competitor competitorBoundary
    apply xiHarmonicStep_potential_minimal system rulesConnected resistanceRate resistanceRatePositive
      resistanceVector resistanceVectorPositive renormalizationEigenpair level oldValues competitor
    intro vertex
    exact competitorBoundary (Sum.inl vertex) (by simp)
  · intro competitor competitorBoundary
    have competitorOld : ∀ vertex, competitor (Sum.inl vertex) = oldValues vertex :=
      fun vertex => competitorBoundary (Sum.inl vertex) (by simp)
    simpa only [xiPotentialEnergy_succ_eq_substituted system rulesConnected] using
      (XiNetwork system level).substAffineProfiles_minimal (system.ruleFamily rulesConnected)
        resistanceVector resistanceVectorPositive profiles profilesPlus profilesMinus profilesMinimal oldValues
          competitor competitorOld

theorem xiHarmonicStep_child_edge_contraction
    (profiles : ∀ colour, (system.rule colour).V → ℝ)
    (profilesPlus : ∀ colour, profiles colour (system.plantPlus colour) = 1)
    (profilesMinus : ∀ colour, profiles colour (system.plantMinus colour) = 0)
    (profilesMinimal : ∀ colour (competitor : (system.rule colour).V → ℝ),
      competitor (system.plantPlus colour) = 1 → competitor (system.plantMinus colour) = 0 →
      ((system.ruleNetwork colour).potentialNetwork resistanceVector resistanceVectorPositive).energy
          (profiles colour) ≤
        ((system.ruleNetwork colour).potentialNetwork resistanceVector resistanceVectorPositive).energy competitor)
    (contractionFactor : ℝ)
    (profileEdgeBound : ∀ colour (edge : (system.rule colour).E),
      |profiles colour ((system.rule colour).tail edge) - profiles colour ((system.rule colour).head edge)| ≤
        contractionFactor)
    (level : ℕ) (oldValues : XiVtx system level → ℝ)
    (edge : XiEdge system.toRuleData (level + 1)) :
    |xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair level oldValues (XiTail system (level + 1) edge) -
      xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair level oldValues (XiHead system (level + 1) edge)| ≤
      |oldValues (XiTail system level edge.1) - oldValues (XiHead system level edge.1)| * contractionFactor := by
  rw [xiHarmonicStep_eq_affine_profiles system rulesConnected resistanceRate resistanceRatePositive
    resistanceVector resistanceVectorPositive renormalizationEigenpair profiles profilesPlus profilesMinus profilesMinimal]
  change |(XiNetwork system level).substAffineProfiles (system.ruleFamily rulesConnected) profiles oldValues
        (((XiNetwork system level).subst (system.ruleFamily rulesConnected)).tail edge) -
      (XiNetwork system level).substAffineProfiles (system.ruleFamily rulesConnected) profiles oldValues
        (((XiNetwork system level).subst (system.ruleFamily rulesConnected)).head edge)| ≤ _
  rw [(XiNetwork system level).substAffineProfiles_edge_difference (system.ruleFamily rulesConnected)
    profiles profilesPlus profilesMinus, abs_mul]
  exact mul_le_mul_of_nonneg_left (profileEdgeBound _ _) (abs_nonneg _)

end Eigenpair

/-- The original standing assumptions construct the actual weighted harmonic
steps and a common strictly contracting child-edge factor. -/
theorem exists_xiHarmonic_strict_contraction (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour)) :
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ resistanceRatePositive : 0 < resistanceRate,
      ∃ resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour =
          resistanceRate * resistanceVector colour,
      ∃ contractionFactor : ℝ, 0 < contractionFactor ∧ contractionFactor < 1 ∧
        ∀ level (oldValues : XiVtx system level → ℝ)
          (edge : XiEdge system.toRuleData (level + 1)),
          |xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive resistanceVector
              resistanceVectorPositive renormalizationEigenpair level oldValues (XiTail system (level + 1) edge) -
            xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive resistanceVector
              resistanceVectorPositive renormalizationEigenpair level oldValues (XiHead system (level + 1) edge)| ≤
            |oldValues (XiTail system level edge.1) - oldValues (XiHead system level edge.1)| * contractionFactor := by
  have coloursPositive : 0 < K := lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt
  obtain ⟨resistanceVector, resistanceRate, vectorPositive, ratePositive, normalized, eigenpair⟩ :=
    (system.connectedRuleSystem rulesConnected).distance_positive_eigenpair coloursPositive distancePositive
  have coordinateEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour =
        resistanceRate * resistanceVector colour := fun colour => congrFun eigenpair colour
  obtain ⟨profiles, contractionFactor, factorPositive, factorStrict, profilesPlus, profilesMinus,
      profilesMinimal, profileEdgeBound⟩ :=
    exists_rule_harmonic_profiles_strict_oscillation system rulesConnected distancePositive oneColourDistance
      resistanceVector vectorPositive
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, coordinateEigenpair,
    contractionFactor, factorPositive, factorStrict, ?_⟩
  exact xiHarmonicStep_child_edge_contraction system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive coordinateEigenpair profiles profilesPlus profilesMinus profilesMinimal
      contractionFactor profileEdgeBound

end EIGS
