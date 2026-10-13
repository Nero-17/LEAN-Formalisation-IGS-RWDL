import RequestProject.Section31.EIGSCoreRecovery
import RequestProject.Section31.TraceEnergyPythagoras

/-! Actual harmonic approximation converges in residual energy. The exact
Pythagorean identity is derived from finite trace minimization on the unchanged
EIGS networks; harmonic approximation is not treated as an L² projection. -/

namespace EIGS

open IGS.Sec31 Filter Topology

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

include rulesConnected renormalizationEigenpair

theorem xiHarmonicCoreAt_energy_pythagoras (level : ℕ)
    (harmonic target : xiWeightedEnergyDomain system resistanceRate resistanceRatePositive
      resistanceVector resistanceVectorPositive)
    (harmonicCore : harmonic ∈ xiHarmonicCoreAt system resistanceRate resistanceRatePositive
      resistanceVector resistanceVectorPositive level)
    (sameBoundary : ∀ vertex : XiVtx system level,
      target.val (xiVertexEmbedding system level vertex) =
        harmonic.val (xiVertexEmbedding system level vertex)) :
    (xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive target).toReal =
      (xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive harmonic).toReal +
      (xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive (target - harmonic)).toReal := by
  refine traceEnergyValue_pythagoras_of_attained_trace
    (xiUnionWeightedNetwork system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive)
    (xiUnionWeightedNetwork_energy_increasing_of_eigenpair system rulesConnected resistanceRate
      resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair)
    (xiLevelVertices system level) level ?_ harmonic target ?_ ?_
  · intro edge
    exact ⟨⟨XiTail system level edge, rfl⟩, ⟨XiHead system level edge, rfl⟩⟩
  · change (xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive harmonic).toReal = _
    rw [harmonicCore]
    exact ENNReal.toReal_ofReal
      ((xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive level).energy_nonneg (harmonic.val ∘ xiVertexEmbedding system level))
  · intro vertex membership
    obtain ⟨finiteVertex, rfl⟩ := membership
    exact sameBoundary finiteVertex

theorem exists_xiHarmonic_energy_recovery_of_eigenpair
    (target : xiWeightedEnergyDomain system resistanceRate resistanceRatePositive
      resistanceVector resistanceVectorPositive) :
    ∃ approximation : ℕ → xiWeightedEnergyDomain system resistanceRate resistanceRatePositive
        resistanceVector resistanceVectorPositive,
      (∀ level, approximation level ∈ xiHarmonicCoreAt system resistanceRate resistanceRatePositive
        resistanceVector resistanceVectorPositive level) ∧
      (∀ level (vertex : XiVtx system level),
        (approximation level).val (xiVertexEmbedding system level vertex) =
          target.val (xiVertexEmbedding system level vertex)) ∧
      (∀ vertex, Tendsto (fun level => (approximation level).val vertex) atTop (𝓝 (target.val vertex))) ∧
      Tendsto (fun level =>
        (xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive (target - approximation level)).toReal) atTop (𝓝 0) := by
  classical
  have approximationsExist : ∀ level,
      ∃ approximation : xiWeightedEnergyDomain system resistanceRate resistanceRatePositive
          resistanceVector resistanceVectorPositive,
        (∀ vertex : XiVtx system level,
          approximation.val (xiVertexEmbedding system level vertex) =
            target.val (xiVertexEmbedding system level vertex)) ∧
        xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive approximation = ENNReal.ofReal
            ((xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
              resistanceVectorPositive level).energy (target.val ∘ xiVertexEmbedding system level)) := by
    intro level
    obtain ⟨extension, extensionValues, extensionEnergy⟩ := exists_xiHarmonic_union_extension system
      rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
        renormalizationEigenpair level (target.val ∘ xiVertexEmbedding system level)
    have extensionInDomain : extension ∈ xiWeightedEnergyDomain system resistanceRate resistanceRatePositive
        resistanceVector resistanceVectorPositive := by
      apply (xiWeightedEnergyDomain_iff system resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive extension).2
      rw [extensionEnergy]
      exact ENNReal.ofReal_ne_top
    exact ⟨⟨extension, extensionInDomain⟩, extensionValues 0, extensionEnergy⟩
  choose approximation approximationBoundary approximationEnergy using approximationsExist
  have approximationCore : ∀ level, approximation level ∈ xiHarmonicCoreAt system resistanceRate
      resistanceRatePositive resistanceVector resistanceVectorPositive level := by
    intro level
    change xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive (approximation level) = ENNReal.ofReal
        ((xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive level).energy ((approximation level).val ∘ xiVertexEmbedding system level))
    rw [show (approximation level).val ∘ xiVertexEmbedding system level =
      target.val ∘ xiVertexEmbedding system level from funext (approximationBoundary level)]
    exact approximationEnergy level
  refine ⟨approximation, approximationCore, approximationBoundary, ?_, ?_⟩
  · intro vertex
    obtain ⟨birthLevel, membership⟩ := xiVertexUnion_exhausted system vertex
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop birthLevel] with level afterBirth
    obtain ⟨finiteVertex, representation⟩ := xiLevelVertices_monotone system afterBirth membership
    simpa only [representation] using (approximationBoundary level finiteVertex).symm
  · have approximationEnergyLimit : Tendsto (fun level =>
        (xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive (approximation level)).toReal) atTop
        (𝓝 ((xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive target).toReal)) := by
      have targetEnergyLimit := finite_energy_tendsto_traceEnergyValue
        (xiUnionWeightedNetwork system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive)
        (xiUnionWeightedNetwork_energy_increasing_of_eigenpair system rulesConnected resistanceRate
          resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair) target
      convert targetEnergyLimit using 1
      ext level
      rw [approximationEnergy]
      exact ENNReal.toReal_ofReal
        ((xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive level).energy_nonneg (target.val ∘ xiVertexEmbedding system level))
    have targetConstant : Tendsto (fun _ : ℕ =>
        (xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive target).toReal) atTop
        (𝓝 ((xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive target).toReal)) := tendsto_const_nhds
    have residualLimit := targetConstant.sub approximationEnergyLimit
    rw [sub_self] at residualLimit
    apply residualLimit.congr
    intro level
    have pythagoras := xiHarmonicCoreAt_energy_pythagoras system rulesConnected resistanceRate
      resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair level
        (approximation level) target (approximationCore level)
        (fun vertex => (approximationBoundary level vertex).symm)
    linarith

end Eigenpair

theorem exists_xiHarmonic_energy_recovery (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ resistanceRatePositive : 0 < resistanceRate,
      ∃ resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∀ target : xiWeightedEnergyDomain system resistanceRate resistanceRatePositive
          resistanceVector resistanceVectorPositive,
        ∃ approximation : ℕ → xiWeightedEnergyDomain system resistanceRate resistanceRatePositive
            resistanceVector resistanceVectorPositive,
          (∀ level, approximation level ∈ xiHarmonicCoreAt system resistanceRate resistanceRatePositive
            resistanceVector resistanceVectorPositive level) ∧
          (∀ level (vertex : XiVtx system level),
            (approximation level).val (xiVertexEmbedding system level vertex) =
              target.val (xiVertexEmbedding system level vertex)) ∧
          (∀ vertex, Tendsto (fun level => (approximation level).val vertex) atTop (𝓝 (target.val vertex))) ∧
          Tendsto (fun level =>
            (xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector
              resistanceVectorPositive (target - approximation level)).toReal) atTop (𝓝 0) := by
  have coloursPositive : 0 < K := lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt
  obtain ⟨resistanceVector, resistanceRate, vectorPositive, ratePositive, normalized, eigenpair⟩ :=
    (system.connectedRuleSystem rulesConnected).distance_positive_eigenpair coloursPositive distancePositive
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, ?_⟩
  exact exists_xiHarmonic_energy_recovery_of_eigenpair system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive (fun colour => congrFun eigenpair colour)

end EIGS
