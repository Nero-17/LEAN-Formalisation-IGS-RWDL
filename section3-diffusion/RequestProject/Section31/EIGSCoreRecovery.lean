import RequestProject.Section31.EIGSHarmonicCore

/-!
# Actual harmonic core recovery in the pointwise-and-energy topology

The finite-level harmonic extensions are constructed on the actual vertex
union, belong to the actual finite-energy domain, match the target at every
vertex eventually, and converge in energy. This is not asserted to be the
varying-space L² recovery theorem; that additional topology needs the completed
space and its measure.
-/

namespace EIGS

open IGS.Sec31 Filter Topology
open scoped ENNReal

variable {K : ℕ}

def xiHarmonicCoreAt (system : EIGSData K) (resistanceRate : ℝ)
    (resistanceRatePositive : 0 < resistanceRate) (resistanceVector : Fin K → ℝ)
    (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour) (level : ℕ) :
    Set (xiWeightedEnergyDomain system resistanceRate resistanceRatePositive
      resistanceVector resistanceVectorPositive) :=
  {values | xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector
    resistanceVectorPositive values = ENNReal.ofReal
      ((xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive level).energy (values.val ∘ xiVertexEmbedding system level))}

theorem exists_xiHarmonic_core_recovery (system : EIGSData K)
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
          (∀ vertex, Tendsto (fun level => (approximation level).val vertex) atTop (𝓝 (target.val vertex))) ∧
          Tendsto (fun level =>
            (xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector
              resistanceVectorPositive (approximation level)).toReal) atTop
            (𝓝 ((xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector
              resistanceVectorPositive target).toReal)) := by
  classical
  have coloursPositive : 0 < K := lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt
  obtain ⟨resistanceVector, resistanceRate, vectorPositive, ratePositive, normalized, eigenpair⟩ :=
    (system.connectedRuleSystem rulesConnected).distance_positive_eigenpair coloursPositive distancePositive
  have coordinateEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour =
        resistanceRate * resistanceVector colour := fun colour => congrFun eigenpair colour
  have energyIncreasing := xiUnionWeightedNetwork_energy_increasing_of_eigenpair system rulesConnected
    resistanceRate ratePositive resistanceVector vectorPositive coordinateEigenpair
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, ?_⟩
  intro target
  have approximationsExist : ∀ level,
      ∃ approximation : xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive,
        (∀ vertex : XiVtx system level,
          approximation.val (xiVertexEmbedding system level vertex) =
            target.val (xiVertexEmbedding system level vertex)) ∧
        xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive approximation =
          ENNReal.ofReal ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector
            vectorPositive level).energy (target.val ∘ xiVertexEmbedding system level)) := by
    intro level
    obtain ⟨extension, extensionRestriction, extensionEnergy⟩ :=
      exists_xiHarmonic_union_extension system rulesConnected resistanceRate ratePositive resistanceVector
        vectorPositive coordinateEigenpair level (target.val ∘ xiVertexEmbedding system level)
    have extensionInDomain : extension ∈ xiWeightedEnergyDomain system resistanceRate ratePositive
        resistanceVector vectorPositive := by
      apply (xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive extension).2
      rw [extensionEnergy]
      exact ENNReal.ofReal_ne_top
    refine ⟨⟨extension, extensionInDomain⟩, ?_, extensionEnergy⟩
    exact extensionRestriction 0
  choose approximation approximationBoundary approximationEnergy using approximationsExist
  refine ⟨approximation, ?_, ?_, ?_⟩
  · intro level
    change xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (approximation level) = ENNReal.ofReal
        ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy
          ((approximation level).val ∘ xiVertexEmbedding system level))
    have restrictionEquality : (approximation level).val ∘ xiVertexEmbedding system level =
        target.val ∘ xiVertexEmbedding system level := funext (approximationBoundary level)
    rw [restrictionEquality]
    exact approximationEnergy level
  · intro vertex
    obtain ⟨birthLevel, membership⟩ := xiVertexUnion_exhausted system vertex
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop birthLevel] with level afterBirth
    obtain ⟨finiteVertex, representation⟩ := xiLevelVertices_monotone system afterBirth membership
    simpa only [representation] using (approximationBoundary level finiteVertex).symm
  · have targetEnergyLimit := finite_energy_tendsto_traceEnergyValue
      (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive)
      energyIncreasing target
    convert targetEnergyLimit using 1
    ext level
    rw [approximationEnergy]
    exact ENNReal.toReal_ofReal
      ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy_nonneg
        (target.val ∘ xiVertexEmbedding system level))

end EIGS
