import RequestProject.Section31.EIGSHarmonicExtension

/-!
# A constructed finite-level harmonic core in the actual energy domain

Original rule assumptions supply the weights. Every function on every finite
vertex level has an extension in the constructed domain with exactly its
finite weighted energy. This constructs finite-energy core candidates; density
in the completed measure space is a separate analytic obligation.
-/

namespace EIGS

open IGS.Sec31
open scoped ENNReal

variable {K : ℕ}

theorem exists_xiHarmonic_core_extensions (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ resistanceRatePositive : 0 < resistanceRate,
      ∃ resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∀ initialLevel (initialValues : XiVtx system initialLevel → ℝ),
        ∃ extension : xiWeightedEnergyDomain system resistanceRate resistanceRatePositive
            resistanceVector resistanceVectorPositive,
          (∀ vertex : XiVtx system initialLevel,
            extension.val (xiVertexEmbedding system initialLevel vertex) = initialValues vertex) ∧
          xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector
            resistanceVectorPositive extension = ENNReal.ofReal
              ((xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
                resistanceVectorPositive initialLevel).energy initialValues) := by
  have coloursPositive : 0 < K := lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt
  obtain ⟨resistanceVector, resistanceRate, vectorPositive, ratePositive, normalized, eigenpair⟩ :=
    (system.connectedRuleSystem rulesConnected).distance_positive_eigenpair coloursPositive distancePositive
  have coordinateEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour =
        resistanceRate * resistanceVector colour := fun colour => congrFun eigenpair colour
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, ?_⟩
  intro initialLevel initialValues
  obtain ⟨extension, extensionRestriction, extensionEnergy⟩ :=
    exists_xiHarmonic_union_extension system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive coordinateEigenpair initialLevel initialValues
  have extensionInDomain : extension ∈ xiWeightedEnergyDomain system resistanceRate ratePositive
      resistanceVector vectorPositive := by
    apply (xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive extension).2
    rw [extensionEnergy]
    exact ENNReal.ofReal_ne_top
  refine ⟨⟨extension, extensionInDomain⟩, ?_, extensionEnergy⟩
  intro vertex
  exact extensionRestriction 0 vertex

end EIGS
