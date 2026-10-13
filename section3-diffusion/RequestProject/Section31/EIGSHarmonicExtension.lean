import RequestProject.Section31.EIGSLimitEnergy
import RequestProject.Section31.NestedValueExtension

/-!
# Actual finite-energy harmonic extensions on the vertex union

Attained successor trace minima are iterated and glued on the increasing
canonical vertex images. Every prescribed finite-level function obtains a
function on the actual union with precisely the same extended energy.
-/

namespace EIGS

open IGS.Sec31
open scoped ENNReal

variable {K : ℕ}

theorem xiLevelVertices_monotone (system : EIGSData K) :
    Monotone (xiLevelVertices system) :=
  monotone_nat_of_le_succ (xiLevelVertices_succ_subset system)

noncomputable def xiRangeValues (system : EIGSData K) (level : ℕ)
    (values : XiVtx system level → ℝ) (vertex : xiLevelVertices system level) : ℝ :=
  values (Classical.choose vertex.property)

theorem xiRangeValues_eq (system : EIGSData K) (level : ℕ)
    (values : XiVtx system level → ℝ) (vertex : xiLevelVertices system level)
    (finiteVertex : XiVtx system level)
    (representsVertex : xiVertexEmbedding system level finiteVertex = vertex.val) :
    xiRangeValues system level values vertex = values finiteVertex := by
  apply congrArg values
  apply xiVertexEmbedding_injective system level
  exact (Classical.choose_spec vertex.property).trans representsVertex.symm

section Eigenpair

variable (system : EIGSData K)
  (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
  (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
  (resistanceVector : Fin K → ℝ)
  (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
  (renormalizationEigenpair : ∀ colour,
    (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)

noncomputable def xiHarmonicStep (level : ℕ) (oldValues : XiVtx system level → ℝ) :
    XiVtx system (level + 1) → ℝ :=
  Classical.choose (exists_xiWeighted_trace_of_eigenpair system rulesConnected resistanceRate
    resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair level oldValues)

theorem xiHarmonicStep_old (level : ℕ) (oldValues : XiVtx system level → ℝ)
    (vertex : XiVtx system level) :
    xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive
      resistanceVector resistanceVectorPositive renormalizationEigenpair level oldValues (Sum.inl vertex) =
        oldValues vertex :=
  (Classical.choose_spec (exists_xiWeighted_trace_of_eigenpair system rulesConnected resistanceRate
    resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair level oldValues)).1 vertex

theorem xiHarmonicStep_energy (level : ℕ) (oldValues : XiVtx system level → ℝ) :
    (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive (level + 1)).energy
        (xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive
          resistanceVector resistanceVectorPositive renormalizationEigenpair level oldValues) =
      (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive level).energy oldValues :=
  (Classical.choose_spec (exists_xiWeighted_trace_of_eigenpair system rulesConnected resistanceRate
    resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair level oldValues)).2.1

noncomputable def xiHarmonicValues (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ) :
    (offset : ℕ) → XiVtx system (initialLevel + offset) → ℝ
  | 0 => initialValues
  | offset + 1 => xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive
      resistanceVector resistanceVectorPositive renormalizationEigenpair (initialLevel + offset)
        (xiHarmonicValues initialLevel initialValues offset)

theorem xiHarmonicValues_old (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ)
    (offset : ℕ) (vertex : XiVtx system (initialLevel + offset)) :
    xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive renormalizationEigenpair initialLevel initialValues (offset + 1) (Sum.inl vertex) =
      xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset vertex :=
  xiHarmonicStep_old system rulesConnected resistanceRate resistanceRatePositive resistanceVector
    resistanceVectorPositive renormalizationEigenpair (initialLevel + offset) _ vertex

theorem xiHarmonicValues_energy (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ)
    (offset : ℕ) :
    (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive (initialLevel + offset)).energy
        (xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset) =
      (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive initialLevel).energy initialValues := by
  induction offset with
  | zero => rfl
  | succ offset induction =>
      exact (xiHarmonicStep_energy system rulesConnected resistanceRate resistanceRatePositive
        resistanceVector resistanceVectorPositive renormalizationEigenpair (initialLevel + offset) _).trans induction

theorem exists_xiHarmonic_union_extension (initialLevel : ℕ)
    (initialValues : XiVtx system initialLevel → ℝ) :
    ∃ extension : XiVertexUnion system → ℝ,
      (∀ offset (vertex : XiVtx system (initialLevel + offset)),
        extension (xiVertexEmbedding system (initialLevel + offset) vertex) =
          xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
            resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset vertex) ∧
      xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive extension = ENNReal.ofReal
          ((xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
            resistanceVectorPositive initialLevel).energy initialValues) := by
  have shiftedSetsIncreasing : Monotone (fun offset => xiLevelVertices system (initialLevel + offset)) := by
    intro first second comparison
    exact xiLevelVertices_monotone system (Nat.add_le_add_left comparison initialLevel)
  have shiftedSetsExhaustive : ∀ vertex, ∃ offset, vertex ∈ xiLevelVertices system (initialLevel + offset) := by
    intro vertex
    obtain ⟨level, membership⟩ := xiVertexUnion_exhausted system vertex
    refine ⟨level, xiLevelVertices_monotone system ?_ membership⟩
    omega
  have shiftedValuesCompatible : ∀ offset (vertex : xiLevelVertices system (initialLevel + offset)),
      xiRangeValues system (initialLevel + (offset + 1))
          (xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
            resistanceVectorPositive renormalizationEigenpair initialLevel initialValues (offset + 1))
          ⟨vertex.val, shiftedSetsIncreasing (Nat.le_succ offset) vertex.property⟩ =
        xiRangeValues system (initialLevel + offset)
          (xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
            resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset) vertex := by
    intro offset vertex
    obtain ⟨finiteVertex, representation⟩ := vertex.property
    have nextRepresentation :
        xiVertexEmbedding system (initialLevel + (offset + 1)) (Sum.inl finiteVertex) = vertex.val := by
      simpa only [Nat.add_succ, xiVertexEmbedding_old] using representation
    rw [xiRangeValues_eq system (initialLevel + (offset + 1)) _
        ⟨vertex.val, shiftedSetsIncreasing (Nat.le_succ offset) vertex.property⟩
        (Sum.inl finiteVertex) nextRepresentation,
      xiRangeValues_eq system (initialLevel + offset) _ _ finiteVertex representation]
    exact xiHarmonicValues_old system rulesConnected resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset finiteVertex
  obtain ⟨extension, extensionValues⟩ := exists_nested_value_extension
    (fun offset => xiLevelVertices system (initialLevel + offset)) shiftedSetsIncreasing shiftedSetsExhaustive
    (fun offset => xiRangeValues system (initialLevel + offset)
      (xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset)) shiftedValuesCompatible
  have extensionRestriction : ∀ offset (vertex : XiVtx system (initialLevel + offset)),
      extension (xiVertexEmbedding system (initialLevel + offset) vertex) =
        xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset vertex := by
    intro offset vertex
    exact (extensionValues offset ⟨xiVertexEmbedding system (initialLevel + offset) vertex, vertex, rfl⟩).trans
      (xiRangeValues_eq system (initialLevel + offset) _ _ vertex rfl)
  have fineEnergy : ∀ offset,
      (xiUnionWeightedNetwork system resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive (initialLevel + offset)).energy extension =
      (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive initialLevel).energy initialValues := by
    intro offset
    change (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive (initialLevel + offset)).energy
        (extension ∘ xiVertexEmbedding system (initialLevel + offset)) = _
    rw [show extension ∘ xiVertexEmbedding system (initialLevel + offset) =
      xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset from
          funext (extensionRestriction offset)]
    exact xiHarmonicValues_energy system rulesConnected resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset
  refine ⟨extension, extensionRestriction, le_antisymm ?_ ?_⟩
  · apply extendedTraceEnergy_le_of_bound
    intro level
    by_cases afterInitial : initialLevel ≤ level
    · obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le afterInitial
      exact (fineEnergy offset).le
    · have earlierBound := xiUnionWeightedNetwork_energy_increasing_of_eigenpair system rulesConnected
        resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
        renormalizationEigenpair extension (by omega : level ≤ initialLevel)
      exact earlierBound.trans_eq (fineEnergy 0)
  · have initialBound := le_iSup (fun level => ENNReal.ofReal
        ((xiUnionWeightedNetwork system resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive level).energy extension)) initialLevel
    have initialEnergy :
        (xiUnionWeightedNetwork system resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive initialLevel).energy extension =
        (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive initialLevel).energy initialValues := fineEnergy 0
    rw [initialEnergy] at initialBound
    exact initialBound

end Eigenpair

end EIGS
