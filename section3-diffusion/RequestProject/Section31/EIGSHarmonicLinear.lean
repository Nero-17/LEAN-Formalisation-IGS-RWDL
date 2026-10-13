import RequestProject.Section31.EIGSHarmonicContraction

/-! The constructed actual harmonic extensions depend linearly and injectively
on the prescribed finite vertex values. This supplies actual harmonic
coordinates, before choosing a completed space or an L² measure. -/

namespace EIGS.Network

variable {K : ℕ} (network : Network K) (rules : RuleFamily K)

noncomputable def substAffineProfilesLinearMap (profiles : ∀ colour, (rules.R colour).V → ℝ) :
    (network.V → ℝ) →ₗ[ℝ] ((network.subst rules).V → ℝ) where
  toFun := network.substAffineProfiles rules profiles
  map_add' := by
    intro first second
    funext vertex
    cases vertex <;> simp only [substAffineProfiles, Pi.add_apply] <;> ring
  map_smul' := by
    intro scalar values
    funext vertex
    cases vertex <;> simp only [substAffineProfiles, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring

end EIGS.Network

namespace EIGS

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

theorem exists_xiHarmonicStep_linear (level : ℕ) :
    ∃ extensionMap : (XiVtx system level → ℝ) →ₗ[ℝ] (XiVtx system (level + 1) → ℝ),
      extensionMap.toFun = xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive
        resistanceVector resistanceVectorPositive renormalizationEigenpair level := by
  classical
  have profilesExist := fun colour =>
    (system.ruleNetwork colour).exists_minimum_potential_energy_eq_inverse_effRes resistanceVector
      resistanceVectorPositive (rulesConnected colour) (system.plantPlus colour) (system.plantMinus colour)
        (system.plant_ne colour)
  choose profiles profilesPlus profilesMinus profilesMinimal profilesEnergy using profilesExist
  refine ⟨(XiNetwork system level).substAffineProfilesLinearMap (system.ruleFamily rulesConnected) profiles, ?_⟩
  funext values
  exact (xiHarmonicStep_eq_affine_profiles system rulesConnected resistanceRate resistanceRatePositive
    resistanceVector resistanceVectorPositive renormalizationEigenpair profiles profilesPlus profilesMinus
      profilesMinimal level values).symm

noncomputable def xiHarmonicStepLinearMap (level : ℕ) :
    (XiVtx system level → ℝ) →ₗ[ℝ] (XiVtx system (level + 1) → ℝ) :=
  Classical.choose (exists_xiHarmonicStep_linear system rulesConnected resistanceRate resistanceRatePositive
    resistanceVector resistanceVectorPositive renormalizationEigenpair level)

theorem xiHarmonicStepLinearMap_apply (level : ℕ) (values : XiVtx system level → ℝ) :
    xiHarmonicStepLinearMap system rulesConnected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair level values =
      xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair level values :=
  congrFun (Classical.choose_spec (exists_xiHarmonicStep_linear system rulesConnected resistanceRate
    resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair level)) values

noncomputable def xiHarmonicValuesLinearMap (initialLevel : ℕ) :
    (offset : ℕ) → (XiVtx system initialLevel → ℝ) →ₗ[ℝ] (XiVtx system (initialLevel + offset) → ℝ)
  | 0 => LinearMap.id
  | offset + 1 =>
      (xiHarmonicStepLinearMap system rulesConnected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair (initialLevel + offset)).comp
          (xiHarmonicValuesLinearMap initialLevel offset)

theorem xiHarmonicValuesLinearMap_apply (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ) :
    ∀ offset, xiHarmonicValuesLinearMap system rulesConnected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair initialLevel offset initialValues =
      xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset := by
  intro offset
  induction offset with
  | zero => rfl
  | succ offset induction =>
      change xiHarmonicStepLinearMap system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair (initialLevel + offset)
            (xiHarmonicValuesLinearMap system rulesConnected resistanceRate resistanceRatePositive resistanceVector
              resistanceVectorPositive renormalizationEigenpair initialLevel offset initialValues) = _
      rw [induction, xiHarmonicStepLinearMap_apply]
      rfl

noncomputable def xiHarmonicUnionExtension (initialLevel : ℕ)
    (initialValues : XiVtx system initialLevel → ℝ) : XiVertexUnion system → ℝ :=
  Classical.choose (exists_xiHarmonic_union_extension system rulesConnected resistanceRate resistanceRatePositive
    resistanceVector resistanceVectorPositive renormalizationEigenpair initialLevel initialValues)

theorem xiHarmonicUnionExtension_values (initialLevel : ℕ)
    (initialValues : XiVtx system initialLevel → ℝ) (offset : ℕ)
    (vertex : XiVtx system (initialLevel + offset)) :
    xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair initialLevel initialValues
          (xiVertexEmbedding system (initialLevel + offset) vertex) =
      xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset vertex :=
  (Classical.choose_spec (exists_xiHarmonic_union_extension system rulesConnected resistanceRate resistanceRatePositive
    resistanceVector resistanceVectorPositive renormalizationEigenpair initialLevel initialValues)).1 offset vertex

theorem xiHarmonicUnionExtension_energy (initialLevel : ℕ)
    (initialValues : XiVtx system initialLevel → ℝ) :
    xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
        (xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair initialLevel initialValues) =
      ENNReal.ofReal ((xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive initialLevel).energy initialValues) :=
  (Classical.choose_spec (exists_xiHarmonic_union_extension system rulesConnected resistanceRate resistanceRatePositive
    resistanceVector resistanceVectorPositive renormalizationEigenpair initialLevel initialValues)).2

theorem xiVertexUnion_exhausted_after (initialLevel : ℕ) (vertex : XiVertexUnion system) :
    ∃ offset, ∃ finiteVertex : XiVtx system (initialLevel + offset),
      xiVertexEmbedding system (initialLevel + offset) finiteVertex = vertex := by
  obtain ⟨birthLevel, membership⟩ := xiVertexUnion_exhausted system vertex
  exact ⟨birthLevel, xiLevelVertices_monotone system (Nat.le_add_left _ _) membership⟩

noncomputable def xiHarmonicUnionLinearMap (initialLevel : ℕ) :
    (XiVtx system initialLevel → ℝ) →ₗ[ℝ] (XiVertexUnion system → ℝ) where
  toFun := xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector
    resistanceVectorPositive renormalizationEigenpair initialLevel
  map_add' := by
    intro first second
    funext vertex
    obtain ⟨offset, finiteVertex, rfl⟩ := xiVertexUnion_exhausted_after system initialLevel vertex
    simp only [Pi.add_apply, xiHarmonicUnionExtension_values,
      ← xiHarmonicValuesLinearMap_apply, map_add]
  map_smul' := by
    intro scalar values
    funext vertex
    obtain ⟨offset, finiteVertex, rfl⟩ := xiVertexUnion_exhausted_after system initialLevel vertex
    simp only [Pi.smul_apply, xiHarmonicUnionExtension_values,
      ← xiHarmonicValuesLinearMap_apply, map_smul, RingHom.id_apply]

theorem xiHarmonicUnionLinearMap_injective (initialLevel : ℕ) :
    Function.Injective (xiHarmonicUnionLinearMap system rulesConnected resistanceRate resistanceRatePositive
      resistanceVector resistanceVectorPositive renormalizationEigenpair initialLevel) := by
  intro first second equality
  funext vertex
  have boundaryEquality := congrFun equality (xiVertexEmbedding system initialLevel vertex)
  change xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive renormalizationEigenpair initialLevel first (xiVertexEmbedding system initialLevel vertex) =
    xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive renormalizationEigenpair initialLevel second (xiVertexEmbedding system initialLevel vertex)
    at boundaryEquality
  have firstBoundary := xiHarmonicUnionExtension_values system rulesConnected resistanceRate resistanceRatePositive
    resistanceVector resistanceVectorPositive renormalizationEigenpair initialLevel first 0 vertex
  have secondBoundary := xiHarmonicUnionExtension_values system rulesConnected resistanceRate resistanceRatePositive
    resistanceVector resistanceVectorPositive renormalizationEigenpair initialLevel second 0 vertex
  change _ = first vertex at firstBoundary
  change _ = second vertex at secondBoundary
  simp only [Nat.add_zero] at firstBoundary secondBoundary
  rw [firstBoundary, secondBoundary] at boundaryEquality
  exact boundaryEquality

end Eigenpair

end EIGS
