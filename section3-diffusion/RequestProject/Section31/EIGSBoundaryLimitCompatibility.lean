import RequestProject.Section31.EIGSMovingTraceEnergy

/-! Limits of actual coarse boundary restrictions form one function on the
original vertex union. Their finite weighted energies are bounded by the
limiting bound on the original-unit native energies. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology

set_option maxHeartbeats 2400000

variable {K : ℕ}

theorem xiNativeBoundaryValues_compatible (system : EIGSData K) (mass : XiMassParameters system)
    (coarseLevel middleLevel fineLevel : ℕ) (coarseMiddle : coarseLevel ≤ middleLevel)
    (middleFine : middleLevel ≤ fineLevel) (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass fineLevel))
    (vertex : XiVtx system coarseLevel) :
    xiNativeBoundaryValues system mass middleLevel fineLevel values
      (xiVertexInclusion system coarseLevel middleLevel coarseMiddle vertex) =
    xiNativeBoundaryValues system mass coarseLevel fineLevel values vertex := by
  simp only [xiNativeBoundaryValues, dif_pos middleFine, dif_pos (coarseMiddle.trans middleFine)]
  rw [xiVertexInclusion_comp]

theorem xiNativeBoundaryLimits_compatible (system : EIGSData K) (mass : XiMassParameters system)
    (sequence : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
    (levels : ℕ → ℕ) (levelsTendsto : Tendsto levels atTop atTop)
    (boundaries : ∀ coarseLevel, XiVtx system coarseLevel → ℝ)
    (boundaryConvergence : ∀ coarseLevel, Tendsto
      (fun index => xiNativeBoundaryValues system mass coarseLevel (levels index) (sequence (levels index)))
      atTop (nhds (boundaries coarseLevel)))
    (coarseLevel middleLevel : ℕ) (coarseMiddle : coarseLevel ≤ middleLevel) (vertex : XiVtx system coarseLevel) :
    boundaries middleLevel (xiVertexInclusion system coarseLevel middleLevel coarseMiddle vertex) =
      boundaries coarseLevel vertex := by
  have middleConvergence := ((continuous_apply (xiVertexInclusion system coarseLevel middleLevel coarseMiddle vertex)).tendsto
    (boundaries middleLevel)).comp (boundaryConvergence middleLevel)
  have coarseConvergence := ((continuous_apply vertex).tendsto (boundaries coarseLevel)).comp (boundaryConvergence coarseLevel)
  apply tendsto_nhds_unique middleConvergence
  apply coarseConvergence.congr'
  filter_upwards [levelsTendsto.eventually (eventually_ge_atTop middleLevel)] with index middleFine
  exact (xiNativeBoundaryValues_compatible system mass coarseLevel middleLevel (levels index) coarseMiddle middleFine
    (sequence (levels index)) vertex).symm

theorem exists_xiUnionFunction_of_compatible_boundaries (system : EIGSData K)
    (boundaries : ∀ level, XiVtx system level → ℝ)
    (compatible : ∀ coarseLevel fineLevel (levelsOrdered : coarseLevel ≤ fineLevel) (vertex : XiVtx system coarseLevel),
      boundaries fineLevel (xiVertexInclusion system coarseLevel fineLevel levelsOrdered vertex) = boundaries coarseLevel vertex) :
    ∃ values : XiVertexUnion system → ℝ, ∀ level vertex,
      values (xiVertexEmbedding system level vertex) = boundaries level vertex := by
  classical
  choose levels representatives representations using xiVertexUnion_exhausted system
  refine ⟨fun vertex => boundaries (levels vertex) (representatives vertex), ?_⟩
  intro level vertex
  by_cases afterBirth : levels (xiVertexEmbedding system level vertex) ≤ level
  · have includedEquality : xiVertexInclusion system (levels (xiVertexEmbedding system level vertex)) level afterBirth
        (representatives (xiVertexEmbedding system level vertex)) = vertex := by
      apply xiVertexEmbedding_injective system level
      rw [xiVertexEmbedding_inclusion, representations]
    have agreement := compatible (levels (xiVertexEmbedding system level vertex)) level afterBirth
      (representatives (xiVertexEmbedding system level vertex))
    rw [includedEquality] at agreement
    exact agreement.symm
  · have beforeBirth := Nat.le_of_lt (Nat.lt_of_not_ge afterBirth)
    have includedEquality : xiVertexInclusion system level (levels (xiVertexEmbedding system level vertex)) beforeBirth vertex =
        representatives (xiVertexEmbedding system level vertex) := by
      apply xiVertexEmbedding_injective system (levels (xiVertexEmbedding system level vertex))
      rw [xiVertexEmbedding_inclusion, representations]
    have agreement := compatible level (levels (xiVertexEmbedding system level vertex)) beforeBirth vertex
    rw [includedEquality] at agreement
    exact agreement

theorem xiNativeBoundaryLimit_energy_le (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (mass : XiMassParameters system)
    (resistanceRate normalization : ℝ) (ratePositive : 0 < resistanceRate)
    (normalizationPositive : 0 < normalization) (resistanceVector : Fin K → ℝ)
    (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector)))
    (sequence : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
    (levels : ℕ → ℕ) (levelsTendsto : Tendsto levels atTop atTop)
    (coarseLevel : ℕ) (boundaryLimit : XiVtx system coarseLevel → ℝ)
    (boundaryConvergence : Tendsto
      (fun index => xiNativeBoundaryValues system mass coarseLevel (levels index) (sequence (levels index)))
      atTop (nhds boundaryLimit))
    (energyBound : ℝ) (energiesBounded : ∀ᶠ index in atTop,
      xiNativeScaledUnitEnergy system mass resistanceRate normalization (levels index) (sequence (levels index)) ≤ energyBound) :
    (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive coarseLevel).energy boundaryLimit ≤ energyBound := by
  apply le_of_tendsto (xiUnitPotentialScaledEnergy_moving_tendsto system rulesConnected resistanceRate normalization
    ratePositive normalizationPositive resistanceVector vectorPositive normalizedConvergence coarseLevel levels levelsTendsto
    (fun index => xiNativeBoundaryValues system mass coarseLevel (levels index) (sequence (levels index))) boundaryLimit boundaryConvergence)
  filter_upwards [energiesBounded] with index energyBoundAtIndex
  exact (xiNativeBoundaryValues_unit_energy_le system rulesConnected mass resistanceRate normalization ratePositive
    normalizationPositive coarseLevel (levels index) (sequence (levels index))).trans energyBoundAtIndex

theorem xiUnionFunction_finiteEnergy_of_boundary_bound (system : EIGSData K)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (boundaries : ∀ level, XiVtx system level → ℝ) (values : XiVertexUnion system → ℝ)
    (agreement : ∀ level vertex, values (xiVertexEmbedding system level vertex) = boundaries level vertex)
    (energyBound : ℝ) (energiesBounded : ∀ level,
      (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy (boundaries level) ≤ energyBound) :
    values ∈ xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive ∧
      xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive values ≤ ENNReal.ofReal energyBound := by
  have bound : ∀ level, (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy values ≤ energyBound := by
    intro level
    change (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy
      (values ∘ xiVertexEmbedding system level) ≤ energyBound
    rw [show values ∘ xiVertexEmbedding system level = boundaries level from funext (agreement level)]
    exact energiesBounded level
  exact ⟨⟨energyBound, bound⟩, extendedTraceEnergy_le_of_bound _ values energyBound bound⟩

end EIGS

#print axioms EIGS.xiNativeBoundaryValues_compatible
#print axioms EIGS.xiNativeBoundaryLimits_compatible
#print axioms EIGS.exists_xiUnionFunction_of_compatible_boundaries
#print axioms EIGS.xiNativeBoundaryLimit_energy_le
#print axioms EIGS.xiUnionFunction_finiteEnergy_of_boundary_bound
