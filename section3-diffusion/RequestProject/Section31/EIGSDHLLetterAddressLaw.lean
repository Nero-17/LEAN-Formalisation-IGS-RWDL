import RequestProject.Section31.EIGSDHLRetentionWordMass
import RequestProject.Section31.EIGSAddressMeasureUniqueness
import RequestProject.Section31.EIGSAnalyticTimeScale

/-! The iid child-letter product codes exactly the actual inverse-limit
address law of DHL(2,2). Edge coordinates themselves are not independent.
Finite word-edge bijections identify their marginals; compatibility and
the proved marginal-uniqueness theorem identify the entire address law. -/

namespace EIGS
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section

instance dhlActualEdgeNonempty (level : ℕ) : Nonempty (XiEdge (flowerSystem 2 2).toRuleData level) :=
  ⟨dhlEdgeOfWord level (fun _ => (0, 0))⟩

theorem dhlUniformWord_map_edge (level : ℕ) :
    ((PMF.uniformOfFintype (Fin level → Fin 2 × Fin 2)).toMeasure).map (dhlEdgeOfWord level) =
      (PMF.uniformOfFintype (XiEdge (flowerSystem 2 2).toRuleData level)).toMeasure := by
  apply Measure.ext_of_singleton
  intro edge
  rw [Measure.map_apply (Measurable.of_discrete : Measurable (dhlEdgeOfWord level))
    (measurableSet_singleton edge)]
  have fibre : (dhlEdgeOfWord level) ⁻¹' {edge} = {(dhlWordEdgeEquiv level).symm edge} := by
    ext word
    exact (dhlWordEdgeEquiv level).apply_eq_iff_eq_symm_apply
  rw [fibre]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [PMF.uniformOfFintype_apply]
  rw [Fintype.card_congr (dhlWordEdgeEquiv level)]

theorem dhlMass_edgeLaw_uniform (mass : XiMassParameters (flowerSystem 2 2)) (level : ℕ) :
    mass.edgeLaw level =
      (PMF.uniformOfFintype (XiEdge (flowerSystem 2 2).toRuleData level)).toMeasure := by
  have rate : mass.rate = 4 := by
    rw [XiMassParameters.rate_eq_spectralRadius, flowerSystem_massSpectralRadius]
    norm_num
  have edgeCard : Fintype.card (XiEdge (flowerSystem 2 2).toRuleData level) = 4 ^ level := by
    rw [← Fintype.card_congr (dhlWordEdgeEquiv level)]
    simp
  apply Measure.ext_of_singleton
  intro edge
  have weight : mass.edgeWeight level edge = 1 / (4 : ℝ) ^ level := by
    unfold XiMassParameters.edgeWeight
    rw [rate, show XiCol (flowerSystem 2 2).toRuleData level edge = (flowerSystem 2 2).initCol from
      Subsingleton.elim _ _]
    field_simp [(mass.amplitude_positive (flowerSystem 2 2).initCol).ne']
  unfold XiMassParameters.edgeLaw
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [XiMassParameters.edgePMF_apply,
    PMF.uniformOfFintype_apply, edgeCard, Nat.cast_pow, Nat.cast_ofNat]
  change ENNReal.ofReal (mass.edgeWeight level edge) = _
  rw [weight]
  simp

theorem dhlLetters_coordinate_law (mass : XiMassParameters (flowerSystem 2 2)) (level : ℕ) :
    ((Measure.infinitePi (fun _ : ℕ => dhlLetterLaw)).map dhlAddressOfLetters).map
      (xiAddressEdge (flowerSystem 2 2) level) = mass.edgeLaw level := by
  have prefixLaw : (Measure.infinitePi (fun _ : ℕ => dhlLetterLaw)).map
      (fun sample (position : Fin level) => sample position.val) =
        Measure.pi (fun _ : Fin level => dhlLetterLaw) := by
    have prefixEquality : independentWordBlock (Alphabet := Fin 2 × Fin 2) level 0 0 =
        (fun sample (position : Fin level) => sample position.val) := by
      funext sample position
      change sample (0 + 0 * level + position.val) = sample position.val
      simp only [zero_mul, zero_add]
    have blockLaw : (Measure.infinitePi (fun _ : ℕ => dhlLetterLaw)).map
        (independentWordBlock level 0 0) = Measure.pi (fun _ : Fin level => dhlLetterLaw) :=
      independent_word_block_law dhlLetterLaw 1 level 0 (0 : Fin 1)
    rw [prefixEquality] at blockLaw
    exact blockLaw
  rw [Measure.map_map (measurable_xiAddressEdge (flowerSystem 2 2) level)
    measurable_dhlAddressOfLetters]
  change (Measure.infinitePi (fun _ : ℕ => dhlLetterLaw)).map
    ((dhlEdgeOfWord level) ∘ (fun sample (position : Fin level) => sample position.val)) = _
  rw [← Measure.map_map (Measurable.of_discrete : Measurable (dhlEdgeOfWord level))
    (measurable_pi_iff.mpr (fun position : Fin level => measurable_pi_apply position.val)),
    prefixLaw, dhlUniformWordLaw, dhlUniformWord_map_edge, dhlMass_edgeLaw_uniform]

theorem dhlLetters_map_addressMeasure (mass : XiMassParameters (flowerSystem 2 2)) :
    (Measure.infinitePi (fun _ : ℕ => dhlLetterLaw)).map dhlAddressOfLetters = mass.addressMeasure := by
  apply xiAddressMeasure_eq_of_marginals
  intro level
  rw [dhlLetters_coordinate_law, mass.addressMeasure_coordinate]

end
end EIGS

#print axioms EIGS.dhlUniformWord_map_edge
#print axioms EIGS.dhlMass_edgeLaw_uniform
#print axioms EIGS.dhlLetters_coordinate_law
#print axioms EIGS.dhlLetters_map_addressMeasure
