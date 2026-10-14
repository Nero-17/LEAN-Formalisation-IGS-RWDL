import RequestProject.Section31.FiniteBallCoverMassBounds

/-! Quantitative bounds for the standard Mathlib covering number on a
compact space. Compactness supplies finite covers; the mass comparisons
then apply to a minimal cover and a maximal separated set. -/

namespace IGS.Sec31
open MeasureTheory Metric Set
open scoped Classical NNReal ENNReal
noncomputable section

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

theorem compact_coveringNumber_univ_ne_top (radius : ℝ≥0) (radiusPositive : 0 < radius) :
    Metric.coveringNumber radius (Set.univ : Set Space) ≠ ⊤ := by
  obtain ⟨centers, centersSubset, centersFinite, cover⟩ :=
    Metric.exists_finite_isCover_of_isCompact radiusPositive.ne' (isCompact_univ : IsCompact (Set.univ : Set Space))
  exact ne_of_lt ((cover.coveringNumber_le_encard centersSubset).trans_lt centersFinite.encard_lt_top)

theorem compact_externalCoveringNumber_univ_ne_top (radius : ℝ≥0) (radiusPositive : 0 < radius) :
    Metric.externalCoveringNumber radius (Set.univ : Set Space) ≠ ⊤ := by
  exact ne_of_lt ((Metric.externalCoveringNumber_le_coveringNumber radius Set.univ).trans_lt
    (lt_top_iff_ne_top.mpr (compact_coveringNumber_univ_ne_top radius radiusPositive)))

theorem compact_packingNumber_univ_ne_top (radius : ℝ≥0) (radiusPositive : 0 < radius) :
    Metric.packingNumber radius (Set.univ : Set Space) ≠ ⊤ := by
  have halfPositive : 0 < radius / 2 := by positivity
  have bound := Metric.packingNumber_two_mul_le_externalCoveringNumber (radius / 2) (Set.univ : Set Space)
  have twiceHalf : 2 * (radius / 2) = radius := by ring
  rw [twiceHalf] at bound
  exact ne_of_lt (bound.trans_lt
    (lt_top_iff_ne_top.mpr (compact_externalCoveringNumber_univ_ne_top (radius / 2) halfPositive)))

variable [MeasurableSpace Space] [BorelSpace Space]

theorem compact_coveringNumber_mass_lower_bound (physicalMeasure : Measure Space)
    [IsFiniteMeasure physicalMeasure] (subset : Set Space) (radius : ℝ≥0)
    (radiusPositive : 0 < radius) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (ballMassUpper : ∀ point ∈ subset,
      physicalMeasure.real (Metric.ball point (3 * (radius : ℝ))) ≤ bound) :
    physicalMeasure.real subset ≤
      ((Metric.coveringNumber radius (Set.univ : Set Space)).toNat : ℝ) * bound := by
  have coverFinite := compact_coveringNumber_univ_ne_top (Space := Space) radius radiusPositive
  have centersFinite := Metric.finite_minimalCover (ε := radius) (A := (Set.univ : Set Space))
  let centers : Finset Space := centersFinite.toFinset
  have centersSet : (centers : Set Space) = Metric.minimalCover radius Set.univ := by simp [centers]
  have countEquality := Metric.encard_minimalCover coverFinite
  rw [← centersSet] at countEquality
  have cardEquality : centers.card = (Metric.coveringNumber radius (Set.univ : Set Space)).toNat := by
    simpa using congrArg ENat.toNat countEquality
  have cover (point : Space) (_membership : point ∈ subset) :
      ∃ center ∈ centers, dist point center ≤ (radius : ℝ) := by
    obtain ⟨center, centerIn, near⟩ := Metric.isCover_minimalCover coverFinite (Set.mem_univ point)
    refine ⟨center, ?_, ?_⟩
    · change center ∈ (centers : Set Space)
      rwa [centersSet]
    · exact ENNReal.ofReal_le_coe.mp (by simpa only [edist_dist] using near)
  have actual := real_measure_le_finite_ball_cover_card_mul physicalMeasure subset centers
    (radius : ℝ) bound (by exact_mod_cast radiusPositive) boundNonnegative cover ballMassUpper
  simpa only [cardEquality] using actual

theorem compact_coveringNumber_mass_upper_bound (physicalMeasure : Measure Space)
    [IsFiniteMeasure physicalMeasure] (radius : ℝ≥0) (radiusPositive : 0 < radius)
    (massLower : ℝ) (massLowerNonnegative : 0 ≤ massLower)
    (ballMassLower : ∀ point : Space,
      massLower ≤ physicalMeasure.real (Metric.ball point ((radius : ℝ) / 2))) :
    ((Metric.coveringNumber radius (Set.univ : Set Space)).toNat : ℝ) * massLower ≤
      physicalMeasure.real Set.univ := by
  have packingFinite := compact_packingNumber_univ_ne_top (Space := Space) radius radiusPositive
  have centersFinite : (Metric.maximalSeparatedSet radius (Set.univ : Set Space)).Finite :=
    Set.encard_ne_top_iff.mp (by
      rw [Metric.encard_maximalSeparatedSet packingFinite]
      exact packingFinite)
  letI := centersFinite.fintype
  have separated (first second : Metric.maximalSeparatedSet radius (Set.univ : Set Space))
      (different : first ≠ second) : 2 * ((radius : ℝ) / 2) ≤ dist (first : Space) (second : Space) := by
    have valuesDifferent : (first : Space) ≠ (second : Space) := fun equality => different (Subtype.ext equality)
    have distanceBound := Metric.isSeparated_maximalSeparatedSet first.property second.property valuesDifferent
    have strict : (radius : ℝ) < dist (first : Space) (second : Space) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg radius.coe_nonneg).mp
        (by simpa only [ENNReal.ofReal_coe_nnreal, edist_dist] using distanceBound)
    linarith
  have massBound := separated_finite_ball_card_mul_le_total_mass physicalMeasure
    (fun center : Metric.maximalSeparatedSet radius (Set.univ : Set Space) => (center : Space))
    ((radius : ℝ) / 2) massLower separated (fun center => ballMassLower center)
  have cover := Metric.isCover_maximalSeparatedSet packingFinite
  have coverBound := cover.coveringNumber_le_encard (Metric.maximalSeparatedSet_subset (ε := radius) (A := (Set.univ : Set Space)))
  have cardinalBound : Metric.coveringNumber radius (Set.univ : Set Space) ≤
      (Fintype.card (Metric.maximalSeparatedSet radius (Set.univ : Set Space)) : ℕ∞) := by
    simpa only [Set.encard, ENat.card_eq_coe_fintype_card] using coverBound
  have naturalBound := ENat.toNat_le_of_le_coe cardinalBound
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast naturalBound) massLowerNonnegative).trans massBound

end
end IGS.Sec31

#print axioms IGS.Sec31.compact_coveringNumber_univ_ne_top
#print axioms IGS.Sec31.compact_packingNumber_univ_ne_top
#print axioms IGS.Sec31.compact_coveringNumber_mass_lower_bound
#print axioms IGS.Sec31.compact_coveringNumber_mass_upper_bound
