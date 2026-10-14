import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-! Borel measurability of physical ball masses as the center varies.
The proof integrates the measurable distance relation over the second
coordinate; it does not assume a measurable volume conclusion. -/

namespace IGS.Sec31
open MeasureTheory
noncomputable section

variable {Space : Type*} [PseudoMetricSpace Space] [SecondCountableTopology Space]
  [MeasurableSpace Space] [BorelSpace Space]

theorem measurable_real_ball_mass (physicalMeasure : Measure Space)
    [SFinite physicalMeasure] (radius : ℝ) :
    Measurable (fun center : Space => physicalMeasure.real (Metric.ball center radius)) := by
  have relationMeasurable : MeasurableSet
      {pair : Space × Space | dist pair.2 pair.1 < radius} :=
    measurableSet_lt (measurable_snd.dist measurable_fst) measurable_const
  have sectionMeasurable :=
    @measurable_measure_prodMk_left Space Space _ _ physicalMeasure _ _ relationMeasurable
  simpa only [Measure.real, Metric.ball, Set.preimage_setOf_eq] using
    sectionMeasurable.ennreal_toReal

theorem measurableSet_eventual_geometric_ball_mass_bound
    (physicalMeasure : Measure Space) [SFinite physicalMeasure]
    (radii bounds : ℕ → ℝ) :
    MeasurableSet {center : Space | ∃ threshold : ℕ, ∀ level : ℕ,
      threshold ≤ level → physicalMeasure.real (Metric.ball center (radii level)) ≤ bounds level} := by
  simp only [Set.setOf_exists, Set.setOf_forall]
  apply MeasurableSet.iUnion
  intro threshold
  apply MeasurableSet.iInter
  intro level
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le (measurable_real_ball_mass physicalMeasure (radii level)) measurable_const

end
end IGS.Sec31

#print axioms IGS.Sec31.measurable_real_ball_mass
#print axioms IGS.Sec31.measurableSet_eventual_geometric_ball_mass_bound
