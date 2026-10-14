import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-! Augment each filtration sigma algebra by all globally measure-null sets,
then take its right-continuation. The ambient sigma algebra is the completed
one. Using eventual measurability relative to the global measure is essential:
completing only the trimmed measure at a time need not add every global null
set at that time. No Markov property is part of this construction. -/

namespace IGS.Sec31.UsualAugmentation

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

variable {Sample Time : Type*} [ambient : MeasurableSpace Sample]

section NullAugmentation

variable [Preorder Time]

def nullAugmentation (measure : Measure Sample) (filtration : Filtration Time ambient) :
    Filtration Time (eventuallyMeasurableSpace ambient (ae measure)) where
  seq time := eventuallyMeasurableSpace (filtration time) (ae measure)
  mono' := by
    intro first second ordered event eventMeasurable
    obtain ⟨representative, representativeMeasurable, sameEvent⟩ := eventMeasurable
    exact ⟨representative, filtration.mono ordered _ representativeMeasurable, sameEvent⟩
  le' := by
    intro time event eventMeasurable
    obtain ⟨representative, representativeMeasurable, sameEvent⟩ := eventMeasurable
    exact ⟨representative, filtration.le time _ representativeMeasurable, sameEvent⟩

theorem nullAugmentation_measurableSet_iff
    (measure : Measure Sample) (filtration : Filtration Time ambient) (time : Time) (event : Set Sample) :
    MeasurableSet[nullAugmentation measure filtration time] event ↔
      ∃ representative, MeasurableSet[filtration time] representative ∧ event =ᵐ[measure] representative :=
  Iff.rfl

theorem filtration_le_nullAugmentation
    (measure : Measure Sample) (filtration : Filtration Time ambient) (time : Time) :
    filtration time ≤ nullAugmentation measure filtration time := by
  intro event eventMeasurable
  exact ⟨event, eventMeasurable, EventuallyEq.refl _ _⟩

theorem nullAugmentation_measurableSet_of_null
    (measure : Measure Sample) (filtration : Filtration Time ambient) (time : Time) (event : Set Sample)
    (eventNull : measure event = 0) :
    MeasurableSet[nullAugmentation measure filtration time] event :=
  ⟨∅, @MeasurableSet.empty Sample (filtration time), ae_eq_empty.mpr eventNull⟩

end NullAugmentation

section UsualAugmentation

variable [PartialOrder Time]

def usualAugmentation
    (measure : Measure Sample) (filtration : Filtration Time ambient) :
    Filtration Time (eventuallyMeasurableSpace ambient (ae measure)) :=
  (nullAugmentation measure filtration).rightCont

instance usualAugmentation_isRightContinuous
    (measure : Measure Sample) (filtration : Filtration Time ambient) :
    (usualAugmentation measure filtration).IsRightContinuous := by
  unfold usualAugmentation
  infer_instance

theorem filtration_le_usualAugmentation
    (measure : Measure Sample) (filtration : Filtration Time ambient) (time : Time) :
    filtration time ≤ usualAugmentation measure filtration time :=
  (filtration_le_nullAugmentation measure filtration time).trans
    ((nullAugmentation measure filtration).le_rightCont time)

theorem usualAugmentation_measurableSet_of_null
    (measure : Measure Sample) (filtration : Filtration Time ambient) (time : Time) (event : Set Sample)
    (eventNull : measure event = 0) :
    MeasurableSet[usualAugmentation measure filtration time] event :=
  (nullAugmentation measure filtration).le_rightCont time event
    (nullAugmentation_measurableSet_of_null measure filtration time event eventNull)

end UsualAugmentation

end
end IGS.Sec31.UsualAugmentation

#print axioms IGS.Sec31.UsualAugmentation.nullAugmentation_measurableSet_iff
#print axioms IGS.Sec31.UsualAugmentation.filtration_le_nullAugmentation
#print axioms IGS.Sec31.UsualAugmentation.nullAugmentation_measurableSet_of_null
#print axioms IGS.Sec31.UsualAugmentation.filtration_le_usualAugmentation
#print axioms IGS.Sec31.UsualAugmentation.usualAugmentation_measurableSet_of_null
