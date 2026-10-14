import RequestProject.Section31.J1FiniteJumpParameterCompactness
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Analysis.SpecificLimits.Basic

namespace IGS.Sec31.DiscreteMarkov
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 4000000

theorem interiorOrderedKnots_mem_some_separated (count : ℕ) (knots : InteriorOrderedKnots count) :
    ∃ grid : ℕ, knots.val ∈ separatedJumpKnots count (1 / (grid + 1 : ℝ)) := by
  have coordinates (index : Fin count) : ∀ᶠ grid : ℕ in atTop,
      1 / (grid + 1 : ℝ) ≤ (knots.val index).val ∧
        (knots.val index).val ≤ 1 - 1 / (grid + 1 : ℝ) := by
    have lower := tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (gt_mem_nhds (knots.property.2 index).1)
    have upper := tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (gt_mem_nhds (sub_pos.mpr (knots.property.2 index).2))
    filter_upwards [lower, upper] with grid lower upper
    constructor <;> linarith
  have pairs (first second : Fin count) : ∀ᶠ grid : ℕ in atTop,
      first < second → 1 / (grid + 1 : ℝ) ≤ (knots.val second).val - (knots.val first).val := by
    by_cases ordered : first < second
    · have positive : 0 < (knots.val second).val - (knots.val first).val :=
        sub_pos.mpr (knots.property.1 ordered)
      filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds positive)]
        with grid small
      exact fun _ => small.le
    · exact Eventually.of_forall (fun _ contradiction => False.elim (ordered contradiction))
  have together := (eventually_all.mpr coordinates).and
    (eventually_all.mpr (fun first => eventually_all.mpr (pairs first)))
  obtain ⟨grid, bounded⟩ := together.exists
  exact ⟨grid, bounded⟩

theorem isTight_singleton_of_countable_compact_capture
    {Space : Type*} [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (law : Measure Space) [IsFiniteMeasure law]
    (family : Set (Set Space)) (familyCountable : family.Countable)
    (compact : ∀ set ∈ family, IsCompact set)
    (captured : ∀ᵐ point ∂law, ∃ set ∈ family, point ∈ set) :
    IsTightMeasureSet {law} := by
  classical
  have enlargedCountable : (insert ∅ family).Countable := familyCountable.insert ∅
  obtain ⟨sets, rangeEquality⟩ := enlargedCountable.exists_eq_range (Set.insert_nonempty ∅ family)
  have setsCompact (index : ℕ) : IsCompact (sets index) := by
    have membership : sets index ∈ insert ∅ family := by rw [rangeEquality]; exact mem_range_self index
    rcases membership with empty | membership
    · rw [empty]
      exact isCompact_empty
    · exact compact _ membership
  have covered : ∀ᵐ point ∂law, point ∈ ⋃ index, sets index := by
    filter_upwards [captured] with point witness
    obtain ⟨set, inFamily, inSet⟩ := witness
    have membership : set ∈ Set.range sets := by rw [← rangeEquality]; exact mem_insert_of_mem _ inFamily
    obtain ⟨index, rfl⟩ := membership
    exact mem_iUnion.mpr ⟨index, inSet⟩
  have null : law (⋂ index, (accumulate sets index)ᶜ) = 0 := by
    rw [← compl_iUnion, iUnion_accumulate]
    exact ae_iff.mp covered
  have limit : Tendsto (fun index => law (accumulate sets index)ᶜ) atTop (𝓝 0) := by
    rw [← null]
    apply tendsto_measure_iInter_atTop
    · intro index
      exact (isCompact_accumulate setsCompact index).isClosed.measurableSet.compl.nullMeasurableSet
    · intro first second ordered
      exact compl_subset_compl.mpr (monotone_accumulate ordered)
    · exact ⟨0, measure_ne_top law _⟩
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro error errorPositive
  obtain ⟨index, bound⟩ := (limit.eventually (gt_mem_nhds errorPositive)).exists
  refine ⟨accumulate sets index, isCompact_accumulate setsCompact index, ?_⟩
  simpa only [mem_singleton_iff, forall_eq] using bound.le

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.interiorOrderedKnots_mem_some_separated
#print axioms IGS.Sec31.DiscreteMarkov.isTight_singleton_of_countable_compact_capture
