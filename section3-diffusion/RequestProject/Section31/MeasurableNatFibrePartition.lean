import RequestProject.Section31.ExponentialHoldingTimePaths

namespace IGS.Sec31.PoissonClock
open MeasureTheory Set
noncomputable section

theorem measure_nat_fibre_partition
    {Sample : Type*} [MeasurableSpace Sample] (law : Measure Sample)
    (index : Sample → ℕ) (indexMeasurable : Measurable index)
    (event : Set Sample) (eventMeasurable : MeasurableSet event) :
    law event = ∑' count : ℕ, law {sample | sample ∈ event ∧ index sample = count} := by
  have unionEquality : event = ⋃ count : ℕ, {sample | sample ∈ event ∧ index sample = count} := by
    ext sample
    simp only [mem_iUnion, mem_setOf_eq]
    constructor
    · intro membership
      exact ⟨index sample, membership, rfl⟩
    · rintro ⟨_, membership, _⟩
      exact membership
  have disjoint : Pairwise (fun first second : ℕ =>
      Disjoint {sample | sample ∈ event ∧ index sample = first}
        {sample | sample ∈ event ∧ index sample = second}) := by
    intro first second distinct
    apply Set.disjoint_left.mpr
    intro sample firstMembership secondMembership
    exact distinct (firstMembership.2.symm.trans secondMembership.2)
  have measurable (count : ℕ) : MeasurableSet {sample | sample ∈ event ∧ index sample = count} :=
    eventMeasurable.inter ((measurableSet_singleton count).preimage indexMeasurable)
  calc
    law event = law (⋃ count : ℕ, {sample | sample ∈ event ∧ index sample = count}) :=
      congrArg law unionEquality
    _ = _ := measure_iUnion disjoint measurable

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.measure_nat_fibre_partition
