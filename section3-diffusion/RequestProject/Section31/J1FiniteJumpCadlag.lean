import RequestProject.Section31.J1FiniteJumpFunctions
import RequestProject.Section31.J1UnitGridReconstruction

namespace IGS.Sec31.DiscreteMarkov
noncomputable section
open Set Filter Topology

theorem finiteJumpCount_eventually_right {count : ℕ} (knots : Fin count → UnitJ1Time)
    (time : UnitJ1Time) :
    ∀ᶠ nextTime in 𝓝[Ici time] time, finiteJumpCount knots nextTime = finiteJumpCount knots time := by
  classical
  have individual (index : Fin count) :
      ∀ᶠ nextTime in 𝓝[Ici time] time, (knots index ≤ nextTime ↔ knots index ≤ time) := by
    by_cases before : knots index ≤ time
    · filter_upwards [self_mem_nhdsWithin] with nextTime after
      exact ⟨fun _ => before, fun _ => before.trans after⟩
    · have after : time < knots index := lt_of_not_ge before
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds after)] with nextTime nextTimeBefore
      exact ⟨fun ordered => False.elim (not_le_of_gt nextTimeBefore ordered), fun ordered => False.elim (before ordered)⟩
  filter_upwards [eventually_all.mpr individual] with nextTime agreement
  unfold finiteJumpCount
  congr 1
  ext index
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, agreement]

theorem finiteJumpCount_eventually_left {count : ℕ} (knots : Fin count → UnitJ1Time)
    (time : UnitJ1Time) :
    ∀ᶠ previous in 𝓝[Iio time] time,
      finiteJumpCount knots previous = (Finset.univ.filter (fun index => knots index < time)).card := by
  classical
  have individual (index : Fin count) :
      ∀ᶠ previous in 𝓝[Iio time] time, (knots index ≤ previous ↔ knots index < time) := by
    by_cases before : knots index < time
    · filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds before)] with previous after
      exact ⟨fun _ => before, fun _ => after.le⟩
    · have after : time ≤ knots index := le_of_not_gt before
      filter_upwards [self_mem_nhdsWithin] with previous previousBefore
      exact ⟨fun ordered => False.elim (not_le_of_gt (previousBefore.trans_le after) ordered),
        fun ordered => False.elim (before ordered)⟩
  filter_upwards [eventually_all.mpr individual] with previous agreement
  unfold finiteJumpCount
  congr 1
  ext index
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, agreement]

theorem finiteEndpointJumpFunction_isCadlag {State : Type*} [MetricSpace State] {count : ℕ}
    (knots : Fin count → UnitJ1Time) (states : Fin (count + 1) → State) (endpoint : State) :
    IsCadlagPath (finiteEndpointJumpFunction knots states endpoint) := by
  classical
  constructor
  · intro time
    by_cases terminal : time.val = 1
    · apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with nextTime after
      have lower : time.val ≤ nextTime.val := after
      have nextTimeTerminal : nextTime.val = 1 := le_antisymm nextTime.property.2
        (by simpa only [terminal] using lower)
      simp only [finiteEndpointJumpFunction, if_pos nextTimeTerminal, if_pos terminal]
    · have timeBefore : time < (⟨1, by norm_num⟩ : UnitJ1Time) :=
        lt_of_le_of_ne time.property.2 terminal
      apply tendsto_const_nhds.congr'
      filter_upwards [finiteJumpCount_eventually_right knots time,
        nhdsWithin_le_nhds (Iio_mem_nhds timeBefore)] with nextTime countEquality nextTimeBefore
      have nextTimeNotTerminal : nextTime.val ≠ 1 := ne_of_lt nextTimeBefore
      simp only [finiteEndpointJumpFunction, if_neg terminal, if_neg nextTimeNotTerminal]
      unfold finiteJumpFunction
      congr 1
      apply Fin.ext
      exact countEquality.symm
  · intro time
    let leftCount := (Finset.univ.filter (fun index => knots index < time)).card
    have countBound : leftCount ≤ count :=
      (Finset.card_filter_le _ _).trans_eq (Finset.card_fin count)
    refine ⟨states ⟨leftCount, Nat.lt_succ_of_le countBound⟩, ?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [finiteJumpCount_eventually_left knots time, self_mem_nhdsWithin]
      with previous countEquality previousBefore
    have previousNotTerminal : previous.val ≠ 1 := ne_of_lt (previousBefore.trans_le time.property.2)
    simp only [finiteEndpointJumpFunction, if_neg previousNotTerminal]
    unfold finiteJumpFunction
    congr 1
    apply Fin.ext
    exact countEquality.symm

def finiteEndpointCadlagJ1Path {State : Type*} [MetricSpace State] {count : ℕ}
    (knots : Fin count → UnitJ1Time) (states : Fin (count + 1) → State) (endpoint : State) :
    UnitCadlagJ1Path State :=
  ⟨⟨finiteEndpointJumpFunction knots states endpoint⟩, finiteEndpointJumpFunction_isCadlag knots states endpoint⟩

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finiteEndpointJumpFunction_isCadlag
#print axioms IGS.Sec31.DiscreteMarkov.finiteEndpointCadlagJ1Path

