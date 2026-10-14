import RequestProject.Section31.CanonicalContinuousPathProcess
import RequestProject.Section31.ContinuousTimePathFamilyMeasurability
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Deterministic-time Markov integral identities are derived from finite
observation formulas. No conditional expectation or Markov identity is
assumed by the actual consumer. -/

namespace IGS.Sec31.FiniteObservationTimeReindexing
open MeasureTheory Filter Topology
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 5000000

theorem exists_monotone_zero_start_terminal_time_product_representation
    {Space : Type*} [TopologicalSpace Space] (dimension : ℕ)
    (times : Fin dimension → ℝ≥0) (tests : Fin dimension → C(Space, ℝ))
    (horizon : ℝ≥0) (timesBound : ∀ index, times index ≤ horizon) :
    ∃ count : ℕ, ∃ orderedTimes : ℕ → ℝ≥0,
      Monotone orderedTimes ∧ orderedTimes 0 = 0 ∧ orderedTimes count = horizon ∧
      ∃ orderedTests : ℕ → C(Space, ℝ),
        ∀ path : ℝ≥0 → Space,
          (∏ index : Fin dimension, tests index (path (times index))) =
            ∏ index : Fin count, orderedTests index.val (path (orderedTimes index.val)) := by
  let timeSet : Finset ℝ≥0 := insert horizon (insert 0 (Finset.univ.image times))
  have zeroMembership : (0 : ℝ≥0) ∈ timeSet := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have cardPositive : 0 < timeSet.card := Finset.card_pos.mpr ⟨0, zeroMembership⟩
  let count := timeSet.card - 1
  have cardIdentity : timeSet.card = count + 1 := by
    dsimp only [count]
    exact (Nat.sub_add_cancel (Nat.succ_le_iff.mpr cardPositive)).symm
  let grid : Fin (count + 1) ↪o ℝ≥0 := timeSet.orderEmbOfFin cardIdentity
  have zeroRange : (0 : ℝ≥0) ∈ Set.range grid := by
    rw [Finset.range_orderEmbOfFin]
    exact zeroMembership
  obtain ⟨zeroIndex, zeroIdentity⟩ := zeroRange
  have gridZero : grid 0 = 0 := by
    apply le_antisymm
    · simpa only [zeroIdentity] using grid.monotone (Fin.zero_le zeroIndex)
    · exact zero_le _
  let orderedTimes (index : ℕ) : ℝ≥0 :=
    grid ⟨min index count, Nat.lt_succ_of_le (Nat.min_le_right index count)⟩
  have timeIdentity (index : Fin (count + 1)) : orderedTimes index.val = grid index := by
    dsimp only [orderedTimes]
    congr 1
    apply Fin.ext
    exact Nat.min_eq_left (Nat.le_of_lt_succ index.isLt)
  have timesMonotone : Monotone orderedTimes := by
    intro first second ordered
    apply grid.monotone
    change min first count ≤ min second count
    exact min_le_min_right count ordered
  have startsAtZero : orderedTimes 0 = 0 :=
    (timeIdentity (0 : Fin (count + 1))).trans gridZero
  let orderedTests (index : ℕ) : C(Space, ℝ) :=
    ∏ original ∈ Finset.univ.filter (fun original : Fin dimension => times original = orderedTimes index),
      tests original
  have gridBound (index : Fin (count + 1)) : grid index ≤ horizon := by
    have membership : grid index ∈ timeSet := by
      simpa only [grid, Finset.range_orderEmbOfFin] using
        (show grid index ∈ Set.range grid from ⟨index, rfl⟩)
    rcases Finset.mem_insert.mp membership with equality | membership
    · exact equality.le
    · rcases Finset.mem_insert.mp membership with equality | membership
      · exact equality.le.trans (zero_le horizon)
      · obtain ⟨original, _, equality⟩ := Finset.mem_image.mp membership
        rw [← equality]
        exact timesBound original
  have horizonRange : horizon ∈ Set.range grid := by
    rw [Finset.range_orderEmbOfFin]
    change horizon ∈ timeSet
    exact Finset.mem_insert_self horizon (insert 0 (Finset.univ.image times))
  obtain ⟨horizonIndex, horizonIdentity⟩ := horizonRange
  have lastTime : grid (Fin.last count) = horizon := by
    apply le_antisymm (gridBound _)
    simpa only [horizonIdentity] using grid.monotone (Fin.le_last horizonIndex)
  have endpoint : orderedTimes (count + 1) = horizon := by
    simpa only [orderedTimes, min_eq_right (Nat.le_succ count)] using lastTime
  refine ⟨count + 1, orderedTimes, timesMonotone, startsAtZero, endpoint, orderedTests, ?_⟩
  intro path
  have mapsTo : ∀ index ∈ (Finset.univ : Finset (Fin dimension)), times index ∈ timeSet := by
    intro index _
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩))
  have grouped := Finset.prod_fiberwise_of_maps_to mapsTo
    (fun index : Fin dimension => tests index (path (times index)))
  rw [← Finset.image_orderEmbOfFin_univ timeSet cardIdentity,
    Finset.prod_image grid.injective.injOn] at grouped
  have groupedFinite :
      (∏ index : Fin (count + 1),
        ∏ original ∈ Finset.univ.filter (fun original : Fin dimension => times original = grid index),
          tests original (path (times original))) =
        ∏ original : Fin dimension, tests original (path (times original)) := grouped
  have evaluation (index : Fin (count + 1)) :
      orderedTests index.val (path (orderedTimes index.val)) =
        ∏ original ∈ Finset.univ.filter (fun original : Fin dimension => times original = grid index),
          tests original (path (times original)) := by
    simp only [orderedTests, ContinuousMap.prod_apply, timeIdentity]
    apply Finset.prod_congr rfl
    intro original membership
    rw [(Finset.mem_filter.mp membership).2]
  have regrouped :
      (∏ index : Fin (count + 1), orderedTests index.val (path (orderedTimes index.val))) =
        ∏ original : Fin dimension, tests original (path (times original)) := by
    calc
      _ = ∏ index : Fin (count + 1),
          ∏ original ∈ Finset.univ.filter (fun original : Fin dimension => times original = grid index),
            tests original (path (times original)) := by
        apply Finset.prod_congr rfl
        intro index _
        exact evaluation index
      _ = _ := groupedFinite
  exact regrouped.symm


end
end IGS.Sec31.FiniteObservationTimeReindexing

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 6000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

local instance continuousDeterministicMarkovMeasurableSpace : MeasurableSpace C(ℝ≥0, State) := borel _
local instance continuousDeterministicMarkovBorelSpace : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

def ContinuousPathOrderedBanachObservations
    (law : ProbabilityMeasure C(ℝ≥0, State))
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ)) (start : State) : Prop :=
  ∀ (times : ℕ → ℝ≥0), Monotone times → times 0 = 0 →
    ∀ (tests : ℕ → C(State, ℝ)) (count : ℕ) (terminal : C(State, ℝ)),
      (∫ path : C(ℝ≥0, State), (∏ index : Fin count, tests index.val (path (times index.val))) *
        terminal (path (times count)) ∂(law : Measure C(ℝ≥0, State))) =
        BanachBackwardObservations.backwardProduct semigroup
          (fun test => ContinuousLinearMap.mul ℝ C(State, ℝ) test)
          ((List.range count).map (fun index => (times (index + 1) - times index, tests index))) terminal start

theorem continuousBackwardProduct_append
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (first second : List (ℝ≥0 × C(State, ℝ))) (terminal : C(State, ℝ)) :
    BanachBackwardObservations.backwardProduct semigroup
        (fun test => ContinuousLinearMap.mul ℝ C(State, ℝ) test) (first ++ second) terminal =
      BanachBackwardObservations.backwardProduct semigroup
        (fun test => ContinuousLinearMap.mul ℝ C(State, ℝ) test) first
        (BanachBackwardObservations.backwardProduct semigroup
          (fun test => ContinuousLinearMap.mul ℝ C(State, ℝ) test) second terminal) := by
  induction first with
  | nil => rfl
  | cons observation remaining induction =>
      simp only [List.cons_append, BanachBackwardObservations.backwardProduct, induction]

theorem continuousPath_ordered_past_future_factorization
    (law : ProbabilityMeasure C(ℝ≥0, State))
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ)) (start : State)
    (observations : ContinuousPathOrderedBanachObservations law semigroup start)
    (times : ℕ → ℝ≥0) (timesMonotone : Monotone times) (startsAtZero : times 0 = 0)
    (tests : ℕ → C(State, ℝ)) (count : ℕ) (delay : ℝ≥0) (terminal : C(State, ℝ)) :
    (∫ path : C(ℝ≥0, State), (∏ index : Fin count, tests index.val (path (times index.val))) *
      terminal (path (times count + delay)) ∂(law : Measure C(ℝ≥0, State))) =
      ∫ path : C(ℝ≥0, State), (∏ index : Fin count, tests index.val (path (times index.val))) *
        semigroup delay terminal (path (times count)) ∂(law : Measure C(ℝ≥0, State)) := by
  let extendedTimes (index : ℕ) : ℝ≥0 :=
    if index ≤ count then times index else times count + delay
  let extendedTests (index : ℕ) : C(State, ℝ) := if index < count then tests index else 1
  have extendedMonotone : Monotone extendedTimes := by
    intro first second ordered
    by_cases firstBound : first ≤ count
    · by_cases secondBound : second ≤ count
      · simpa only [extendedTimes, if_pos firstBound, if_pos secondBound] using timesMonotone ordered
      · simpa only [extendedTimes, if_pos firstBound, if_neg secondBound] using
          (timesMonotone firstBound).trans (le_add_of_nonneg_right (zero_le delay))
    · have secondNotBound : ¬ second ≤ count := fun bound => firstBound (ordered.trans bound)
      simp only [extendedTimes, if_neg firstBound, if_neg secondNotBound, le_refl]
  have extendedZero : extendedTimes 0 = 0 := by
    simpa only [extendedTimes, if_pos (Nat.zero_le count)] using startsAtZero
  have oldFactor (path : C(ℝ≥0, State)) (index : Fin count) :
      extendedTests index.val (path (extendedTimes index.val)) = tests index.val (path (times index.val)) := by
    simp only [extendedTests, if_pos index.isLt, extendedTimes, if_pos (Nat.le_of_lt index.isLt)]
  have extendedProduct (path : C(ℝ≥0, State)) :
      (∏ index : Fin (count + 1), extendedTests index.val (path (extendedTimes index.val))) *
        terminal (path (extendedTimes (count + 1))) =
        (∏ index : Fin count, tests index.val (path (times index.val))) *
          terminal (path (times count + delay)) := by
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, oldFactor, extendedTests,
      if_neg (lt_irrefl count), ContinuousMap.one_apply, mul_one,
      extendedTimes, if_neg (show ¬ count + 1 ≤ count by omega)]
  have firstObservations :
      (List.range count).map (fun index =>
        (extendedTimes (index + 1) - extendedTimes index, extendedTests index)) =
      (List.range count).map (fun index => (times (index + 1) - times index, tests index)) := by
    apply List.map_congr_left
    intro index membership
    have bound := List.mem_range.mp membership
    simp only [extendedTimes, if_pos (Nat.le_of_lt bound), if_pos (Nat.succ_le_of_lt bound),
      extendedTests, if_pos bound]
  have backwardIdentity :
      BanachBackwardObservations.backwardProduct semigroup
        (fun test => ContinuousLinearMap.mul ℝ C(State, ℝ) test)
        ((List.range (count + 1)).map (fun index =>
          (extendedTimes (index + 1) - extendedTimes index, extendedTests index))) terminal =
      BanachBackwardObservations.backwardProduct semigroup
        (fun test => ContinuousLinearMap.mul ℝ C(State, ℝ) test)
        ((List.range count).map (fun index => (times (index + 1) - times index, tests index)))
        (semigroup delay terminal) := by
    rw [List.range_succ, List.map_append, firstObservations, continuousBackwardProduct_append]
    simp [extendedTimes, extendedTests, BanachBackwardObservations.backwardProduct]
  have futureObservation := observations extendedTimes extendedMonotone extendedZero extendedTests (count + 1) terminal
  have currentObservation := observations times timesMonotone startsAtZero tests count (semigroup delay terminal)
  calc
    _ = ∫ path : C(ℝ≥0, State),
        (∏ index : Fin (count + 1), extendedTests index.val (path (extendedTimes index.val))) *
          terminal (path (extendedTimes (count + 1))) ∂(law : Measure C(ℝ≥0, State)) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun path => (extendedProduct path).symm
    _ = _ := futureObservation.trans
      ((congrArg (fun function : C(State, ℝ) => function start) backwardIdentity).trans currentObservation.symm)

theorem continuousPath_finite_past_future_factorization
    (law : ProbabilityMeasure C(ℝ≥0, State))
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ)) (start : State)
    (observations : ContinuousPathOrderedBanachObservations law semigroup start)
    (time delay : ℝ≥0) (dimension : ℕ) (pastTimes : Fin dimension → ℝ≥0)
    (pastTimesBound : ∀ index, pastTimes index ≤ time)
    (tests : Fin dimension → C(State, ℝ)) (terminal : C(State, ℝ)) :
    (∫ path : C(ℝ≥0, State), (∏ index, tests index (path (pastTimes index))) *
      terminal (path (time + delay)) ∂(law : Measure C(ℝ≥0, State))) =
      ∫ path : C(ℝ≥0, State), (∏ index, tests index (path (pastTimes index))) *
        semigroup delay terminal (path time) ∂(law : Measure C(ℝ≥0, State)) := by
  obtain ⟨count, orderedTimes, timesMonotone, startsAtZero, endpoint, orderedTests, representation⟩ :=
    FiniteObservationTimeReindexing.exists_monotone_zero_start_terminal_time_product_representation
      dimension pastTimes tests time pastTimesBound
  have factorization := continuousPath_ordered_past_future_factorization law semigroup start observations
    orderedTimes timesMonotone startsAtZero orderedTests count delay terminal
  have futureIdentity :
      (∫ path : C(ℝ≥0, State), (∏ index, tests index (path (pastTimes index))) *
        terminal (path (time + delay)) ∂(law : Measure C(ℝ≥0, State))) =
      ∫ path : C(ℝ≥0, State), (∏ index : Fin count, orderedTests index.val (path (orderedTimes index.val))) *
        terminal (path (orderedTimes count + delay)) ∂(law : Measure C(ℝ≥0, State)) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun path => by
      dsimp only
      rw [representation path, endpoint]
  have currentIdentity :
      (∫ path : C(ℝ≥0, State), (∏ index, tests index (path (pastTimes index))) *
        semigroup delay terminal (path time) ∂(law : Measure C(ℝ≥0, State))) =
      ∫ path : C(ℝ≥0, State), (∏ index : Fin count, orderedTests index.val (path (orderedTimes index.val))) *
        semigroup delay terminal (path (orderedTimes count)) ∂(law : Measure C(ℝ≥0, State)) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun path => by
      dsimp only
      rw [representation path, endpoint]
  exact futureIdentity.trans (factorization.trans currentIdentity.symm)

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.FiniteObservationTimeReindexing.exists_monotone_zero_start_terminal_time_product_representation
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_ordered_past_future_factorization
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_finite_past_future_factorization


