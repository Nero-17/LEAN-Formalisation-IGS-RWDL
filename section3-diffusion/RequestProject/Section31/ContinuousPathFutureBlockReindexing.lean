import RequestProject.Section31.ContinuousPathStoppingFutureBlocks
import Mathlib.Algebra.BigOperators.Fin

/-! Translate the list recursion into the ordered observation products
already proved for the same global continuous-path family. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal BigOperators
noncomputable section

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

theorem continuousPathFutureObservationProduct_indexed
    (path : C(ℝ≥0, State)) (start : ℝ≥0)
    (times : ℕ → ℝ≥0) (timesMonotone : Monotone times)
    (tests : ℕ → C(State, ℝ)) (terminal : C(State, ℝ)) (count offset : ℕ) :
    continuousPathFutureObservationProduct
      ((List.range count).map (fun index =>
        (times (offset + index + 1) - times (offset + index), tests (offset + index))))
      terminal path (start + times offset) =
      (∏ index : Fin count, tests (offset + index.val) (path (start + times (offset + index.val)))) *
        terminal (path (start + times (offset + count))) := by
  induction count generalizing offset with
  | zero => simp [continuousPathFutureObservationProduct]
  | succ count induction =>
      have listIdentity :
          ((List.range (count + 1)).map (fun index =>
            (times (offset + index + 1) - times (offset + index), tests (offset + index)))) =
          (times (offset + 1) - times offset, tests offset) ::
            ((List.range count).map (fun index =>
              (times ((offset + 1) + index + 1) - times ((offset + 1) + index), tests ((offset + 1) + index)))) := by
        simp [List.range_succ_eq_map, Function.comp_def, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      have nextTime : (start + times offset) + (times (offset + 1) - times offset) =
          start + times (offset + 1) := by
        rw [add_assoc, add_tsub_cancel_of_le (timesMonotone (Nat.le_succ offset))]
      rw [listIdentity, continuousPathFutureObservationProduct, nextTime, induction, Fin.prod_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, Nat.add_zero]
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      exact (mul_assoc _ _ _).symm

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousPathFutureObservationProduct_indexed
