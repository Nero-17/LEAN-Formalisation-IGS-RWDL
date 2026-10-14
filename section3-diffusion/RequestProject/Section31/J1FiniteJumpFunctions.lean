import RequestProject.Section31.J1IntervalFiniteKnotsAlignment
import RequestProject.Section31.J1UnitTimeInstances

/-! Finite step functions, with the terminal value retained separately,
are aligned by the actual interval OrderIso. The resulting bound uses the
repository's genuine real-infimum J1 distance, not a renamed uniform norm. -/

namespace IGS.Sec31.DiscreteMarkov
open Set
open scoped UniformConvergence
noncomputable section

def finiteJumpCount {count : ℕ} (knots : Fin count → UnitJ1Time) (time : UnitJ1Time) : ℕ := by
  classical
  exact (Finset.univ.filter (fun index => knots index ≤ time)).card

theorem finiteJumpCount_le {count : ℕ} (knots : Fin count → UnitJ1Time) (time : UnitJ1Time) :
    finiteJumpCount knots time ≤ count := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_fin count)

def finiteJumpFunction {State : Type*} {count : ℕ} (knots : Fin count → UnitJ1Time)
    (states : Fin (count + 1) → State) (time : UnitJ1Time) : State :=
  states ⟨finiteJumpCount knots time, Nat.lt_succ_of_le (finiteJumpCount_le knots time)⟩

def finiteEndpointJumpFunction {State : Type*} {count : ℕ} (knots : Fin count → UnitJ1Time)
    (states : Fin (count + 1) → State) (endpoint : State) (time : UnitJ1Time) : State :=
  if time.val = 1 then endpoint else finiteJumpFunction knots states time

theorem finiteJumpFunction_time_change {State : Type*} {count : ℕ}
    (first second : Fin count → UnitJ1Time) (states : Fin (count + 1) → State)
    (change : UnitJ1Time ≃o UnitJ1Time) (knotIdentity : ∀ index, change (first index) = second index)
    (time : UnitJ1Time) :
    finiteJumpFunction second states (change time) = finiteJumpFunction first states time := by
  classical
  have counts : finiteJumpCount second (change time) = finiteJumpCount first time := by
    unfold finiteJumpCount
    congr 1
    ext index
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← knotIdentity index, change.le_iff_le]
  unfold finiteJumpFunction
  congr 1
  apply Fin.ext
  exact counts

theorem finiteEndpointJumpFunction_time_change {State : Type*} {count : ℕ}
    (first second : Fin count → UnitJ1Time) (states : Fin (count + 1) → State) (endpoint : State)
    (change : UnitJ1Time ≃o UnitJ1Time) (knotIdentity : ∀ index, change (first index) = second index)
    (time : UnitJ1Time) :
    finiteEndpointJumpFunction second states endpoint (change time) =
      finiteEndpointJumpFunction first states endpoint time := by
  have terminalEquivalent : (change time).val = 1 ↔ time.val = 1 := by
    constructor
    · intro terminal
      have equality : change time = (⟨1, by norm_num⟩ : UnitJ1Time) := Subtype.ext terminal
      rw [← intervalOrderIso_one_fixed change] at equality
      exact congrArg Subtype.val (change.injective equality)
    · intro terminal
      have equality : time = (⟨1, by norm_num⟩ : UnitJ1Time) := Subtype.ext terminal
      rw [equality, intervalOrderIso_one_fixed change]
  unfold finiteEndpointJumpFunction
  simp only [terminalEquivalent]
  split_ifs
  · rfl
  · exact finiteJumpFunction_time_change first second states change knotIdentity time

theorem finiteEndpointJumpFunction_J1_le_clock_error
    {State : Type*} [MetricSpace State] [BoundedSpace State] {count : ℕ}
    (first second : Fin count → UnitJ1Time) (states : Fin (count + 1) → State) (endpoint : State)
    (change : UnitJ1Time ≃o UnitJ1Time) (knotIdentity : ∀ index, change (first index) = second index)
    (error : ℝ) (errorNonnegative : 0 ≤ error)
    (timeBound : ∀ time, dist (change time) time ≤ error) :
    skorokhodJ1Distance (finiteEndpointJumpFunction first states endpoint)
      (finiteEndpointJumpFunction second states endpoint) ≤ error := by
  apply (skorokhodJ1Distance_le_cost _ _ change).trans
  have clockBound : dist (UniformFun.ofFun (fun time => change time)) (UniformFun.ofFun id) ≤ error :=
    (UniformFun.dist_le errorNonnegative).mpr timeBound
  have pathEquality : (fun time => finiteEndpointJumpFunction second states endpoint (change time)) =
      finiteEndpointJumpFunction first states endpoint :=
    funext (finiteEndpointJumpFunction_time_change first second states endpoint change knotIdentity)
  unfold skorokhodJ1Cost
  rw [pathEquality, dist_self]
  exact max_le clockBound errorNonnegative

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finiteJumpFunction_time_change
#print axioms IGS.Sec31.DiscreteMarkov.finiteEndpointJumpFunction_time_change
#print axioms IGS.Sec31.DiscreteMarkov.finiteEndpointJumpFunction_J1_le_clock_error
