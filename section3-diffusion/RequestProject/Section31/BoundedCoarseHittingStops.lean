import RequestProject.Section31.BoundedStoppingFutureBlock
import Mathlib.Data.Nat.Find

/-! Actual capped coarse-skeleton hitting times. A deterministic path scanner
records its last coarse point and the number of successive distinct coarse
arrivals. The stopping histories are proved from those actual coordinates;
no regeneration or strong Markov assumption is introduced. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped BigOperators ProbabilityTheory Classical

noncomputable section
set_option maxHeartbeats 4000000

variable {X : Type} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X]

def historyBefore {time : ℕ} (earlier : ℕ) (bounded : earlier ≤ time)
    (history : Finset.Iic time → X) : Finset.Iic earlier → X :=
  fun index => history ⟨index.val,
    Finset.mem_Iic.mpr ((Finset.mem_Iic.mp index.property).trans bounded)⟩

def cappedHitIndex (horizon : ℕ)
    (predicate : (time : ℕ) → (Finset.Iic time → X) → Prop)
    (path : ℕ → X) : Fin (horizon + 1) :=
  ⟨Nat.find (show ∃ time, time = horizon ∨ predicate time (frestrictLe time path) from
    ⟨horizon, Or.inl rfl⟩),
    Nat.lt_succ_of_le (Nat.find_min'
      (show ∃ time, time = horizon ∨ predicate time (frestrictLe time path) from
        ⟨horizon, Or.inl rfl⟩) (Or.inl rfl))⟩

def cappedHitHistory (horizon : ℕ)
    (predicate : (time : ℕ) → (Finset.Iic time → X) → Prop)
    (index : Fin (horizon + 1)) : Set (Finset.Iic index.val → X) :=
  {history | (index.val = horizon ∨ predicate index.val history) ∧
    ∀ earlier : Fin index.val,
      ¬predicate earlier.val
        (historyBefore earlier.val (Nat.le_of_lt earlier.isLt) history)}

theorem cappedHitIndex_eq_iff (horizon : ℕ)
    (predicate : (time : ℕ) → (Finset.Iic time → X) → Prop)
    (index : Fin (horizon + 1)) (path : ℕ → X) :
    cappedHitIndex horizon predicate path = index ↔
      frestrictLe index.val path ∈ cappedHitHistory horizon predicate index := by
  unfold cappedHitIndex
  rw [Fin.ext_iff, Nat.find_eq_iff]
  change ((index.val = horizon ∨ predicate index.val (frestrictLe index.val path)) ∧
      ∀ earlier < index.val,
        ¬(earlier = horizon ∨ predicate earlier (frestrictLe earlier path))) ↔ _
  constructor
  · rintro ⟨current, before⟩
    refine ⟨current, ?_⟩
    intro earlier occurs
    apply before earlier.val earlier.isLt
    exact Or.inr occurs
  · rintro ⟨current, before⟩
    refine ⟨current, ?_⟩
    intro earlier bounded occurs
    rcases occurs with capped | occurs
    · have indexBound : index.val ≤ horizon := Nat.le_of_lt_succ index.isLt
      omega
    · exact before ⟨earlier, bounded⟩ occurs

def boundedFirstHistoryHit (horizon : ℕ)
    (predicate : (time : ℕ) → (Finset.Iic time → X) → Prop) :
    BoundedHistoryStop (X := X) horizon where
  time := cappedHitIndex horizon predicate
  historyEvent := cappedHitHistory horizon predicate
  level_iff := cappedHitIndex_eq_iff horizon predicate

theorem cappedHitIndex_before (horizon : ℕ)
    (predicate : (time : ℕ) → (Finset.Iic time → X) → Prop)
    (path : ℕ → X) {earlier : ℕ}
    (before : earlier < (cappedHitIndex horizon predicate path).val) :
    ¬predicate earlier (frestrictLe earlier path) := by
  exact fun occurs => Nat.find_min _ before (Or.inr occurs)

theorem cappedHitIndex_occurs_before_cap (horizon : ℕ)
    (predicate : (time : ℕ) → (Finset.Iic time → X) → Prop)
    (path : ℕ → X) (beforeCap : (cappedHitIndex horizon predicate path).val < horizon) :
    predicate (cappedHitIndex horizon predicate path).val
      (frestrictLe (cappedHitIndex horizon predicate path).val path) := by
  have occurs := Nat.find_spec
    (show ∃ time, time = horizon ∨ predicate time (frestrictLe time path) from
      ⟨horizon, Or.inl rfl⟩)
  rcases occurs with capped | occurs
  · exact False.elim ((Nat.ne_of_lt beforeCap) capped)
  · exact occurs

theorem cappedHitIndex_le_of_occurs (horizon : ℕ)
    (predicate : (time : ℕ) → (Finset.Iic time → X) → Prop)
    (time : ℕ) (path : ℕ → X) (occurs : predicate time (frestrictLe time path)) :
    (cappedHitIndex horizon predicate path).val ≤ time := by
  exact Nat.find_min'
    (show ∃ index, index = horizon ∨ predicate index (frestrictLe index path) from
      ⟨horizon, Or.inl rfl⟩) (Or.inr occurs)

def coarseArrivalUpdate (coarse : Finset X) (point : X) (state : Option X × ℕ) :
    Option X × ℕ :=
  if point ∈ coarse ∧ state.1 ≠ some point then (some point, state.2 + 1) else state

def coarseArrivalState (coarse : Finset X) (path : ℕ → X) : ℕ → Option X × ℕ
  | 0 => if path 0 ∈ coarse then (some (path 0), 1) else (none, 0)
  | time + 1 => coarseArrivalUpdate coarse (path (time + 1))
      (coarseArrivalState coarse path time)

theorem coarseArrivalState_congr (coarse : Finset X) (first second : ℕ → X)
    (time : ℕ) (agree : ∀ index ≤ time, first index = second index) :
    coarseArrivalState coarse first time = coarseArrivalState coarse second time := by
  revert agree
  induction time with
  | zero =>
    intro agree
    simp only [coarseArrivalState, agree 0 le_rfl]
  | succ time inductionHypothesis =>
    intro agree
    rw [coarseArrivalState, coarseArrivalState, agree (time + 1) le_rfl,
      inductionHypothesis (fun index bounded => agree index (bounded.trans (Nat.le_succ time)))]

def completedHistory {time : ℕ} (history : Finset.Iic time → X) : ℕ → X :=
  fun index => if bounded : index ≤ time then history ⟨index, Finset.mem_Iic.mpr bounded⟩
    else history ⟨0, Finset.mem_Iic.mpr (Nat.zero_le time)⟩

def coarseArrivalHistory (coarse : Finset X) (time : ℕ)
    (history : Finset.Iic time → X) : Option X × ℕ :=
  coarseArrivalState coarse (completedHistory history) time

theorem coarseArrivalHistory_restrict (coarse : Finset X) (time : ℕ) (path : ℕ → X) :
    coarseArrivalHistory coarse time (frestrictLe time path) =
      coarseArrivalState coarse path time := by
  apply coarseArrivalState_congr
  intro index bounded
  simp only [completedHistory, dif_pos bounded, frestrictLe_apply]

/-- Arrival number zero is the first coarse hit. Each subsequent arrival must
be at a coarse point different from the last recorded coarse point. The
horizon value is also the cap sentinel and is not asserted to be a hit. -/
def boundedCoarseArrival (coarse : Finset X) (arrival horizon : ℕ) :
    BoundedHistoryStop (X := X) horizon :=
  boundedFirstHistoryHit horizon
    (fun time history => arrival + 1 ≤ (coarseArrivalHistory coarse time history).2)

theorem boundedCoarseArrival_before (coarse : Finset X) (arrival horizon : ℕ)
    (path : ℕ → X) {earlier : ℕ}
    (before : earlier < ((boundedCoarseArrival coarse arrival horizon).time path).val) :
    (coarseArrivalState coarse path earlier).2 < arrival + 1 := by
  have excluded := cappedHitIndex_before horizon
    (fun time history => arrival + 1 ≤ (coarseArrivalHistory coarse time history).2)
    path before
  dsimp only at excluded
  rw [coarseArrivalHistory_restrict] at excluded
  exact Nat.lt_of_not_ge excluded

theorem boundedCoarseArrival_occurs (coarse : Finset X) (arrival horizon : ℕ)
    (path : ℕ → X)
    (beforeCap : ((boundedCoarseArrival coarse arrival horizon).time path).val < horizon) :
    arrival + 1 ≤ (coarseArrivalState coarse path
      ((boundedCoarseArrival coarse arrival horizon).time path).val).2 := by
  have occurs := cappedHitIndex_occurs_before_cap horizon
    (fun time history => arrival + 1 ≤ (coarseArrivalHistory coarse time history).2)
    path beforeCap
  dsimp only at occurs
  rwa [coarseArrivalHistory_restrict] at occurs

theorem coarseArrivalState_increase (coarse : Finset X) (path : ℕ → X) (time : ℕ)
    (increased : (coarseArrivalState coarse path time).2 <
      (coarseArrivalState coarse path (time + 1)).2) :
    path (time + 1) ∈ coarse ∧
      (coarseArrivalState coarse path (time + 1)).1 = some (path (time + 1)) := by
  by_cases arrives : path (time + 1) ∈ coarse ∧
      (coarseArrivalState coarse path time).1 ≠ some (path (time + 1))
  · simpa only [coarseArrivalState, coarseArrivalUpdate, if_pos arrives] using
      (show path (time + 1) ∈ coarse ∧ some (path (time + 1)) = some (path (time + 1))
        from ⟨arrives.1, rfl⟩)
  · simp only [coarseArrivalState, coarseArrivalUpdate, if_neg arrives] at increased
    exact False.elim (Nat.lt_irrefl _ increased)

theorem boundedCoarseArrival_is_coarse (coarse : Finset X) (arrival horizon : ℕ)
    (path : ℕ → X)
    (beforeCap : ((boundedCoarseArrival coarse arrival horizon).time path).val < horizon) :
    path ((boundedCoarseArrival coarse arrival horizon).time path).val ∈ coarse ∧
      (coarseArrivalState coarse path
        ((boundedCoarseArrival coarse arrival horizon).time path).val).1 =
          some (path ((boundedCoarseArrival coarse arrival horizon).time path).val) := by
  have occurs := boundedCoarseArrival_occurs coarse arrival horizon path beforeCap
  generalize timeEquality : ((boundedCoarseArrival coarse arrival horizon).time path).val = time
    at occurs ⊢
  cases time with
  | zero =>
    by_cases startsCoarse : path 0 ∈ coarse
    · simp [coarseArrivalState, startsCoarse]
    · simp only [coarseArrivalState, if_neg startsCoarse] at occurs
      omega
  | succ time =>
    have before : time < ((boundedCoarseArrival coarse arrival horizon).time path).val := by omega
    have previous := boundedCoarseArrival_before coarse arrival horizon path before
    exact coarseArrivalState_increase coarse path time (by omega)

theorem coarseArrivalState_count_step (coarse : Finset X) (path : ℕ → X) (time : ℕ) :
    (coarseArrivalState coarse path time).2 ≤ (coarseArrivalState coarse path (time + 1)).2 ∧
      (coarseArrivalState coarse path (time + 1)).2 ≤ (coarseArrivalState coarse path time).2 + 1 := by
  by_cases arrives : path (time + 1) ∈ coarse ∧
      (coarseArrivalState coarse path time).1 ≠ some (path (time + 1))
  · simp only [coarseArrivalState, coarseArrivalUpdate, if_pos arrives]
    omega
  · simp only [coarseArrivalState, coarseArrivalUpdate, if_neg arrives]
    omega

theorem coarseArrivalState_count_monotone (coarse : Finset X) (path : ℕ → X) :
    Monotone (fun time => (coarseArrivalState coarse path time).2) := by
  exact monotone_nat_of_le_succ (fun time => (coarseArrivalState_count_step coarse path time).1)

theorem coarseArrivalState_current_coarse (coarse : Finset X) (path : ℕ → X) (time : ℕ)
    (belongs : path time ∈ coarse) :
    (coarseArrivalState coarse path time).1 = some (path time) := by
  cases time with
  | zero => simp only [coarseArrivalState, if_pos belongs]
  | succ time =>
    by_cases arrives : path (time + 1) ∈ coarse ∧
        (coarseArrivalState coarse path time).1 ≠ some (path (time + 1))
    · simp only [coarseArrivalState, coarseArrivalUpdate, if_pos arrives]
    · have same : (coarseArrivalState coarse path time).1 = some (path (time + 1)) := by
        by_contra different
        exact arrives ⟨belongs, different⟩
      simpa only [coarseArrivalState, coarseArrivalUpdate, if_neg arrives] using same

theorem coarseArrivalState_same_count (coarse : Finset X) (path : ℕ → X)
    {first last : ℕ} (ordered : first ≤ last)
    (sameCount : (coarseArrivalState coarse path first).2 = (coarseArrivalState coarse path last).2) :
    coarseArrivalState coarse path first = coarseArrivalState coarse path last := by
  revert sameCount
  induction last, ordered using Nat.le_induction with
  | base => intro _; rfl
  | succ last ordered inductionHypothesis =>
    intro sameCount
    have firstToLast := coarseArrivalState_count_monotone coarse path ordered
    dsimp only at firstToLast
    have lastToNext := (coarseArrivalState_count_step coarse path last).1
    have previousCount : (coarseArrivalState coarse path first).2 =
        (coarseArrivalState coarse path last).2 := by omega
    have previousState := inductionHypothesis previousCount
    by_cases arrives : path (last + 1) ∈ coarse ∧
        (coarseArrivalState coarse path last).1 ≠ some (path (last + 1))
    · simp only [coarseArrivalState, coarseArrivalUpdate, if_pos arrives] at sameCount
      omega
    · simpa only [coarseArrivalState, coarseArrivalUpdate, if_neg arrives] using previousState

theorem coarseArrivalState_none_iff_count_zero (coarse : Finset X) (path : ℕ → X) (time : ℕ) :
    (coarseArrivalState coarse path time).1 = none ↔ (coarseArrivalState coarse path time).2 = 0 := by
  induction time with
  | zero =>
    by_cases startsCoarse : path 0 ∈ coarse <;> simp [coarseArrivalState, startsCoarse]
  | succ time inductionHypothesis =>
    by_cases arrives : path (time + 1) ∈ coarse ∧
        (coarseArrivalState coarse path time).1 ≠ some (path (time + 1))
    · simp [coarseArrivalState, coarseArrivalUpdate, arrives]
    · simpa only [coarseArrivalState, coarseArrivalUpdate, if_neg arrives] using inductionHypothesis

theorem boundedCoarseArrival_first_avoid (coarse : Finset X) (horizon : ℕ)
    (path : ℕ → X) {time : ℕ}
    (before : time < ((boundedCoarseArrival coarse 0 horizon).time path).val) :
    path time ∉ coarse := by
  intro belongs
  have count := boundedCoarseArrival_before coarse 0 horizon path before
  have zero : (coarseArrivalState coarse path time).2 = 0 := by omega
  have none := (coarseArrivalState_none_iff_count_zero coarse path time).mpr zero
  rw [coarseArrivalState_current_coarse coarse path time belongs] at none
  cases none

theorem boundedCoarseArrival_count_eq (coarse : Finset X) (arrival horizon : ℕ)
    (path : ℕ → X)
    (beforeCap : ((boundedCoarseArrival coarse arrival horizon).time path).val < horizon) :
    (coarseArrivalState coarse path
      ((boundedCoarseArrival coarse arrival horizon).time path).val).2 = arrival + 1 := by
  have occurs := boundedCoarseArrival_occurs coarse arrival horizon path beforeCap
  generalize timeEquality : ((boundedCoarseArrival coarse arrival horizon).time path).val = time
    at occurs ⊢
  cases time with
  | zero =>
    by_cases startsCoarse : path 0 ∈ coarse
    · simp only [coarseArrivalState, if_pos startsCoarse] at occurs ⊢
      omega
    · simp only [coarseArrivalState, if_neg startsCoarse] at occurs
      omega
  | succ time =>
    have before : time < ((boundedCoarseArrival coarse arrival horizon).time path).val := by omega
    have previous := boundedCoarseArrival_before coarse arrival horizon path before
    have step := (coarseArrivalState_count_step coarse path time).2
    omega

theorem boundedCoarseArrival_le_of_count (coarse : Finset X) (arrival horizon time : ℕ)
    (path : ℕ → X) (occurs : arrival + 1 ≤ (coarseArrivalState coarse path time).2) :
    ((boundedCoarseArrival coarse arrival horizon).time path).val ≤ time := by
  apply cappedHitIndex_le_of_occurs
  dsimp only
  rwa [coarseArrivalHistory_restrict]

theorem boundedCoarseArrival_monotone (coarse : Finset X) (horizon : ℕ) (path : ℕ → X) :
    Monotone (fun arrival => ((boundedCoarseArrival coarse arrival horizon).time path).val) := by
  intro first last ordered
  dsimp only
  by_cases beforeCap : ((boundedCoarseArrival coarse last horizon).time path).val < horizon
  · apply boundedCoarseArrival_le_of_count
    have occurs := boundedCoarseArrival_occurs coarse last horizon path beforeCap
    omega
  · have lastCap : ((boundedCoarseArrival coarse last horizon).time path).val = horizon := by
      have bounded := ((boundedCoarseArrival coarse last horizon).time path).isLt
      omega
    rw [lastCap]
    exact Nat.le_of_lt_succ ((boundedCoarseArrival coarse first horizon).time path).isLt

theorem boundedCoarseArrival_le_iff (coarse : Finset X) (arrival horizon time : ℕ)
    (beforeCap : time < horizon) (path : ℕ → X) :
    ((boundedCoarseArrival coarse arrival horizon).time path).val ≤ time ↔
      arrival + 1 ≤ (coarseArrivalState coarse path time).2 := by
  constructor
  · intro bounded
    have occurs := boundedCoarseArrival_occurs coarse arrival horizon path
      (lt_of_le_of_lt bounded beforeCap)
    exact occurs.trans (coarseArrivalState_count_monotone coarse path bounded)
  · exact boundedCoarseArrival_le_of_count coarse arrival horizon time path

/-- Changing the cap cannot change a hit already completed strictly before
both caps. This permits finite-horizon Laplace arguments without assuming that
the corresponding unbounded hitting time is finite. -/
theorem boundedCoarseArrival_cap_consistent (coarse : Finset X) (arrival firstCap lastCap : ℕ)
    (path : ℕ → X)
    (firstBeforeCap : ((boundedCoarseArrival coarse arrival firstCap).time path).val < firstCap)
    (beforeLastCap : ((boundedCoarseArrival coarse arrival firstCap).time path).val < lastCap) :
    ((boundedCoarseArrival coarse arrival lastCap).time path).val =
      ((boundedCoarseArrival coarse arrival firstCap).time path).val := by
  have firstOccurs := boundedCoarseArrival_occurs coarse arrival firstCap path firstBeforeCap
  have lastLeFirst := boundedCoarseArrival_le_of_count coarse arrival lastCap _ path firstOccurs
  have lastOccurs := boundedCoarseArrival_occurs coarse arrival lastCap path
    (lt_of_le_of_lt lastLeFirst beforeLastCap)
  exact Nat.le_antisymm lastLeFirst
    (boundedCoarseArrival_le_of_count coarse arrival firstCap _ path lastOccurs)

/-- Before the cap, successive scanner stopping times are precisely successive
hits on a coarse point distinct from the previous stopped coarse point. Every
intermediate coarse observation is the previous center, including returns. -/
theorem boundedCoarseArrival_next_distinct (coarse : Finset X) (arrival horizon : ℕ)
    (path : ℕ → X)
    (nextBeforeCap : ((boundedCoarseArrival coarse (arrival + 1) horizon).time path).val < horizon) :
    ((boundedCoarseArrival coarse arrival horizon).time path).val <
        ((boundedCoarseArrival coarse (arrival + 1) horizon).time path).val ∧
      path ((boundedCoarseArrival coarse (arrival + 1) horizon).time path).val ∈ coarse ∧
      path ((boundedCoarseArrival coarse (arrival + 1) horizon).time path).val ≠
        path ((boundedCoarseArrival coarse arrival horizon).time path).val ∧
      ∀ time, ((boundedCoarseArrival coarse arrival horizon).time path).val ≤ time →
        time < ((boundedCoarseArrival coarse (arrival + 1) horizon).time path).val →
        path time ∈ coarse →
          path time = path ((boundedCoarseArrival coarse arrival horizon).time path).val := by
  have ordered := boundedCoarseArrival_monotone coarse horizon path (Nat.le_succ arrival)
  dsimp only at ordered
  simp only [Nat.succ_eq_add_one] at ordered
  have firstBeforeCap : ((boundedCoarseArrival coarse arrival horizon).time path).val < horizon :=
    lt_of_le_of_lt ordered nextBeforeCap
  have firstCount := boundedCoarseArrival_count_eq coarse arrival horizon path firstBeforeCap
  have nextCount := boundedCoarseArrival_count_eq coarse (arrival + 1) horizon path nextBeforeCap
  have strict : ((boundedCoarseArrival coarse arrival horizon).time path).val <
      ((boundedCoarseArrival coarse (arrival + 1) horizon).time path).val := by
    by_contra notStrict
    have equal : ((boundedCoarseArrival coarse arrival horizon).time path).val =
        ((boundedCoarseArrival coarse (arrival + 1) horizon).time path).val := by omega
    rw [equal] at firstCount
    omega
  have nextCoarse := (boundedCoarseArrival_is_coarse coarse (arrival + 1) horizon path nextBeforeCap).1
  have firstState := (boundedCoarseArrival_is_coarse coarse arrival horizon path firstBeforeCap).2
  have intermediate : ∀ time,
      ((boundedCoarseArrival coarse arrival horizon).time path).val ≤ time →
      time < ((boundedCoarseArrival coarse (arrival + 1) horizon).time path).val →
      coarseArrivalState coarse path time = coarseArrivalState coarse path
        ((boundedCoarseArrival coarse arrival horizon).time path).val := by
    intro time afterFirst beforeNext
    apply (coarseArrivalState_same_count coarse path afterFirst ?_).symm
    have lower := coarseArrivalState_count_monotone coarse path afterFirst
    dsimp only at lower
    have upper := boundedCoarseArrival_before coarse (arrival + 1) horizon path beforeNext
    omega
  refine ⟨strict, nextCoarse, ?_, ?_⟩
  · intro equalPoints
    generalize nextTimeEquality : ((boundedCoarseArrival coarse (arrival + 1) horizon).time path).val = nextTime
      at nextCount nextCoarse equalPoints
    cases nextTime with
    | zero => omega
    | succ time =>
      have afterFirst : ((boundedCoarseArrival coarse arrival horizon).time path).val ≤ time := by omega
      have beforeNext : time < ((boundedCoarseArrival coarse (arrival + 1) horizon).time path).val := by omega
      have previousState := intermediate time afterFirst beforeNext
      have lastState : (coarseArrivalState coarse path time).1 = some (path (time + 1)) := by
        rw [previousState, firstState, equalPoints]
      have noArrival : ¬(path (time + 1) ∈ coarse ∧
          (coarseArrivalState coarse path time).1 ≠ some (path (time + 1))) := by
        exact fun contradiction => contradiction.2 lastState
      simp only [coarseArrivalState, coarseArrivalUpdate, if_neg noArrival] at nextCount
      have previousCount := congrArg Prod.snd previousState
      omega
  · intro time afterFirst beforeNext belongs
    have current := coarseArrivalState_current_coarse coarse path time belongs
    rw [intermediate time afterFirst beforeNext, firstState] at current
    exact (Option.some.inj current).symm

end

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.cappedHitIndex_eq_iff
#print axioms IGS.Sec31.DiscreteMarkov.cappedHitIndex_before
#print axioms IGS.Sec31.DiscreteMarkov.coarseArrivalHistory_restrict
#print axioms IGS.Sec31.DiscreteMarkov.boundedCoarseArrival_before
#print axioms IGS.Sec31.DiscreteMarkov.boundedCoarseArrival_occurs
#print axioms IGS.Sec31.DiscreteMarkov.boundedCoarseArrival_is_coarse
#print axioms IGS.Sec31.DiscreteMarkov.boundedCoarseArrival_count_eq
#print axioms IGS.Sec31.DiscreteMarkov.boundedCoarseArrival_next_distinct
#print axioms IGS.Sec31.DiscreteMarkov.boundedCoarseArrival_first_avoid
#print axioms IGS.Sec31.DiscreteMarkov.boundedCoarseArrival_cap_consistent
