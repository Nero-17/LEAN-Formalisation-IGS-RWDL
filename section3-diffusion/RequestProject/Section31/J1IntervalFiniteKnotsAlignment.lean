import RequestProject.Section31.J1IntervalOneKnotAlignment

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace IGS.Sec31.DiscreteMarkov
noncomputable section
open Set
open scoped _root_.Topology

theorem intervalOrderIso_one_fixed
    (change : UnitJ1Time ≃o UnitJ1Time) :
    change (⟨1, by norm_num⟩ : UnitJ1Time) = (⟨1, by norm_num⟩ : UnitJ1Time) := by
  apply Subtype.ext
  apply le_antisymm (change _).property.2
  have increasing := change.monotone (show change.symm (⟨1, by norm_num⟩ : UnitJ1Time) ≤
      (⟨1, by norm_num⟩ : UnitJ1Time) from (change.symm (⟨1, by norm_num⟩ : UnitJ1Time)).property.2)
  rw [change.apply_symm_apply] at increasing
  exact increasing

theorem intervalOrderIso_zero_fixed
    (change : UnitJ1Time ≃o UnitJ1Time) :
    change (⟨0, by norm_num⟩ : UnitJ1Time) = (⟨0, by norm_num⟩ : UnitJ1Time) := by
  apply Subtype.ext
  apply le_antisymm _ (change _).property.1
  have increasing := change.monotone (show (⟨0, by norm_num⟩ : UnitJ1Time) ≤
      change.symm (⟨0, by norm_num⟩ : UnitJ1Time) from (change.symm (⟨0, by norm_num⟩ : UnitJ1Time)).property.1)
  rw [change.apply_symm_apply] at increasing
  exact increasing

theorem interval_finite_knots_orderIso
    (count : ℕ) (first second : Fin count → UnitJ1Time)
    (firstIncreasing : StrictMono first) (secondIncreasing : StrictMono second)
    (firstInterior : ∀ index, 0 < (first index).val ∧ (first index).val < 1)
    (secondInterior : ∀ index, 0 < (second index).val ∧ (second index).val < 1)
    (tolerance : ℝ) (close : ∀ index, dist (first index) (second index) ≤ tolerance) :
    ∃ change : UnitJ1Time ≃o UnitJ1Time,
      (∀ index, change (first index) = second index) ∧
      ∀ point, dist (change point) point ≤ ((2 : ℝ)^count - 1) * tolerance := by
  induction count with
  | zero =>
    refine ⟨OrderIso.refl _, fun index => Fin.elim0 index, ?_⟩
    intro point
    simp
  | succ count inductionHypothesis =>
    let firstOld : Fin count → UnitJ1Time := fun index => first index.castSucc
    let secondOld : Fin count → UnitJ1Time := fun index => second index.castSucc
    have firstOldIncreasing : StrictMono firstOld := firstIncreasing.comp Fin.strictMono_castSucc
    have secondOldIncreasing : StrictMono secondOld := secondIncreasing.comp Fin.strictMono_castSucc
    obtain ⟨previous, previousKnots, previousDisplacement⟩ := inductionHypothesis firstOld secondOld firstOldIncreasing secondOldIncreasing
      (fun index => firstInterior index.castSucc) (fun index => secondInterior index.castSucc) (fun index => close index.castSucc)
    let currentFirst := previous (first (Fin.last count))
    let currentSecond := second (Fin.last count)
    have currentFirstInterior : currentFirst.val < 1 := by
      have increasing := previous.strictMono (show first (Fin.last count) < (⟨1, by norm_num⟩ : UnitJ1Time) from (firstInterior (Fin.last count)).2)
      rw [intervalOrderIso_one_fixed] at increasing
      exact increasing
    have currentSecondInterior : currentSecond.val < 1 := (secondInterior (Fin.last count)).2
    obtain ⟨pivot, pivotBeforeFirst, pivotBeforeSecond, oldBelowPivot⟩ :
        ∃ pivot : UnitJ1Time, pivot < currentFirst ∧ pivot < currentSecond ∧
          ∀ index : Fin count, secondOld index ≤ pivot := by
      by_cases empty : count = 0
      · subst count
        refine ⟨⟨0, by norm_num⟩, ?_, (secondInterior (Fin.last 0)).1, fun index => Fin.elim0 index⟩
        have increasing := previous.strictMono (show (⟨0, by norm_num⟩ : UnitJ1Time) < first (Fin.last 0) from (firstInterior (Fin.last 0)).1)
        rw [intervalOrderIso_zero_fixed] at increasing
        exact increasing
      · let lastOld : Fin count := ⟨count - 1, by omega⟩
        refine ⟨secondOld lastOld, ?_, ?_, ?_⟩
        · rw [← previousKnots lastOld]
          apply previous.strictMono
          exact firstIncreasing (by exact Fin.castSucc_lt_last lastOld)
        · exact secondIncreasing (Fin.castSucc_lt_last lastOld)
        · intro index
          apply secondOldIncreasing.monotone
          change index.val ≤ count - 1
          omega
    obtain ⟨lastMove, lastKnot, previousFixed, lastDisplacement⟩ := interval_single_knot_orderIso
      pivot currentFirst currentSecond pivotBeforeFirst pivotBeforeSecond currentFirstInterior currentSecondInterior
    refine ⟨previous.trans lastMove, ?_, ?_⟩
    · intro index
      refine Fin.lastCases ?_ (fun oldIndex => ?_) index
      · exact lastKnot
      · change lastMove (previous (firstOld oldIndex)) = secondOld oldIndex
        rw [previousKnots oldIndex]
        exact previousFixed _ (oldBelowPivot oldIndex)
    · intro point
      have lastDistance : dist currentFirst currentSecond ≤ ((2 : ℝ)^count - 1) * tolerance + tolerance :=
        (dist_triangle currentFirst (first (Fin.last count)) currentSecond).trans
          (add_le_add (previousDisplacement (first (Fin.last count))) (close (Fin.last count)))
      calc
        dist ((previous.trans lastMove) point) point ≤ dist (lastMove (previous point)) (previous point) + dist (previous point) point := dist_triangle _ _ _
        _ ≤ dist currentFirst currentSecond + ((2 : ℝ)^count - 1) * tolerance :=
          add_le_add (lastDisplacement (previous point)) (previousDisplacement point)
        _ ≤ (((2 : ℝ)^count - 1) * tolerance + tolerance) + ((2 : ℝ)^count - 1) * tolerance :=
          add_le_add_left lastDistance _
        _ = ((2 : ℝ)^(count + 1) - 1) * tolerance := by rw [pow_succ]; ring

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.interval_finite_knots_orderIso

