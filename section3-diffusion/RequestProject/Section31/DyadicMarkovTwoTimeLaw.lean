import RequestProject.Section31.EIGSDyadicMarkovProcessOfRules

/-! Actual two-time joint laws of the constructed dyadic total process.
The proof projects the already proved full-history/block-endpoint law and
the actual complete dyadic prefix laws. No two-time-law premise is assumed.
Stationarity is supplied by genuine kernel invariance. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Preorder
open scoped ProbabilityTheory NNRat
set_option maxHeartbeats 3000000

variable {X : Type*} [MeasurableSpace X]

theorem pathLaw_coordinate_pair (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : Measure X) [SFinite initial] (start offset : ℕ) :
    (pathLaw kernel initial).map (fun path => (path start, path (start + offset))) =
      (pathLaw kernel initial).map (fun path => path start) ⊗ₘ (kernel ^ offset) := by
  haveI : SFinite (pathLaw kernel initial) := by
    unfold pathLaw
    infer_instance
  have factor : (fun path : ℕ → X => (path start, path (start + offset))) =
      (Prod.map (fun history : Finset.Iic start → X =>
        history ⟨start, Finset.mem_Iic.mpr le_rfl⟩) id) ∘
      (fun path => (frestrictLe start path, path (start + offset))) := rfl
  rw [factor, ← Measure.map_map
      (f := fun path : ℕ → X => (frestrictLe (π := fun _ : ℕ => X) start path, path (start + offset)))
      (g := Prod.map (fun history : Finset.Iic start → X =>
        history ⟨start, Finset.mem_Iic.mpr le_rfl⟩) (id : X → X))
      ((measurable_pi_apply _).prodMap measurable_id)
      ((measurable_frestrictLe start).prodMk (measurable_pi_apply _)),
    pathLaw_history_endpoint_joint, compProd_map_left_comap,
    Measure.map_map (f := frestrictLe (π := fun _ : ℕ => X) start)
      (g := fun history : Finset.Iic start → X => history ⟨start, Finset.mem_Iic.mpr le_rfl⟩)
      (measurable_pi_apply _) (measurable_frestrictLe start)]
  rfl

theorem pathLaw_stationary_coordinate_pair (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : Measure X) [SFinite initial] (invariant : kernel.Invariant initial)
    (start offset : ℕ) :
    (pathLaw kernel initial).map (fun path => (path start, path (start + offset))) =
      initial ⊗ₘ (kernel ^ offset) := by
  rw [pathLaw_coordinate_pair, pathLaw_coordinate_stationary kernel initial invariant]

theorem rationalSkeletonLaw_stationary_pair (family : ℚ≥0 → Kernel X X)
    (markov : ∀ time, IsMarkovKernel (family time)) (initial : Measure X) [SFinite initial]
    (invariant : ∀ time, (family time).Invariant initial)
    (zeroLaw : family 0 = Kernel.id)
    (addLaw : ∀ firstTime secondTime,
      family secondTime ∘ₖ family firstTime = family (firstTime + secondTime))
    (step : ℚ≥0) (start offset : ℕ) :
    (rationalSkeletonLaw family markov step initial).map
        (fun path => (path start, path (start + offset))) = initial ⊗ₘ family (offset • step) := by
  letI : IsMarkovKernel (family step) := markov step
  change (pathLaw (family step) initial).map _ = _
  rw [pathLaw_stationary_coordinate_pair (family step) initial (invariant step),
    kernel_pow_fixed_step family zeroLaw addLaw]

variable [StandardBorelSpace X] [Nonempty X]

theorem dyadicPathLaw_ordered_pair (family : ℚ≥0 → Kernel X X)
    (markov : ∀ time, IsMarkovKernel (family time)) (initial : Measure X)
    [IsProbabilityMeasure initial] (invariant : ∀ time, (family time).Invariant initial)
    (zeroLaw : family 0 = Kernel.id)
    (addLaw : ∀ firstTime secondTime,
      family secondTime ∘ₖ family firstTime = family (firstTime + secondTime))
    (firstTime secondTime : DyadicTime) (ordered : firstTime.val ≤ secondTime.val) :
    (dyadicPathLaw family markov initial).map
      (fun path => (path firstTime, path secondTime)) = initial ⊗ₘ family (secondTime.val - firstTime.val) := by
  let count := max (dyadicEnumeration.symm firstTime) (dyadicEnumeration.symm secondTime)
  let firstIndex : Finset.Iic count :=
    ⟨dyadicEnumeration.symm firstTime, Finset.mem_Iic.mpr (le_max_left _ _)⟩
  let secondIndex : Finset.Iic count :=
    ⟨dyadicEnumeration.symm secondTime, Finset.mem_Iic.mpr (le_max_right _ _)⟩
  let levels := fun index => dyadicTimeLevel (dyadicEnumeration index)
  let indices := fun index => dyadicTimeIndex (dyadicEnumeration index)
  let step := dyadicStep (prefixGridLevel levels count)
  let firstGridIndex := prefixGridIndex levels indices count firstIndex
  let secondGridIndex := prefixGridIndex levels indices count secondIndex
  have firstIdentity : firstGridIndex • step = firstTime.val := by
    dsimp only [firstGridIndex, step, levels, indices]
    rw [prefixGridIndex_time, ← dyadicTime_representation]
    change (dyadicEnumeration (dyadicEnumeration.symm firstTime)).val = firstTime.val
    rw [Equiv.apply_symm_apply]
  have secondIdentity : secondGridIndex • step = secondTime.val := by
    dsimp only [secondGridIndex, step, levels, indices]
    rw [prefixGridIndex_time, ← dyadicTime_representation]
    change (dyadicEnumeration (dyadicEnumeration.symm secondTime)).val = secondTime.val
    rw [Equiv.apply_symm_apply]
  have stepPositive : 0 < step := by
    dsimp only [step, dyadicStep]
    positivity
  have gridOrdered : firstGridIndex ≤ secondGridIndex := by
    by_contra contrary
    have strict : secondGridIndex • step < firstGridIndex • step :=
      nsmul_lt_nsmul_left stepPositive (Nat.lt_of_not_ge contrary)
    rw [firstIdentity, secondIdentity] at strict
    exact (not_lt_of_ge ordered) strict
  have gapIdentity : (secondGridIndex - firstGridIndex) • step = secondTime.val - firstTime.val := by
    apply (eq_tsub_iff_add_eq_of_le ordered).mpr
    rw [← firstIdentity, ← add_nsmul, Nat.sub_add_cancel gridOrdered, secondIdentity]
  have measurable : Measurable
      (fun path : DyadicTime → X => fun index : Finset.Iic count =>
        path (dyadicEnumeration index.val)) := by
    apply measurable_pi_lambda
    intro index
    exact measurable_pi_apply _
  calc
    (dyadicPathLaw family markov initial).map
        (fun path => (path firstTime, path secondTime)) =
        ((dyadicPathLaw family markov initial).map
          (fun path (index : Finset.Iic count) => path (dyadicEnumeration index.val))).map
            (fun history => (history firstIndex, history secondIndex)) := by
      rw [Measure.map_map ((measurable_pi_apply _).prodMk (measurable_pi_apply _)) measurable]
      congr 1
      funext path
      change (path firstTime, path secondTime) =
        (path (dyadicEnumeration (dyadicEnumeration.symm firstTime)),
          path (dyadicEnumeration (dyadicEnumeration.symm secondTime)))
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    _ = (dyadicPrefixLaws family markov initial levels indices count).map
          (fun history => (history firstIndex, history secondIndex)) := by
      rw [dyadicPathLaw_enumerated_prefix family markov initial zeroLaw addLaw]
    _ = (rationalSkeletonLaw family markov step initial).map
          (fun path => (path firstGridIndex, path secondGridIndex)) := by
      unfold dyadicPrefixLaws
      rw [Measure.map_map ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
        (dyadicPrefix_measurable _ _ _)]
      rfl
    _ = initial ⊗ₘ family ((secondGridIndex - firstGridIndex) • step) := by
      have endpoint : firstGridIndex + (secondGridIndex - firstGridIndex) = secondGridIndex :=
        Nat.add_sub_of_le gridOrdered
      simpa only [endpoint] using rationalSkeletonLaw_stationary_pair family markov initial
        invariant zeroLaw addLaw step firstGridIndex (secondGridIndex - firstGridIndex)
    _ = initial ⊗ₘ family (secondTime.val - firstTime.val) := by rw [gapIdentity]

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.pathLaw_coordinate_pair
#print axioms IGS.Sec31.DiscreteMarkov.rationalSkeletonLaw_stationary_pair
#print axioms IGS.Sec31.DiscreteMarkov.dyadicPathLaw_ordered_pair
