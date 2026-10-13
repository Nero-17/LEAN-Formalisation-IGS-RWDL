import Mathlib.Data.Finset.Sort
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Arbitrary finite observation products can be regrouped on the ordered
finite set of their times together with zero. Tests at repeated times are
multiplied; the unobserved zero time has the empty product one. The proof is
pointwise, so it applies to genuine path-law integrals from any start. -/

namespace IGS.Sec31.FiniteObservationTimeReindexing

open MeasureTheory Filter Topology
open scoped BigOperators Classical NNReal
noncomputable section

theorem exists_monotone_zero_start_product_representation
    {Space : Type*} [TopologicalSpace Space] (dimension : ℕ)
    (times : Fin dimension → ℝ≥0) (tests : Fin dimension → C(Space, ℝ)) :
    ∃ count : ℕ, ∃ orderedTimes : ℕ → ℝ≥0,
      Monotone orderedTimes ∧ orderedTimes 0 = 0 ∧
      ∃ orderedTests : ℕ → C(Space, ℝ), ∃ terminal : C(Space, ℝ),
        ∀ path : ℝ≥0 → Space,
          (∏ index : Fin dimension, tests index (path (times index))) =
            (∏ index : Fin count, orderedTests index.val (path (orderedTimes index.val))) *
              terminal (path (orderedTimes count)) := by
  let timeSet : Finset ℝ≥0 := insert 0 (Finset.univ.image times)
  have zeroMembership : (0 : ℝ≥0) ∈ timeSet := Finset.mem_insert_self _ _
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
  refine ⟨count, orderedTimes, timesMonotone, startsAtZero, orderedTests, orderedTests count, ?_⟩
  intro path
  have mapsTo : ∀ index ∈ (Finset.univ : Finset (Fin dimension)), times index ∈ timeSet := by
    intro index _
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩)
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
  simpa only [Fin.prod_univ_castSucc, Fin.val_castSucc, Fin.val_last] using regrouped.symm

theorem arbitrary_products_have_limit_of_ordered_products
    {Space : Type*} [TopologicalSpace Space]
    {Sample : ℕ → Type*} [∀ level, MeasurableSpace (Sample level)]
    (laws : ∀ level, Measure (Sample level))
    (observation : ∀ level, ℝ≥0 → Sample level → Space)
    (orderedProducts : ∀ (times : ℕ → ℝ≥0), Monotone times → times 0 = 0 →
      ∀ (tests : ℕ → C(Space, ℝ)) (count : ℕ) (terminal : C(Space, ℝ)),
      ∃ value : ℝ, Tendsto (fun level => ∫ sample,
        (∏ index : Fin count, tests index.val (observation level (times index.val) sample)) *
          terminal (observation level (times count) sample) ∂laws level) atTop (𝓝 value))
    (dimension : ℕ) (times : Fin dimension → ℝ≥0) (tests : Fin dimension → C(Space, ℝ)) :
    ∃ value : ℝ, Tendsto (fun level => ∫ sample,
      ∏ index : Fin dimension, tests index (observation level (times index) sample) ∂laws level)
        atTop (𝓝 value) := by
  obtain ⟨count, orderedTimes, monotone, startsAtZero, orderedTests, terminal, representation⟩ :=
    exists_monotone_zero_start_product_representation dimension times tests
  obtain ⟨value, convergence⟩ := orderedProducts orderedTimes monotone startsAtZero orderedTests count terminal
  refine ⟨value, ?_⟩
  convert convergence using 1
  funext level
  apply integral_congr_ae
  exact Eventually.of_forall fun sample => representation (fun time => observation level time sample)

end
end IGS.Sec31.FiniteObservationTimeReindexing

#print axioms IGS.Sec31.FiniteObservationTimeReindexing.exists_monotone_zero_start_product_representation
#print axioms IGS.Sec31.FiniteObservationTimeReindexing.arbitrary_products_have_limit_of_ordered_products
