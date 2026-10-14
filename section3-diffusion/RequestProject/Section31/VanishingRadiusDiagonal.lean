import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

namespace IGS.Sec31.DiscreteMarkov
noncomputable section
open Filter
open scoped Topology

theorem exists_vanishing_positive_radii_of_eventual
    (acceptable : ℕ → ℝ → Prop)
    (eventual : ∀ radius : ℝ, 0 < radius → ∀ᶠ index in atTop, acceptable index radius) :
    ∃ radii : ℕ → ℝ, (∀ index, 0 < radii index) ∧ Tendsto radii atTop (𝓝 0) ∧
      ∃ threshold : ℕ, ∀ index ≥ threshold, acceptable index (radii index) := by
  classical
  have thresholds : ∀ scale : ℕ, ∃ threshold : ℕ, ∀ index ≥ threshold,
      acceptable index (1 / (scale + 1 : ℝ)) := by
    intro scale
    exact eventually_atTop.mp (eventual _ (by positivity))
  choose threshold good using thresholds
  let eligible := fun index => (Finset.range (index + 1)).filter (fun scale => threshold scale ≤ index)
  let selected := fun index => (eligible index).sup id
  have selectedDiverges : Tendsto selected atTop atTop := by
    apply tendsto_atTop.mpr
    intro scale
    filter_upwards [eventually_ge_atTop (max scale (threshold scale))] with index large
    have membership : scale ∈ eligible index :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ((le_max_left _ _).trans large)),
        (le_max_right _ _).trans large⟩
    change scale ≤ (eligible index).sup (fun value : ℕ => value)
    exact Finset.le_sup (f := fun value : ℕ => value) membership
  refine ⟨fun index => 1 / (selected index + 1 : ℝ), fun _ => by positivity,
    tendsto_one_div_add_atTop_nhds_zero_nat.comp selectedDiverges, threshold 0, ?_⟩
  intro index large
  have nonempty : (eligible index).Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.zero_lt_succ index), large⟩⟩
  have selectedMembership : selected index ∈ eligible index := by
    obtain ⟨scale, membership, equality⟩ := Finset.sup_mem_of_nonempty (f := id) nonempty
    change (eligible index).sup id ∈ eligible index
    rw [← equality]
    exact membership
  exact good (selected index) index (Finset.mem_filter.mp selectedMembership).2

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.exists_vanishing_positive_radii_of_eventual
