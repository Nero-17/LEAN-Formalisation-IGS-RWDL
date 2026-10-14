import RequestProject.Section31.J1FiniteJumpFunctions
import RequestProject.Section31.J1UnitGridReconstruction

/-! Deterministic fixed-grid approximation of finitely jumping paths in
the genuine time-change J1 distance. Endpoint jumps are retained exactly. -/

namespace IGS.Sec31.DiscreteMarkov
open Filter Set Topology
open scoped NNReal
noncomputable section
set_option maxHeartbeats 5000000

def unitGridPoint (grid : ℕ) (index : Fin (grid + 2)) : UnitJ1Time :=
  ⟨(index.val : ℝ) / (grid + 1 : ℝ), by
    have denominator : 0 < (grid + 1 : ℝ) := by positivity
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) denominator.le
    · apply (div_le_one denominator).mpr
      exact_mod_cast Nat.le_of_lt_succ index.isLt⟩

def unitGridFunctionReconstruction {State : Type*} (grid : ℕ)
    (values : Fin (grid + 2) → State) (time : UnitJ1Time) : State := values (unitGridIndex grid time)

theorem unitGridMesh_tendsto :
    Tendsto (fun grid : ℕ => 1 / (grid + 1 : ℝ)) atTop (𝓝 0) := by
  simpa only [Nat.cast_add, Nat.cast_one] using tendsto_one_div_add_atTop_nhds_zero_nat

variable {Space : Type*} [MetricSpace Space]

def roundedIntervalKnot (grid : ℕ) (time : UnitJ1Time) :
    UnitJ1Time :=
  ⟨(⌈(grid+1 : ℝ) * (time : ℝ)⌉₊ : ℝ) / (grid+1 : ℝ), by
    have positive : 0 < (grid+1 : ℝ) := by positivity
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) positive.le
    · apply (div_le_one positive).mpr
      have bound : ⌈(grid+1 : ℝ) * (time : ℝ)⌉₊ ≤ grid+1 := Nat.ceil_le.mpr (by
        simpa only [Nat.cast_add, Nat.cast_one, mul_one] using
          mul_le_mul_of_nonneg_left time.property.2 positive.le)
      exact_mod_cast bound⟩

theorem roundedIntervalKnot_distance (grid : ℕ)
    (time : UnitJ1Time) :
    dist (roundedIntervalKnot grid time) time ≤ 1 / (grid+1 : ℝ) := by
  have positive : 0 < (grid+1 : ℝ) := by positivity
  have lower := Nat.le_ceil ((grid+1 : ℝ) * (time : ℝ))
  have upper := Nat.ceil_lt_add_one (mul_nonneg positive.le time.property.1)
  change |(⌈(grid+1 : ℝ) * (time : ℝ)⌉₊ : ℝ) / (grid+1 : ℝ) - (time : ℝ)| ≤ _
  have quotientLower : (time : ℝ) ≤ (⌈(grid+1 : ℝ) * (time : ℝ)⌉₊ : ℝ) / (grid+1 : ℝ) :=
    (le_div_iff₀ positive).mpr (by simpa only [mul_comm] using lower)
  rw [abs_of_nonneg (sub_nonneg.mpr quotientLower)]
  apply (le_div_iff₀ positive).mpr
  rw [sub_mul, div_mul_cancel₀ _ positive.ne']
  nlinarith

theorem roundedIntervalKnot_tendsto
    (time : UnitJ1Time) :
    Tendsto (fun grid => roundedIntervalKnot grid time) atTop (𝓝 time) := by
  apply Metric.tendsto_nhds.mpr
  intro tolerance positive
  filter_upwards [unitGridMesh_tendsto.eventually (gt_mem_nhds positive)] with grid small
  exact (roundedIntervalKnot_distance grid time).trans_lt small

theorem roundedIntervalKnot_grid_inequality (grid : ℕ)
    (knot time : UnitJ1Time) :
    knot ≤ unitGridPoint grid (unitGridIndex grid time) ↔
      roundedIntervalKnot grid knot ≤ time := by
  have positive : 0 < (grid+1 : ℝ) := by positivity
  change (knot : ℝ) ≤ (⌊(grid+1 : ℝ) * (time : ℝ)⌋₊ : ℝ) / (grid+1 : ℝ) ↔
    (⌈(grid+1 : ℝ) * (knot : ℝ)⌉₊ : ℝ) / (grid+1 : ℝ) ≤ (time : ℝ)
  rw [le_div_iff₀ positive, div_le_iff₀ positive]
  rw [mul_comm (knot : ℝ), ← Nat.ceil_le,
    mul_comm (time : ℝ), ← Nat.le_floor_iff (mul_nonneg positive.le time.property.1)]

theorem finiteEndpointJump_grid_identity {count : ℕ}
    (knots : Fin count → UnitJ1Time)
    (states : Fin (count+1) → Space) (endpoint : Space) (grid : ℕ) :
    unitGridFunctionReconstruction grid
      (fun index => finiteEndpointJumpFunction knots states endpoint
        (unitGridPoint grid index)) =
      finiteEndpointJumpFunction (fun index => roundedIntervalKnot grid (knots index)) states endpoint := by
  classical
  funext time
  by_cases terminal : time.val = 1
  · have gridTerminal : (unitGridPoint grid
        (unitGridIndex grid time)).val = 1 := by
      change (⌊(grid+1 : ℝ) * (time : ℝ)⌋₊ : ℝ) / (grid+1 : ℝ) = 1
      rw [terminal, mul_one]
      have floorIdentity : ⌊(grid+1 : ℝ)⌋₊ = grid+1 := by
        simpa only [Nat.cast_add, Nat.cast_one] using Nat.floor_natCast (R := ℝ) (grid+1)
      rw [floorIdentity]
      push_cast
      exact div_self (by positivity)
    simp only [unitGridFunctionReconstruction,
      finiteEndpointJumpFunction, terminal, gridTerminal, if_true]
  · have gridNotTerminal : (unitGridPoint grid
        (unitGridIndex grid time)).val ≠ 1 := by
      have bound := Nat.floor_le (mul_nonneg (by positivity : 0 ≤ (grid+1 : ℝ)) time.property.1)
      have quotientBound : (unitGridPoint grid
          (unitGridIndex grid time)).val ≤ time.val := by
        change (⌊(grid+1 : ℝ) * (time : ℝ)⌋₊ : ℝ) / (grid+1 : ℝ) ≤ (time : ℝ)
        apply (div_le_iff₀ (by positivity : 0 < (grid+1 : ℝ))).mpr
        simpa only [mul_comm] using bound
      exact ne_of_lt (quotientBound.trans_lt (lt_of_le_of_ne time.property.2 terminal))
    simp only [unitGridFunctionReconstruction,
      finiteEndpointJumpFunction, terminal, gridNotTerminal, if_false]
    change states _ = states _
    congr 1
    apply Fin.ext
    unfold finiteJumpCount
    change (Finset.univ.filter (fun index => knots index ≤ unitGridPoint grid
      (unitGridIndex grid time))).card =
        (Finset.univ.filter (fun index => roundedIntervalKnot grid (knots index) ≤ time)).card
    apply congrArg Finset.card
    apply Finset.ext
    intro index
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact roundedIntervalKnot_grid_inequality grid (knots index) time


