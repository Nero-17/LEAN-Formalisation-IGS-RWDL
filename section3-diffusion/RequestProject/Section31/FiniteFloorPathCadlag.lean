import RequestProject.Section31.UniformCadlagClosed
import RequestProject.Section31.FiniteHorizonMarkovStepPathLaw
import Mathlib.Topology.Algebra.Order.Floor

/-! Actual finite floor-clock paths have right continuity and genuine left
limits. The proof uses the eventual constant one-sided values of Int.floor;
no continuity of a discrete trajectory is assumed. -/

namespace IGS.Sec31.DiscreteMarkov

open Set Filter Topology
open scoped NNReal UniformConvergence
noncomputable section

variable {State : Type*} [MetricSpace State]

def realFloorClockPath (rate : ℝ≥0) (trajectory : ℕ → State) (time : ℝ) : State :=
  trajectory ⌊time * (rate : ℝ)⌋₊

theorem realFloorClockPath_isCadlag (rate : ℝ≥0) (trajectory : ℕ → State) :
    IsCadlagPath (realFloorClockPath rate trajectory) := by
  by_cases rateZero : rate = 0
  · have constantContinuous : Continuous (fun _ : ℝ => trajectory 0) := continuous_const
    have pathEquality : realFloorClockPath rate trajectory = fun _ : ℝ => trajectory 0 := by
      funext time
      simp only [realFloorClockPath, rateZero, NNReal.coe_zero, mul_zero, Nat.floor_zero]
    rw [pathEquality]
    exact IGS.Sec31.DiscreteMarkov.Continuous.isCadlagPath constantContinuous
  · have ratePositive : (0 : ℝ) < rate := by exact_mod_cast (pos_iff_ne_zero.mpr rateZero)
    have clockContinuous : Continuous (fun time : ℝ => time * (rate : ℝ)) :=
      continuous_id.mul continuous_const
    constructor
    · intro time
      have clockApproach : Tendsto (fun other : ℝ => other * (rate : ℝ))
          (𝓝[Ici time] time) (𝓝[Ici (time * (rate : ℝ))] (time * (rate : ℝ))) :=
        clockContinuous.continuousWithinAt.tendsto_nhdsWithin
          (fun _ membership => mul_le_mul_of_nonneg_right membership rate.property)
      have floorApproach :=
        (_root_.tendsto_floor_right_pure_floor (time * (rate : ℝ))).comp clockApproach
      have trajectoryApproach :=
        (tendsto_pure_pure (fun index : ℤ => trajectory index.toNat)
          ⌊time * (rate : ℝ)⌋).comp floorApproach
      simpa only [Function.comp_def, Int.floor_toNat, realFloorClockPath] using
        trajectoryApproach.mono_right (pure_le_nhds _)
    · intro time
      have clockApproach : Tendsto (fun other : ℝ => other * (rate : ℝ))
          (𝓝[Iio time] time) (𝓝[Iio (time * (rate : ℝ))] (time * (rate : ℝ))) :=
        clockContinuous.continuousWithinAt.tendsto_nhdsWithin
          (fun _ membership => mul_lt_mul_of_pos_right membership ratePositive)
      have floorApproach :=
        (_root_.tendsto_floor_left_pure_ceil_sub_one (time * (rate : ℝ))).comp clockApproach
      refine ⟨trajectory (⌈time * (rate : ℝ)⌉ - 1).toNat, ?_⟩
      have trajectoryApproach :=
        (tendsto_pure_pure (fun index : ℤ => trajectory index.toNat)
          (⌈time * (rate : ℝ)⌉ - 1)).comp floorApproach
      simpa only [Function.comp_def, Int.floor_toNat, realFloorClockPath] using
        trajectoryApproach.mono_right (pure_le_nhds _)

theorem intervalFloorClockPath_isCadlag (horizon rate : ℝ≥0) (trajectory : ℕ → State) :
    IsCadlagPath (fun time : Icc (0 : ℝ) (horizon : ℝ) =>
      trajectory ⌊time.val * (rate : ℝ)⌋₊) := by
  exact (realFloorClockPath_isCadlag rate trajectory).comp_continuous_strictMono
    Subtype.val continuous_subtype_val (fun _ _ ordered => ordered)

variable [CompactSpace State] [MeasurableSpace State] [BorelSpace State]
variable {Vertex : ℕ → Type*} [∀ level, Fintype (Vertex level)]
variable [∀ level, MeasurableSpace (Vertex level)]
variable [∀ level, MeasurableSingletonClass (Vertex level)]

theorem finiteHorizonStepPaths_isCadlag (horizon : ℝ≥0) (rates : ℕ → ℝ≥0)
    (embedding : (level : ℕ) → Vertex level → State) (level : ℕ)
    (history : Finset.Iic ⌊(horizon : ℝ) * (rates level : ℝ)⌋₊ → Vertex level) :
    IsCadlagPath (finiteHorizonStepPaths horizon rates embedding level history) := by
  let trajectory : ℕ → State := fun index =>
    embedding level (history ⟨min index ⌊(horizon : ℝ) * (rates level : ℝ)⌋₊,
      Finset.mem_Iic.mpr (min_le_right _ _)⟩)
  have boundedFloor (time : Icc (0 : ℝ) (horizon : ℝ)) :
      ⌊time.val * (rates level : ℝ)⌋₊ ≤ ⌊(horizon : ℝ) * (rates level : ℝ)⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_right time.property.2 (rates level).property)
  have pathEquality : (fun time : Icc (0 : ℝ) (horizon : ℝ) =>
      trajectory ⌊time.val * (rates level : ℝ)⌋₊) =
        finiteHorizonStepPaths horizon rates embedding level history := by
    funext time
    simp only [trajectory, finiteHorizonStepPaths, min_eq_left (boundedFloor time)]
  rw [← pathEquality]
  exact intervalFloorClockPath_isCadlag horizon (rates level) trajectory

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.realFloorClockPath_isCadlag
#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizonStepPaths_isCadlag
