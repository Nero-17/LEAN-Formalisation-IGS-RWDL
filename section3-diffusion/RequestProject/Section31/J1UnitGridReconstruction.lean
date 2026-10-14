import RequestProject.Section31.J1UnitTimeInstances
import RequestProject.Section31.FiniteFloorPathCadlag
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-! Measurable fixed-grid reconstructions into the genuine cadlag J1
carrier. The carrier uses the already proved separation of the repository's
real-infimum J1 pseudometric. No completeness or Polish assertion is made. -/

namespace IGS.Sec31.DiscreteMarkov
open Set MeasureTheory
open scoped NNReal UniformConvergence
noncomputable section

abbrev UnitCadlagJ1Path (State : Type*) [MetricSpace State] := CadlagJ1Path UnitJ1Time State

noncomputable instance unitCadlagJ1MetricSpace {State : Type*} [MetricSpace State] [BoundedSpace State] :
    MetricSpace (UnitCadlagJ1Path State) := cadlagIntervalJ1MetricSpace (State := State) 1

instance unitCadlagJ1MeasurableSpace {State : Type*} [MetricSpace State] [BoundedSpace State] :
    MeasurableSpace (UnitCadlagJ1Path State) := borel _

instance unitCadlagJ1BorelSpace {State : Type*} [MetricSpace State] [BoundedSpace State] :
    BorelSpace (UnitCadlagJ1Path State) := ⟨rfl⟩

theorem unitGridFloor_le (grid : ℕ) (time : UnitJ1Time) :
    ⌊(grid + 1 : ℝ) * time.val⌋₊ ≤ grid + 1 := by
  have bound := Nat.floor_mono
    (mul_le_mul_of_nonneg_left time.property.2 (by positivity : 0 ≤ (grid + 1 : ℝ)))
  have top : ⌊(grid + 1 : ℝ)⌋₊ = grid + 1 := by
    rw [show (grid + 1 : ℝ) = ((grid + 1 : ℕ) : ℝ) by simp, Nat.floor_natCast]
  simpa only [mul_one, top] using bound

def unitGridIndex (grid : ℕ) (time : UnitJ1Time) : Fin (grid + 2) :=
  ⟨⌊(grid + 1 : ℝ) * time.val⌋₊, Nat.lt_succ_of_le (unitGridFloor_le grid time)⟩

def unitGridJ1Reconstruction {State : Type*} [MetricSpace State]
    (grid : ℕ) (values : Fin (grid + 2) → State) : UnitCadlagJ1Path State := by
  refine ⟨⟨fun time => values (unitGridIndex grid time)⟩, ?_⟩
  let trajectory : ℕ → State := fun index => values ⟨min index (grid + 1), by omega⟩
  have regular := intervalFloorClockPath_isCadlag (1 : ℝ≥0) (grid + 1 : ℝ≥0) trajectory
  change IsCadlagPath
    (fun time : UnitJ1Time => trajectory ⌊time.val * ((grid + 1 : ℝ≥0) : ℝ)⌋₊) at regular
  have equality :
      (fun time : UnitJ1Time => trajectory ⌊time.val * ((grid + 1 : ℝ≥0) : ℝ)⌋₊) =
      (fun time : UnitJ1Time => values (unitGridIndex grid time)) := by
    funext time
    apply congrArg values
    apply Fin.ext
    simp only [trajectory, unitGridIndex, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    rw [mul_comm]
    exact min_eq_left (unitGridFloor_le grid time)
  rw [equality] at regular
  exact regular

theorem unitGridJ1Reconstruction_lipschitz
    {State : Type*} [MetricSpace State] [BoundedSpace State] (grid : ℕ) :
    LipschitzWith 1 (unitGridJ1Reconstruction (State := State) grid) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  change skorokhodJ1Distance (fun time => first (unitGridIndex grid time))
    (fun time => second (unitGridIndex grid time)) ≤ (1 : ℝ≥0) * dist first second
  simp only [NNReal.coe_one, one_mul]
  apply (skorokhodJ1Distance_le_uniform _ _).trans
  apply (UniformFun.dist_le dist_nonneg).mpr
  intro time
  exact dist_le_pi_dist first second (unitGridIndex grid time)

theorem unitGridJ1Reconstruction_measurable
    {State : Type*} [MetricSpace State] [BoundedSpace State]
    [MeasurableSpace State] [BorelSpace State] [SecondCountableTopology State] (grid : ℕ) :
    Measurable (unitGridJ1Reconstruction (State := State) grid) :=
  (unitGridJ1Reconstruction_lipschitz grid).continuous.measurable

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.unitCadlagJ1MetricSpace
#print axioms IGS.Sec31.DiscreteMarkov.unitGridJ1Reconstruction
#print axioms IGS.Sec31.DiscreteMarkov.unitGridJ1Reconstruction_lipschitz
#print axioms IGS.Sec31.DiscreteMarkov.unitGridJ1Reconstruction_measurable
