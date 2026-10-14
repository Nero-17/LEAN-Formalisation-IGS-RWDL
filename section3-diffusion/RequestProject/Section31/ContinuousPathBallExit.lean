import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Monotone
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.ENNReal.Real

/-! Genuine continuous-path exit from an open metric ball. The first hit of
the closed complement is defined by its infimum, with infinity for no hit.
Closedness makes a finite infimum an attained exit time. Candidate source. -/

namespace IGS.Sec31
open Set Metric MeasureTheory
open scoped NNReal ENNReal Classical
noncomputable section

variable {Space : Type*} [MetricSpace Space]

def continuousPathBallExit (path : C(ℝ≥0, Space)) (center : Space) (radius : ℝ) : ℝ≥0∞ :=
  if reached : ({time : ℝ≥0 | radius ≤ dist (path time) center}).Nonempty then
    (sInf {time : ℝ≥0 | radius ≤ dist (path time) center} : ℝ≥0)
  else ⊤

theorem continuousPathBallExit_le_of_reached (path : C(ℝ≥0, Space))
    (center : Space) (radius : ℝ) (time : ℝ≥0)
    (reached : radius ≤ dist (path time) center) :
    continuousPathBallExit path center radius ≤ (time : ℝ≥0∞) := by
  rw [continuousPathBallExit, dif_pos ⟨time, reached⟩]
  exact ENNReal.coe_le_coe.mpr (csInf_le (OrderBot.bddBelow _) reached)

theorem time_lt_continuousPathBallExit_iff (path : C(ℝ≥0, Space))
    (center : Space) (radius : ℝ) (time : ℝ≥0) :
    (time : ℝ≥0∞) < continuousPathBallExit path center radius ↔
      ∀ observed : ℝ≥0, observed ≤ time → dist (path observed) center < radius := by
  constructor
  · intro survives observed observedBefore
    by_contra outside
    have exited := continuousPathBallExit_le_of_reached path center radius observed
      (le_of_not_gt outside)
    exact (not_lt_of_ge (exited.trans (ENNReal.coe_le_coe.mpr observedBefore))) survives
  · intro stays
    by_cases reached : ({observed : ℝ≥0 | radius ≤ dist (path observed) center}).Nonempty
    · have exitSetClosed : IsClosed {observed : ℝ≥0 | radius ≤ dist (path observed) center} :=
        isClosed_le continuous_const (path.continuous.dist continuous_const)
      have exitAttained := exitSetClosed.csInf_mem reached (OrderBot.bddBelow _)
      have timeBefore : time < sInf {observed : ℝ≥0 | radius ≤ dist (path observed) center} := by
        by_contra notBefore
        exact (not_lt_of_ge exitAttained) (stays _ (le_of_not_gt notBefore))
      rw [continuousPathBallExit, dif_pos reached]
      exact ENNReal.coe_lt_coe.mpr timeBefore
    · rw [continuousPathBallExit, dif_neg reached]
      exact ENNReal.coe_lt_top

def continuousPathPrefixMaxDistance (path : C(ℝ≥0, Space)) (center : Space)
    (time : ℝ≥0) : ℝ :=
  sSup ((fun observed : ℝ≥0 => dist (path observed) center) '' Icc 0 time)

theorem continuousPathPrefixMaxDistance_lt_iff (path : C(ℝ≥0, Space))
    (center : Space) (radius : ℝ) (time : ℝ≥0) :
    continuousPathPrefixMaxDistance path center time < radius ↔
      ∀ observed : ℝ≥0, observed ≤ time → dist (path observed) center < radius := by
  rw [continuousPathPrefixMaxDistance]
  have intervalNonempty : (Icc (0 : ℝ≥0) time).Nonempty := ⟨0, le_rfl, zero_le _⟩
  simpa only [mem_Icc, zero_le, true_and] using
    isCompact_Icc.sSup_lt_iff_of_continuous intervalNonempty
      (path.continuous.dist continuous_const).continuousOn radius

theorem time_lt_continuousPathBallExit_iff_prefixMaxDistance (path : C(ℝ≥0, Space))
    (center : Space) (radius : ℝ) (time : ℝ≥0) :
    (time : ℝ≥0∞) < continuousPathBallExit path center radius ↔
      continuousPathPrefixMaxDistance path center time < radius := by
  rw [time_lt_continuousPathBallExit_iff, continuousPathPrefixMaxDistance_lt_iff]

theorem continuousPathBallExit_survival_isOpen (center : Space) (radius : ℝ)
    (time : ℝ≥0) :
    IsOpen {path : C(ℝ≥0, Space) | (time : ℝ≥0∞) < continuousPathBallExit path center radius} := by
  have mapsOpen := ContinuousMap.isOpen_setOf_mapsTo
    (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) time)) (isOpen_ball (x := center) (ε := radius))
  convert mapsOpen using 1
  ext path
  simp only [mem_setOf_eq, time_lt_continuousPathBallExit_iff, MapsTo, mem_Icc,
    zero_le, true_and, mem_ball]

theorem continuousPathBallExit_measurable [MeasurableSpace C(ℝ≥0, Space)]
    [BorelSpace C(ℝ≥0, Space)] (center : Space) (radius : ℝ) :
    Measurable (fun path : C(ℝ≥0, Space) => continuousPathBallExit path center radius) := by
  apply measurable_of_Ioi
  intro threshold
  by_cases infinite : threshold = ⊤
  · simp only [infinite, Ioi_top, preimage_empty, MeasurableSet.empty]
  · lift threshold to ℝ≥0 using infinite
    exact (continuousPathBallExit_survival_isOpen center radius threshold).measurableSet

end
end IGS.Sec31

#print axioms IGS.Sec31.time_lt_continuousPathBallExit_iff
#print axioms IGS.Sec31.time_lt_continuousPathBallExit_iff_prefixMaxDistance
#print axioms IGS.Sec31.continuousPathBallExit_survival_isOpen
#print axioms IGS.Sec31.continuousPathBallExit_measurable
