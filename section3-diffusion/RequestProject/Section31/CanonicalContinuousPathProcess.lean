import RequestProject.Section31.ContinuousTimePathBorel
import Mathlib.Probability.Process.Stopping

/-! The canonical process on the compact-open Borel continuous path space
has continuous trajectories, is strongly adapted to its natural filtration,
and is progressively measurable. Its stopped value is measurable with respect
to the stopping-time sigma algebra. These are prerequisites for subsequent
Markov and strong Markov proofs, which are not asserted here.

For an infinite stopping time, `stoppedValue` has mathlib's `WithTop.untopA`
convention. Statements about the process at a stopping time must therefore
be restricted to finite stopping times, or to their finite-value event. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 3000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

local instance canonicalContinuousProcessMeasurableSpace : MeasurableSpace C(ℝ≥0, State) := borel _
local instance canonicalContinuousProcessBorelSpace : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

def canonicalContinuousPathProcess (time : ℝ≥0) (path : C(ℝ≥0, State)) : State := path time

theorem canonicalContinuousPathProcess_stronglyMeasurable (time : ℝ≥0) :
    StronglyMeasurable (canonicalContinuousPathProcess (State := State) time) :=
  (continuous_eval_const time).stronglyMeasurable

def canonicalContinuousPathFiltration : Filtration ℝ≥0 (borel C(ℝ≥0, State)) :=
  Filtration.natural canonicalContinuousPathProcess canonicalContinuousPathProcess_stronglyMeasurable

theorem canonicalContinuousPathProcess_stronglyAdapted :
    StronglyAdapted (canonicalContinuousPathFiltration (State := State)) canonicalContinuousPathProcess :=
  Filtration.stronglyAdapted_natural canonicalContinuousPathProcess_stronglyMeasurable

theorem canonicalContinuousPathProcess_continuous (path : C(ℝ≥0, State)) :
    Continuous (fun time => canonicalContinuousPathProcess time path) :=
  path.continuous

theorem canonicalContinuousPathProcess_progMeasurable :
    ProgMeasurable (canonicalContinuousPathFiltration (State := State)) canonicalContinuousPathProcess :=
  canonicalContinuousPathProcess_stronglyAdapted.progMeasurable_of_continuous
    canonicalContinuousPathProcess_continuous

theorem canonicalContinuousPathProcess_stoppedValue_measurable
    (stoppingTime : C(ℝ≥0, State) → WithTop ℝ≥0)
    (stopping : IsStoppingTime canonicalContinuousPathFiltration stoppingTime) :
    Measurable[stopping.measurableSpace]
      (stoppedValue canonicalContinuousPathProcess stoppingTime) :=
  measurable_stoppedValue canonicalContinuousPathProcess_progMeasurable stopping

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.canonicalContinuousPathProcess_stronglyMeasurable
#print axioms IGS.Sec31.DiscreteMarkov.canonicalContinuousPathProcess_stronglyAdapted
#print axioms IGS.Sec31.DiscreteMarkov.canonicalContinuousPathProcess_progMeasurable
#print axioms IGS.Sec31.DiscreteMarkov.canonicalContinuousPathProcess_stoppedValue_measurable

