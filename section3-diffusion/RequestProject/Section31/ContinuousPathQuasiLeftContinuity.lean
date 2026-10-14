import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.WithTop
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.MeasureTheory.Measure.Restrict

/-! Continuous paths converge along all increasing finite-limit time sequences.
This supplies the path-regularity part of a Hunt construction. It does not
assert a Markov property, a completed filtration, or a full Hunt bundle. -/

namespace IGS.Sec31.DiscreteMarkov

open Filter MeasureTheory Topology
open scoped NNReal
noncomputable section

variable {State : Type*} [TopologicalSpace State]

theorem continuousPath_tendsto_at_finite_extended_time
    (path : C(ℝ≥0, State)) (times : ℕ → WithTop ℝ≥0)
    (time : WithTop ℝ≥0) (finite : time ≠ ⊤)
    (convergence : Tendsto times atTop (𝓝 time)) :
    Tendsto (fun index => path (times index).untopA) atTop (𝓝 (path time.untopA)) :=
  path.continuous.continuousAt.tendsto.comp
    ((WithTop.tendsto_untopA finite).comp convergence)

/-- No stopping-time assumption is needed: this holds for every continuous
path and every increasing sequence whose supremum is finite. -/
theorem continuousPath_quasiLeftContinuous_at_finite_supremum
    (path : C(ℝ≥0, State)) (times : ℕ → WithTop ℝ≥0)
    (increasing : Monotone times) (finite : (⨆ index, times index) ≠ ⊤) :
    Tendsto (fun index => path (times index).untopA) atTop
      (𝓝 (path (⨆ index, times index).untopA)) :=
  continuousPath_tendsto_at_finite_extended_time path times _ finite
    (tendsto_atTop_iSup increasing)

/-- The same regularity holds under any law on the actual continuous-path
carrier, on the finite-time event, without exceptional paths to construct. -/
theorem continuousPath_law_quasiLeftContinuous
    [MeasurableSpace C(ℝ≥0, State)] (law : Measure C(ℝ≥0, State))
    (times : ℕ → C(ℝ≥0, State) → WithTop ℝ≥0)
    (increasing : ∀ path, Monotone (fun index => times index path)) :
    ∀ᵐ path ∂law, (⨆ index, times index path) ≠ ⊤ →
      Tendsto (fun index => path (times index path).untopA) atTop
        (𝓝 (path (⨆ index, times index path).untopA)) := by
  exact Filter.Eventually.of_forall fun path finite =>
    continuousPath_quasiLeftContinuous_at_finite_supremum path
      (fun index => times index path) (increasing path) finite

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_tendsto_at_finite_extended_time
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_quasiLeftContinuous_at_finite_supremum
#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_law_quasiLeftContinuous
