import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic

/-! The usual time-change infimum, with no separation assertion. For a compact
real interval, increasing OrderIso maps are the increasing time homeomorphisms.
The construction is initially on arbitrary functions, so its restriction to
the genuine cadlag subtype does not need a different distance formula.
This file does not assert that arbitrary functions form Skorokhod D, nor that
the pseudometric is separated, complete, or Polish. -/

namespace IGS.Sec31.DiscreteMarkov

open Set
open scoped UniformConvergence NNReal
noncomputable section

variable {Time State : Type*} [LinearOrder Time]
variable [MetricSpace Time] [BoundedSpace Time]
variable [MetricSpace State] [BoundedSpace State]

local instance j1TimeChangeNonempty : Nonempty (Time ≃o Time) := ⟨OrderIso.refl Time⟩

/-- On an order-topological interval, the allowed clock changes really are
homeomorphisms for its ordinary topology. -/
def skorokhodTimeChangeHomeomorph [OrderTopology Time]
    (timeChange : Time ≃o Time) : Time ≃ₜ Time := timeChange.toHomeomorph

theorem uniformFunction_dist_eval_le (first second : Time → State) (time : Time) :
    dist (first time) (second time) ≤
      dist (UniformFun.ofFun first) (UniformFun.ofFun second) :=
  (UniformFun.dist_le (dist_nonneg : 0 ≤
    dist (UniformFun.ofFun first) (UniformFun.ofFun second))).mp le_rfl time

def skorokhodJ1Cost (first second : Time → State) (timeChange : Time ≃o Time) : ℝ :=
  max (dist (UniformFun.ofFun (fun time => timeChange time)) (UniformFun.ofFun id))
    (dist (UniformFun.ofFun first) (UniformFun.ofFun (fun time => second (timeChange time))))

theorem skorokhodJ1Cost_nonnegative (first second : Time → State)
    (timeChange : Time ≃o Time) : 0 ≤ skorokhodJ1Cost first second timeChange :=
  (dist_nonneg : 0 ≤ dist (UniformFun.ofFun (fun time => timeChange time))
    (UniformFun.ofFun id)).trans (le_max_left _ _)

theorem skorokhodJ1Cost_clock_le (first second : Time → State)
    (timeChange : Time ≃o Time) (time : Time) :
    dist (timeChange time) time ≤ skorokhodJ1Cost first second timeChange :=
  (uniformFunction_dist_eval_le (fun time => timeChange time) id time).trans (le_max_left _ _)

theorem skorokhodJ1Cost_path_le (first second : Time → State)
    (timeChange : Time ≃o Time) (time : Time) :
    dist (first time) (second (timeChange time)) ≤ skorokhodJ1Cost first second timeChange :=
  (uniformFunction_dist_eval_le first (fun time => second (timeChange time)) time).trans
    (le_max_right _ _)

theorem skorokhodJ1Cost_symm_le (first second : Time → State)
    (timeChange : Time ≃o Time) :
    skorokhodJ1Cost second first timeChange.symm ≤ skorokhodJ1Cost first second timeChange := by
  apply max_le
  · apply (UniformFun.dist_le (skorokhodJ1Cost_nonnegative first second timeChange)).mpr
    intro time
    simpa only [UniformFun.toFun_ofFun, id_eq, OrderIso.apply_symm_apply, dist_comm] using
      skorokhodJ1Cost_clock_le first second timeChange (timeChange.symm time)
  · apply (UniformFun.dist_le (skorokhodJ1Cost_nonnegative first second timeChange)).mpr
    intro time
    simpa only [UniformFun.toFun_ofFun, OrderIso.apply_symm_apply, dist_comm] using
      skorokhodJ1Cost_path_le first second timeChange (timeChange.symm time)

theorem skorokhodJ1Cost_trans_le (first second third : Time → State)
    (firstChange secondChange : Time ≃o Time) :
    skorokhodJ1Cost first third (firstChange.trans secondChange) ≤
      skorokhodJ1Cost first second firstChange + skorokhodJ1Cost second third secondChange := by
  have sumNonnegative : 0 ≤ skorokhodJ1Cost first second firstChange +
      skorokhodJ1Cost second third secondChange :=
    add_nonneg (skorokhodJ1Cost_nonnegative first second firstChange)
      (skorokhodJ1Cost_nonnegative second third secondChange)
  apply max_le
  · apply (UniformFun.dist_le sumNonnegative).mpr
    intro time
    change dist (secondChange (firstChange time)) time ≤ _
    calc
      dist (secondChange (firstChange time)) time ≤
          dist (secondChange (firstChange time)) (firstChange time) + dist (firstChange time) time :=
        dist_triangle _ _ _
      _ ≤ skorokhodJ1Cost second third secondChange + skorokhodJ1Cost first second firstChange :=
        add_le_add (skorokhodJ1Cost_clock_le second third secondChange (firstChange time))
          (skorokhodJ1Cost_clock_le first second firstChange time)
      _ = _ := add_comm _ _
  · apply (UniformFun.dist_le sumNonnegative).mpr
    intro time
    change dist (first time) (third (secondChange (firstChange time))) ≤ _
    exact (dist_triangle (first time) (second (firstChange time))
      (third (secondChange (firstChange time)))).trans
        (add_le_add (skorokhodJ1Cost_path_le first second firstChange time)
          (skorokhodJ1Cost_path_le second third secondChange (firstChange time)))

def skorokhodJ1Distance (first second : Time → State) : ℝ :=
  ⨅ timeChange : Time ≃o Time, skorokhodJ1Cost first second timeChange

theorem skorokhodJ1Cost_bddBelow (first second : Time → State) :
    BddBelow (range (skorokhodJ1Cost first second)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨timeChange, rfl⟩
  exact skorokhodJ1Cost_nonnegative first second timeChange

theorem skorokhodJ1Distance_nonnegative (first second : Time → State) :
    0 ≤ skorokhodJ1Distance first second :=
  le_ciInf fun timeChange => skorokhodJ1Cost_nonnegative first second timeChange

theorem skorokhodJ1Distance_le_cost (first second : Time → State)
    (timeChange : Time ≃o Time) :
    skorokhodJ1Distance first second ≤ skorokhodJ1Cost first second timeChange :=
  ciInf_le (skorokhodJ1Cost_bddBelow first second) timeChange

theorem skorokhodJ1Distance_le_uniform (first second : Time → State) :
    skorokhodJ1Distance first second ≤
      dist (UniformFun.ofFun first) (UniformFun.ofFun second) := by
  have identityBound := skorokhodJ1Distance_le_cost first second (OrderIso.refl Time)
  change skorokhodJ1Distance first second ≤
    max (dist (UniformFun.ofFun (id : Time → Time)) (UniformFun.ofFun id))
      (dist (UniformFun.ofFun first) (UniformFun.ofFun second)) at identityBound
  simpa only [dist_self, max_eq_right (dist_nonneg :
    0 ≤ dist (UniformFun.ofFun first) (UniformFun.ofFun second))] using identityBound

theorem skorokhodJ1Distance_self (path : Time → State) : skorokhodJ1Distance path path = 0 :=
  le_antisymm (by simpa using skorokhodJ1Distance_le_uniform path path)
    (skorokhodJ1Distance_nonnegative path path)

theorem skorokhodJ1Distance_comm (first second : Time → State) :
    skorokhodJ1Distance first second = skorokhodJ1Distance second first := by
  have reverseBound (first second : Time → State) :
      skorokhodJ1Distance first second ≤ skorokhodJ1Distance second first := by
    apply le_ciInf
    intro timeChange
    exact (skorokhodJ1Distance_le_cost first second timeChange.symm).trans
      (skorokhodJ1Cost_symm_le second first timeChange)
  exact le_antisymm (reverseBound first second) (reverseBound second first)

theorem skorokhodJ1Distance_triangle (first second third : Time → State) :
    skorokhodJ1Distance first third ≤
      skorokhodJ1Distance first second + skorokhodJ1Distance second third := by
  apply le_of_forall_pos_le_add
  intro tolerance tolerancePositive
  obtain ⟨firstChange, firstBound⟩ := exists_lt_of_ciInf_lt
    (show skorokhodJ1Distance first second <
      skorokhodJ1Distance first second + tolerance / 2 by linarith)
  obtain ⟨secondChange, secondBound⟩ := exists_lt_of_ciInf_lt
    (show skorokhodJ1Distance second third <
      skorokhodJ1Distance second third + tolerance / 2 by linarith)
  have compositionBound :=
    (skorokhodJ1Distance_le_cost first third (firstChange.trans secondChange)).trans
      (skorokhodJ1Cost_trans_le first second third firstChange secondChange)
  linarith

/-- A separate wrapper prevents the J1 topology being confused with the
uniform topology already present on UniformFun. No cadlag property is encoded
in this auxiliary full-function type. -/
structure J1Function (Time State : Type*) where
  toFun : Time → State

noncomputable instance j1FunctionPseudoMetricSpace : PseudoMetricSpace (J1Function Time State) where
  dist first second := skorokhodJ1Distance first.toFun second.toFun
  dist_self path := skorokhodJ1Distance_self path.toFun
  dist_comm first second := skorokhodJ1Distance_comm first.toFun second.toFun
  dist_triangle first second third := skorokhodJ1Distance_triangle first.toFun second.toFun third.toFun

def uniformFunctionToJ1 (path : Time →ᵤ State) : J1Function Time State := ⟨UniformFun.toFun path⟩

theorem uniformFunctionToJ1_lipschitz : LipschitzWith 1 (uniformFunctionToJ1 (Time := Time) (State := State)) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  simpa only [UniformFun.ofFun_toFun, NNReal.coe_one, one_mul] using
    skorokhodJ1Distance_le_uniform (UniformFun.toFun first) (UniformFun.toFun second)

theorem uniformFunctionToJ1_continuous : Continuous (uniformFunctionToJ1 (Time := Time) (State := State)) :=
  uniformFunctionToJ1_lipschitz.continuous

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.skorokhodJ1Distance_triangle
#print axioms IGS.Sec31.DiscreteMarkov.uniformFunctionToJ1_continuous
