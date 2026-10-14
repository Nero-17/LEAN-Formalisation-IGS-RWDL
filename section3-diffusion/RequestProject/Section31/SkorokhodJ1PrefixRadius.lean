import RequestProject.Section31.CadlagJ1CarrierInstances

/-! Distance to a constant path is the full-horizon maximal displacement
even for the genuine time-change J1 pseudometric. Thus this particular
functional is continuous. No lower semicontinuity of cadlag exit times
is asserted. -/

namespace IGS.Sec31.DiscreteMarkov
open scoped UniformConvergence
noncomputable section
variable {Time State : Type*} [LinearOrder Time]
variable [MetricSpace Time] [BoundedSpace Time]
variable [MetricSpace State] [BoundedSpace State]

theorem skorokhodJ1Distance_constant (path : Time → State) (center : State) :
    skorokhodJ1Distance path (fun _ => center) =
      dist (UniformFun.ofFun path) (UniformFun.ofFun (fun _ : Time => center)) := by
  apply le_antisymm (skorokhodJ1Distance_le_uniform path (fun _ => center))
  letI : Nonempty (Time ≃o Time) := ⟨OrderIso.refl Time⟩
  apply le_ciInf
  intro timeChange
  exact le_max_right _ _

def cadlagJ1ConstantPath (center : State) : CadlagJ1Path Time State :=
  ⟨⟨fun _ => center⟩, Continuous.isCadlagPath continuous_const⟩

def cadlagJ1PrefixRadius (center : State) (path : CadlagJ1Path Time State) : ℝ :=
  dist path (cadlagJ1ConstantPath center)

theorem cadlagJ1PrefixRadius_eq_uniform (center : State) (path : CadlagJ1Path Time State) :
    cadlagJ1PrefixRadius center path =
      dist (UniformFun.ofFun path.val.toFun) (UniformFun.ofFun (fun _ : Time => center)) :=
  skorokhodJ1Distance_constant path.val.toFun center

theorem cadlagJ1PrefixRadius_continuous (center : State) :
    Continuous (cadlagJ1PrefixRadius (Time := Time) center) :=
  continuous_id.dist continuous_const

theorem cadlagJ1PrefixRadius_eval_le (center : State) (path : CadlagJ1Path Time State)
    (time : Time) : dist (path.val.toFun time) center ≤ cadlagJ1PrefixRadius center path := by
  rw [cadlagJ1PrefixRadius_eq_uniform]
  exact uniformFunction_dist_eval_le path.val.toFun (fun _ : Time => center) time

theorem cadlagJ1PrefixRadius_open (center : State) (radius : ℝ) :
    IsOpen {path : CadlagJ1Path Time State | cadlagJ1PrefixRadius center path < radius} :=
  isOpen_lt (cadlagJ1PrefixRadius_continuous center) continuous_const

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.skorokhodJ1Distance_constant
#print axioms IGS.Sec31.DiscreteMarkov.cadlagJ1PrefixRadius_continuous
#print axioms IGS.Sec31.DiscreteMarkov.cadlagJ1PrefixRadius_open
