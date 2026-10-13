import RequestProject.Section31.QuadraticEnergyCompletion
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The unit resolvent of the constructed closed form, obtained from its
energy-plus-L2 Hilbert space. Its variational identity and uniqueness are
proved directly, without a generator or semigroup existence premise. -/

namespace IGS.Sec31.QuadraticEnergySpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)

noncomputable def resolventLift : H →L[ℝ]
    QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable) (closedForm_nonnegative domain form nonnegative closable) := by
  letI := closedEnergySpace_complete domain form nonnegative closable
  exact (inclusion (closedDomain domain form nonnegative)
    (closedForm domain form nonnegative closable) (closedForm_nonnegative domain form nonnegative closable)).adjoint

noncomputable def resolventState : H →L[ℝ] H :=
  (inclusion (closedDomain domain form nonnegative) (closedForm domain form nonnegative closable)
    (closedForm_nonnegative domain form nonnegative closable)).comp (resolventLift domain form nonnegative closable)

theorem resolvent_variational (forcing : H)
    (test : QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable) (closedForm_nonnegative domain form nonnegative closable)) :
    (closedForm domain form nonnegative closable).associated
        (resolventLift domain form nonnegative closable forcing).value test.value +
      inner ℝ ((resolventLift domain form nonnegative closable forcing).value : H) (test.value : H) =
        inner ℝ forcing (test.value : H) := by
  letI := closedEnergySpace_complete domain form nonnegative closable
  exact (inclusion (closedDomain domain form nonnegative)
    (closedForm domain form nonnegative closable) (closedForm_nonnegative domain form nonnegative closable)).adjoint_inner_left
      test forcing

theorem resolvent_energy_identity (forcing : H) :
    closedForm domain form nonnegative closable (resolventLift domain form nonnegative closable forcing).value +
      ‖resolventState domain form nonnegative closable forcing‖ ^ 2 =
        inner ℝ forcing (resolventState domain form nonnegative closable forcing) := by
  have identity := resolvent_variational domain form nonnegative closable forcing
    (resolventLift domain form nonnegative closable forcing)
  simpa only [QuadraticMap.associated_eq_self_apply, real_inner_self_eq_norm_sq] using identity

theorem resolvent_state_norm_le (forcing : H) :
    ‖resolventState domain form nonnegative closable forcing‖ ≤ ‖forcing‖ := by
  have identity := resolvent_energy_identity domain form nonnegative closable forcing
  have nonnegativeEnergy := closedForm_nonnegative domain form nonnegative closable
    (resolventLift domain form nonnegative closable forcing).value
  have innerBound := real_inner_le_norm forcing (resolventState domain form nonnegative closable forcing)
  nlinarith [norm_nonneg forcing, norm_nonneg (resolventState domain form nonnegative closable forcing)]

theorem resolvent_unique (forcing : H)
    (candidate : QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable) (closedForm_nonnegative domain form nonnegative closable))
    (variational : ∀ test : QuadraticEnergySpace (closedDomain domain form nonnegative)
        (closedForm domain form nonnegative closable) (closedForm_nonnegative domain form nonnegative closable),
      (closedForm domain form nonnegative closable).associated candidate.value test.value +
        inner ℝ (candidate.value : H) (test.value : H) = inner ℝ forcing (test.value : H)) :
    candidate = resolventLift domain form nonnegative closable forcing := by
  apply ext_inner_right ℝ
  intro test
  exact (variational test).trans (resolvent_variational domain form nonnegative closable forcing test).symm

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.resolvent_variational
#print axioms IGS.Sec31.QuadraticEnergySpace.resolvent_energy_identity
#print axioms IGS.Sec31.QuadraticEnergySpace.resolvent_state_norm_le
#print axioms IGS.Sec31.QuadraticEnergySpace.resolvent_unique
