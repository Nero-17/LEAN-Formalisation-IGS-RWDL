import RequestProject.Section31.QuadraticEnergyResolvent

/-! The operator associated with the constructed closed form. Its domain is
the range of the actual unit resolvent; forcing uniqueness follows from density
of the original form domain. This does not assert a semigroup construction. -/

namespace IGS.Sec31.QuadraticEnergySpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)

theorem resolventState_injective (domainDense : Dense (domain : Set H)) :
    Function.Injective (resolventState domain form nonnegative closable) := by
  intro first second equality
  have stateZero : resolventState domain form nonnegative closable (first - second) = 0 := by
    rw [map_sub, equality, sub_self]
  have liftZero : resolventLift domain form nonnegative closable (first - second) = 0 := by
    apply (equivDomain (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable)
      (closedForm_nonnegative domain form nonnegative closable)).injective
    apply Subtype.ext
    exact stateZero
  have orthogonal : ∀ test ∈ (domain : Set H), inner ℝ (first - second) test = 0 := by
    intro test membership
    have identity := resolvent_variational domain form nonnegative closable (first - second)
      ⟨⟨test, original_mem_closedDomain domain form nonnegative ⟨test, membership⟩⟩⟩
    rw [liftZero] at identity
    change (closedForm domain form nonnegative closable).associated 0
      ⟨test, original_mem_closedDomain domain form nonnegative ⟨test, membership⟩⟩ +
        inner ℝ 0 test = inner ℝ (first - second) test at identity
    simpa only [map_zero, LinearMap.zero_apply, inner_zero_left, zero_add] using identity.symm
  have selfZero : inner ℝ (first - second) (first - second) = 0 := domainDense.induction
    (P := fun test : H => inner ℝ (first - second) test = 0) orthogonal
    (isClosed_eq (continuous_const.inner continuous_id) continuous_const) (first - second)
  exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)).mp selfZero)

noncomputable def generatorDomain : Submodule ℝ H :=
  (resolventState domain form nonnegative closable).range

noncomputable def resolventRangeEquiv (domainDense : Dense (domain : Set H)) :
    H ≃ₗ[ℝ] generatorDomain domain form nonnegative closable :=
  LinearEquiv.ofInjective (resolventState domain form nonnegative closable).toLinearMap
    (resolventState_injective domain form nonnegative closable domainDense)

noncomputable def closedGenerator (domainDense : Dense (domain : Set H)) :
    generatorDomain domain form nonnegative closable →ₗ[ℝ] H :=
  (resolventRangeEquiv domain form nonnegative closable domainDense).symm.toLinearMap -
    (generatorDomain domain form nonnegative closable).subtype

theorem closedGenerator_resolvent (domainDense : Dense (domain : Set H)) (forcing : H) :
    closedGenerator domain form nonnegative closable domainDense
        (resolventRangeEquiv domain form nonnegative closable domainDense forcing) =
      forcing - resolventState domain form nonnegative closable forcing := by
  change (resolventRangeEquiv domain form nonnegative closable domainDense).symm
      ((resolventRangeEquiv domain form nonnegative closable domainDense) forcing) - _ = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem closedGenerator_variational (domainDense : Dense (domain : Set H)) (forcing : H)
    (test : QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable) (closedForm_nonnegative domain form nonnegative closable)) :
    inner ℝ (closedGenerator domain form nonnegative closable domainDense
      (resolventRangeEquiv domain form nonnegative closable domainDense forcing)) (test.value : H) =
      (closedForm domain form nonnegative closable).associated
        (resolventLift domain form nonnegative closable forcing).value test.value := by
  rw [closedGenerator_resolvent, inner_sub_left]
  have identity := resolvent_variational domain form nonnegative closable forcing test
  change _ + inner ℝ (resolventState domain form nonnegative closable forcing) (test.value : H) = _ at identity
  linarith

theorem closedGenerator_nonnegative (domainDense : Dense (domain : Set H))
    (values : generatorDomain domain form nonnegative closable) :
    0 ≤ inner ℝ (closedGenerator domain form nonnegative closable domainDense values) (values : H) := by
  obtain ⟨forcing, rfl⟩ := (resolventRangeEquiv domain form nonnegative closable domainDense).surjective values
  have identity := closedGenerator_variational domain form nonnegative closable domainDense forcing
    (resolventLift domain form nonnegative closable forcing)
  rw [QuadraticMap.associated_eq_self_apply] at identity
  change inner ℝ _ (resolventState domain form nonnegative closable forcing) = _ at identity
  change 0 ≤ inner ℝ _ (resolventState domain form nonnegative closable forcing)
  rw [identity]
  exact closedForm_nonnegative domain form nonnegative closable _

theorem closedGenerator_resolvent_surjective (domainDense : Dense (domain : Set H)) :
    Function.Surjective (fun values : generatorDomain domain form nonnegative closable =>
      (values : H) + closedGenerator domain form nonnegative closable domainDense values) := by
  intro forcing
  refine ⟨resolventRangeEquiv domain form nonnegative closable domainDense forcing, ?_⟩
  dsimp only
  rw [closedGenerator_resolvent]
  change resolventState domain form nonnegative closable forcing +
    (forcing - resolventState domain form nonnegative closable forcing) = forcing
  abel

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.resolventState_injective
#print axioms IGS.Sec31.QuadraticEnergySpace.closedGenerator_resolvent
#print axioms IGS.Sec31.QuadraticEnergySpace.closedGenerator_variational
#print axioms IGS.Sec31.QuadraticEnergySpace.closedGenerator_nonnegative
#print axioms IGS.Sec31.QuadraticEnergySpace.closedGenerator_resolvent_surjective
