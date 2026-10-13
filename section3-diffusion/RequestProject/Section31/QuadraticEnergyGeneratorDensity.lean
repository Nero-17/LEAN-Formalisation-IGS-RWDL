import RequestProject.Section31.QuadraticEnergyGenerator

/-! Density and symmetry of the actual closed-form operator domain, derived
from the resolvent rather than supplied as domain assumptions. -/

namespace IGS.Sec31.QuadraticEnergySpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)

theorem resolventState_selfAdjoint : IsSelfAdjoint (resolventState domain form nonnegative closable) := by
  letI := closedEnergySpace_complete domain form nonnegative closable
  apply ContinuousLinearMap.isSelfAdjoint_iff'.mpr
  change ((inclusion (closedDomain domain form nonnegative) (closedForm domain form nonnegative closable)
      (closedForm_nonnegative domain form nonnegative closable)).comp
      (inclusion (closedDomain domain form nonnegative) (closedForm domain form nonnegative closable)
        (closedForm_nonnegative domain form nonnegative closable)).adjoint).adjoint = _
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] <;> rfl

theorem generatorDomain_dense (domainDense : Dense (domain : Set H)) :
    Dense (generatorDomain domain form nonnegative closable : Set H) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  rw [Submodule.topologicalClosure_eq_top_iff]
  change (resolventState domain form nonnegative closable).rangeᗮ = ⊥
  rw [ContinuousLinearMap.orthogonal_range,
    (resolventState_selfAdjoint domain form nonnegative closable).adjoint_eq]
  exact LinearMap.ker_eq_bot.mpr (resolventState_injective domain form nonnegative closable domainDense)

theorem closedGenerator_symmetric (domainDense : Dense (domain : Set H))
    (first second : generatorDomain domain form nonnegative closable) :
    inner ℝ (closedGenerator domain form nonnegative closable domainDense first) (second : H) =
      inner ℝ (first : H) (closedGenerator domain form nonnegative closable domainDense second) := by
  obtain ⟨firstForcing, rfl⟩ := (resolventRangeEquiv domain form nonnegative closable domainDense).surjective first
  obtain ⟨secondForcing, rfl⟩ := (resolventRangeEquiv domain form nonnegative closable domainDense).surjective second
  have firstIdentity := closedGenerator_variational domain form nonnegative closable domainDense firstForcing
    (resolventLift domain form nonnegative closable secondForcing)
  have secondIdentity := closedGenerator_variational domain form nonnegative closable domainDense secondForcing
    (resolventLift domain form nonnegative closable firstForcing)
  change inner ℝ _ (resolventState domain form nonnegative closable secondForcing) = _ at firstIdentity
  change inner ℝ _ (resolventState domain form nonnegative closable firstForcing) = _ at secondIdentity
  change inner ℝ _ (resolventState domain form nonnegative closable secondForcing) =
    inner ℝ (resolventState domain form nonnegative closable firstForcing) _
  rw [firstIdentity, real_inner_comm
    (closedGenerator domain form nonnegative closable domainDense
      (resolventRangeEquiv domain form nonnegative closable domainDense secondForcing))
    (resolventState domain form nonnegative closable firstForcing), secondIdentity]
  exact QuadraticMap.associated_isSymm ℝ (closedForm domain form nonnegative closable) _ _

/-- The adjoint variational relation has exactly the constructed operator
graph. This states self-adjointness without postulating an unbounded-operator
or semigroup package. -/
theorem closedGenerator_adjoint_characterization (domainDense : Dense (domain : Set H))
    (state forcing : H) :
    (∀ values : generatorDomain domain form nonnegative closable,
      inner ℝ forcing (values : H) =
        inner ℝ state (closedGenerator domain form nonnegative closable domainDense values)) ↔
      ∃ values : generatorDomain domain form nonnegative closable,
        (values : H) = state ∧ closedGenerator domain form nonnegative closable domainDense values = forcing := by
  constructor
  · intro adjointRelation
    obtain ⟨solution, solutionIdentity⟩ :=
      closedGenerator_resolvent_surjective domain form nonnegative closable domainDense (state + forcing)
    dsimp only at solutionIdentity
    have errorOrthogonal : ∀ values : generatorDomain domain form nonnegative closable,
        inner ℝ (state - (solution : H))
          ((values : H) + closedGenerator domain form nonnegative closable domainDense values) = 0 := by
      intro values
      have relation := adjointRelation values
      have symmetry := closedGenerator_symmetric domain form nonnegative closable domainDense solution values
      have identity := congrArg (fun point : H => inner ℝ point (values : H)) solutionIdentity
      simp only [inner_add_left] at identity
      rw [inner_add_right, inner_sub_left, inner_sub_left]
      linarith
    obtain ⟨test, testIdentity⟩ :=
      closedGenerator_resolvent_surjective domain form nonnegative closable domainDense (state - (solution : H))
    dsimp only at testIdentity
    have errorZero := errorOrthogonal test
    rw [testIdentity] at errorZero
    have solutionState : (solution : H) = state :=
      (sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)).mp errorZero)).symm
    refine ⟨solution, solutionState, ?_⟩
    rw [solutionState] at solutionIdentity
    exact add_left_cancel solutionIdentity
  · rintro ⟨values, rfl, rfl⟩ test
    exact closedGenerator_symmetric domain form nonnegative closable domainDense values test

theorem closedGenerator_graph_isClosed (domainDense : Dense (domain : Set H)) :
    IsClosed {pair : H × H | ∃ values : generatorDomain domain form nonnegative closable,
      (values : H) = pair.1 ∧ closedGenerator domain form nonnegative closable domainDense values = pair.2} := by
  have graphEquality :
      {pair : H × H | ∃ values : generatorDomain domain form nonnegative closable,
        (values : H) = pair.1 ∧ closedGenerator domain form nonnegative closable domainDense values = pair.2} =
      {pair : H × H | ∀ values : generatorDomain domain form nonnegative closable,
        inner ℝ pair.2 (values : H) =
          inner ℝ pair.1 (closedGenerator domain form nonnegative closable domainDense values)} := by
    ext pair
    exact (closedGenerator_adjoint_characterization domain form nonnegative closable domainDense pair.1 pair.2).symm
  rw [graphEquality]
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro values
  exact isClosed_eq (continuous_snd.inner continuous_const) (continuous_fst.inner continuous_const)

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.resolventState_selfAdjoint
#print axioms IGS.Sec31.QuadraticEnergySpace.generatorDomain_dense
#print axioms IGS.Sec31.QuadraticEnergySpace.closedGenerator_symmetric
#print axioms IGS.Sec31.QuadraticEnergySpace.closedGenerator_adjoint_characterization
#print axioms IGS.Sec31.QuadraticEnergySpace.closedGenerator_graph_isClosed
