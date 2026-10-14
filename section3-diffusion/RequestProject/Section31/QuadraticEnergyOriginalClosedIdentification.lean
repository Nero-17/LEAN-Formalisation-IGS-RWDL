import RequestProject.Section31.QuadraticEnergyCompletion
import Mathlib.Topology.MetricSpace.Isometry

/-! If the original energy-plus-ambient space is already complete, its
constructed closed domain is exactly its original domain. This identifies
the existing closure without introducing another closed form or semigroup.
Candidate source: compilation is not claimed. -/

namespace IGS.Sec31.QuadraticEnergySpace
open Set UniformSpace
noncomputable section
variable {Hilbert : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert] [CompleteSpace Hilbert]

theorem closedDomain_eq_original_of_complete
    (domain : Submodule ℝ Hilbert) (form : QuadraticForm ℝ domain) (nonnegative : ∀ values, 0 ≤ form values)
    [CompleteSpace (QuadraticEnergySpace domain form nonnegative)] :
    closedDomain domain form nonnegative = domain := by
  let embedding := fun values : QuadraticEnergySpace domain form nonnegative =>
    (values : Completion (QuadraticEnergySpace domain form nonnegative))
  have embeddingClosed : IsClosed (Set.range embedding) :=
    (Completion.coe_isometry.isClosedEmbedding).isClosed_range
  have embeddingDense : DenseRange embedding := Completion.denseRange_coe
  have embeddingSurjective : Function.Surjective embedding := by
    intro point
    have rangeIsAll : Set.range embedding = Set.univ := by
      rw [← embeddingClosed.closure_eq]
      exact embeddingDense.closure_eq
    change point ∈ Set.range embedding
    rw [rangeIsAll]
    exact Set.mem_univ point
  apply Submodule.ext
  intro point
  constructor
  · rintro ⟨completed, rfl⟩
    obtain ⟨original, equality⟩ := embeddingSurjective completed
    rw [← equality, completionMap_coe]
    exact original.value.property
  · intro membership
    exact original_mem_closedDomain domain form nonnegative ⟨point, membership⟩

end
end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.closedDomain_eq_original_of_complete
