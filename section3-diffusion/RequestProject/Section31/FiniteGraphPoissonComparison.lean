import RequestProject.Section31.EIGSCellStarExit

/-! A finite-graph forcing estimate using the actual expected exit time.
It controls the error of harmonic interpolation without an assumed
probabilistic representation or a strong Markov theorem. -/

namespace EIGS

open Matrix
open scoped BigOperators

noncomputable section
variable {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]

theorem poisson_le_boundary_add_exit
    (connected : graph.Connected) (domain : Finset Vertex)
    (proper : domainᶜ.Nonempty) (values : Vertex → ℝ)
    (boundaryUpper forcingUpper : ℝ)
    (boundaryBound : ∀ vertex, vertex ∉ domain → values vertex ≤ boundaryUpper)
    (forcingBound : ∀ vertex ∈ domain,
      (graph.lapMatrix ℝ *ᵥ values) vertex ≤ forcingUpper * graph.degree vertex)
    (vertex : Vertex) :
    values vertex ≤ boundaryUpper + forcingUpper * expExit graph domain vertex := by
  have exitEquation := exitSystem_expExit connected proper
  have comparison := subharmonic_nonpos (G := graph) connected proper
    (f := values - forcingUpper • expExit graph domain - fun _ => boundaryUpper)
    (fun target outside => by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [expExit_zero_of_notMem outside]
      linarith [boundaryBound target outside])
    (fun target inside => by
      have constantZero : (graph.lapMatrix ℝ *ᵥ (fun _ : Vertex => boundaryUpper)) target = 0 := by
        rw [lapMatrix_mulVec_apply]
        simp
      rw [Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [exitEquation.2 target inside, constantZero]
      linarith [forcingBound target inside])
  have bound := comparison vertex
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at bound
  linarith

theorem poisson_abs_le_exit
    (connected : graph.Connected) (domain : Finset Vertex)
    (proper : domainᶜ.Nonempty) (values : Vertex → ℝ) (forcingUpper : ℝ)
    (boundaryZero : ∀ vertex, vertex ∉ domain → values vertex = 0)
    (forcingBound : ∀ vertex ∈ domain,
      |(graph.lapMatrix ℝ *ᵥ values) vertex| ≤ forcingUpper * graph.degree vertex)
    (vertex : Vertex) :
    |values vertex| ≤ forcingUpper * expExit graph domain vertex := by
  have upper := poisson_le_boundary_add_exit graph connected domain proper values 0 forcingUpper
    (fun target outside => (boundaryZero target outside).le)
    (fun target inside => (le_abs_self _).trans (forcingBound target inside)) vertex
  have lower := poisson_le_boundary_add_exit graph connected domain proper (-values) 0 forcingUpper
    (fun target outside => by simp [boundaryZero target outside])
    (fun target inside => by
      rw [Matrix.mulVec_neg]
      exact (neg_le_abs _).trans (forcingBound target inside)) vertex
  simp only [zero_add, Pi.neg_apply] at upper lower
  exact abs_le.mpr ⟨by linarith, upper⟩

theorem harmonic_interpolation_error_le_exit
    (connected : graph.Connected) (domain : Finset Vertex)
    (proper : domainᶜ.Nonempty) (values harmonicValues : Vertex → ℝ) (forcingUpper : ℝ)
    (boundaryAgreement : ∀ vertex, vertex ∉ domain → values vertex = harmonicValues vertex)
    (harmonic : ∀ vertex ∈ domain, (graph.lapMatrix ℝ *ᵥ harmonicValues) vertex = 0)
    (forcingBound : ∀ vertex ∈ domain,
      |(graph.lapMatrix ℝ *ᵥ values) vertex| ≤ forcingUpper * graph.degree vertex)
    (vertex : Vertex) :
    |values vertex - harmonicValues vertex| ≤ forcingUpper * expExit graph domain vertex := by
  apply poisson_abs_le_exit graph connected domain proper (values - harmonicValues) forcingUpper
  · intro target outside
    simp only [Pi.sub_apply, boundaryAgreement target outside, sub_self]
  · intro target inside
    rw [Matrix.mulVec_sub]
    simpa only [Pi.sub_apply, harmonic target inside, sub_zero] using forcingBound target inside

end
end EIGS

#print axioms EIGS.poisson_le_boundary_add_exit
#print axioms EIGS.poisson_abs_le_exit
#print axioms EIGS.harmonic_interpolation_error_le_exit
